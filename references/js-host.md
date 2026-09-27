# A JavaScript host for a proved Bend core

Read this only when a JavaScript program is the caller. A core with no host
needs none of it: the laws, the proofs, the falsifier and the mutants are the
whole method, and `references/workflow.md` is that.

Two tools exist only for this file, and both are in the same shape as the
method's own: a checked-in README is their spec.

- **bend-emit** ([github nohzafk/bend-emit](https://github.com/nohzafk/bend-emit))
  builds the typed ES module the host imports from a core. It refuses a Bend
  type it cannot encode, and it still skips a def with a template parameter
  (`~f`), because the bundler does not export one: such a def stays in the
  module but is undeclared in the `.d.ts`, so give the host a closed wrapper.
- **bend-schema** ([github nohzafk/bend-schema](https://github.com/nohzafk/bend-schema))
  is the schema boundary, with the codec and the schemas written in Bend. A
  graduated-pricing shape and a permissions shape are the two it was built
  for; a host's own shape usually needs a combinator added there, with a law
  pinning it.

## Is this function a candidate?

Port it if it is **small, pure, decides something, and is costly when wrong**,
and its inputs and outputs are integers and declared data, not text. If it does
IO, parses strings or needs an npm package, split it first: the host does that
part and hands the core plain data.

Port one function at a time. The rest of the app barely changes, which is what
makes this cheap to adopt.

## The project layout

A core is three files and a few beside them:

```
core.bend        the defs, no imports but Base
LAWS.bend        law <name>: followed by the claim
PROOF.bend       the tools section, then one section per law
check_mutants.ts the mutant table, importing bend-falsify
test.sh          the gate, in the order below
```

With a host, add `bridge.ts`, `package.json`, `tsconfig.json` and a
`.gitignore` with `dist/`. Create all of it by hand; there is no generator, and
a scaffold you type is a scaffold you understand.

`test.sh` is the gate, and its order is the order to keep:

1. `bend PROOF.bend` through the 5 s wrapper — proves every law, and refuses
   any line about relying on unsafe or foreign code.
2. The falsifier on the spec.
3. The mutant table.
4. `bunx bend-emit core.bend dist`, then diff what it built.
5. The host's tests, against the bridge.
6. `bunx tsc -p .`.

## Calling the core from a JavaScript host

A pure core can be called as a library, with no effects at all. That is usually
the better shape when only the proofs are wanted.

### Bend alone does not build a library

- **`bend x.bend -o x.js` builds a program, not a library**: it ends by running
  `main` and exports nothing. A plain Bun or Node `import "./x.bend"` reads the
  file as text.
- **The page bundler compiles an imported `.bend` into a module**, but its entry
  is bend's own loader output (`export default { name: fn, ... }`), and an HTML
  entry keeps no exports, so the bundle cannot be imported as it comes. A tool
  can bundle a one-line page whose entry hands the module to a hook, wrap the
  chunk as an ES module with a stable name, and write a `.d.ts` read from the
  `.bend` source: `import { slots, type Iv } from "./dist/core.js"`, no hash
  lookup, no global. Each def's name maps to a function taking its arguments
  in one call or curried. A def with an erased (`-`) parameter, or a Bend type
  with no JS encoding, is better refused than guessed.

### What the runtime will not tell you

Every one of these passes the proofs and passes the laws. Only a test at real
scale finds them, which is why the last step below is not optional.

- **Values cross in the runtime's own encoding**: a Nat is a `BigInt`, a list
  is `{ $: "Con", head, tail }` ending in `{ $: "Nil" }`, a constructor is
  `{ $: "Iv", s, e }` — its name and its fields by name, though Bend builds them
  positionally. `Nat.div` runs as BigInt division. Base's generics are encoded
  the same way, with Base's field names: `{ $: "Some", value }` and
  `{ $: "None" }`, `{ $: "Done", value }` and `{ $: "Fail", error }`,
  `{ $: "Inl", value }` and `{ $: "Inr", value }`, `{ $: "Unit" }`. Declared in
  a `.d.ts` as `BendMaybe<T>`, `BendResult<E, A>`, `BendEither<A, B>` and
  `BendUnit`, they let a core return its first error as a `Result`, and tsc
  makes the host handle every constructor.
- **`Nat.min` and `Nat.max` recurse once per unit at run time.** The other Nat
  operations compile to one BigInt operation each, but these two are plain defs
  that peel a successor off both sides, and the compiled JS is
  `q(n-1, t-1) + 1`: one stack frame per unit. Every operation called on
  (3000000, 2000000) through the JS module:

  | fine | overflows (`RangeError: Maximum call stack size exceeded`) |
  |---|---|
  | `Nat.add`, `sub`, `mul`, `div`, `mod`, `is_le`, `is_eq` | `Nat.min`, `Nat.max` (already at 1e5) |

  An epoch minute is about 3e7, so a core that takes the min of two times fails
  at run time. Pick with one comparison instead — `pick(Nat.is_le(a, b), a,
  b)` — and prove it equal to `Nat.min` once, so every fact about `Nat.min`
  still applies.
- **A def that recurses once per list element overflows the JS stack past
  about 12,000 elements, and the mechanism is the call's position.** The
  backend turns only a call in *tail* position into a jump, which the runner
  loops on; a recursive call inside an argument — `Bool.and(p(h), walk(t))`, or
  a constructor holding both halves — is an ordinary native call and costs one
  JS frame per step. So an accumulator form (`walk(t, f(h))` in tail position)
  runs flat, while the same function written as an argument stops at the
  stack: a walk over a list returns up to 12,288 elements and throws at 12,289;
  walking an object field by field, each field looking its key up from the
  front, costs two frames per key and stops at 6,144. The point moves with the
  frame size and with the shape, so the proofs cannot see it.

  **The fix that keeps every proof: a runtime twin, proved equal.** Leave
  the form the laws are proved on in the core as the spec, add a twin that
  runs flat, prove one law, `twin(s) == spec(s)`, and have the host call the
  twin. Choose the twin by what it allocates, not only by its stack: a
  tail-recursive tokenizer (build backwards, reverse) fixed csv-lib's stack
  but still held a token object per character, all live at once (10 MB of
  CSV: 2.9 GB). The twin that paid off fuses the pass away: a loop over the
  string, `run(t, step_m(classify(c), m))`, whose `step` has the spec
  machine's arms with each self-call `go(t, ph, st, out)` written as a state
  `Run{ph, st, out}` and each answer as `Stop{r}`, which later characters
  leave alone. The equality is one induction on the input, generalised over
  the state: the character case is a lemma split on token x phase whose
  every arm is the induction hypothesis (passed as a closure) or a
  `run_stop` lemma -- a table a script generates from `step`. It checked on
  the first run, the six existing proofs did not change, and the peak fell
  to 0.9 GB (csv-lib `PROOF.bend`, `parse_fast_is_parse`).
- **Base's string building emits ropes.** `String.reverse` and any
  `SCon{c, acc}` accumulator compile to `c + acc` per character, so a string
  the core builds reaches the host as a rope of one-character nodes, all
  retained while the result is. In csv-lib that was half of the remaining
  peak. bend-emit (since edcf64a) lowers `String.reverse`'s loop, and any def
  of the same shape, to a flat native reverse: 10 MB went from 0.9 GB to
  0.42 GB. A string the core builds forwards with `+` is still a rope; build
  it backwards and `String.reverse` it, or flatten it in the bridge. Consuming a
  string with `SCon` matching is *not* quadratic under bun: the emitted
  `slice(1)` does not copy. A pure machine still costs about 3.5x a
  hand-written parser in time (a new state object per step). Put the size a
  host will pass into the scale test, and state the ceiling in the README.
- **Check every number at the door.** The core's laws hold for the unbounded
  Nat, and the run time stops at 2^48-1; a negative BigInt is not a Nat at
  all. The host refuses such values before calling the core.

### The build and the bridge

- **Build the module** with `bunx bend-emit core.bend dist`. Extend the tool if
  it refuses a type; do not work around it in the bridge. What it refuses, and why,
  measured:
  - **It reads a `type` body as one constructor per line.** A constructor split
    across lines, or a comment between the header and the last constructor, fails it
    with `a constructor of X is not Name{field: Type, ...}`. Keep the body plain.
  - **It encodes `Nat`, `Bool`, `String`, `U32` and the generics** (`List`, `Maybe`,
    `Result`, `Either`, `Unit`), plus the types the file declares, and nothing else:
    a signature mentioning `Char` fails with `no TypeScript encoding for the Bend
    type Char`. At that one boundary take a `U32` and build the `Chr{c}` inside --
    a `Char` and its code are the same value there, and strings cross to the host as
    bytes (language.md 2.1) -- or extend the tool, which is the rule above.
- **The bridge** hands the host's value to the bend-schema package's codec
  (`src/codec.ts`, `toRaw`), calls the core's entry point, which checks the
  value against a schema written in Bend and then validates it, and words a
  returned error with `errText(err, "<name>")`. The codec rejects nothing: a
  number the Nat cannot hold becomes `RBad`, and the core reports it at its
  path. Every domain rule belongs to the core, and is proved — see "The core
  validates" in `references/workflow.md`. Once that holds, the bridge has no
  business logic left: it is the codec, the wording of errors, and the IO.
- **Delete the TypeScript implementation**, and point its existing tests at the
  bridge, so the tests that were checking the old code now check the core.
- **Add a test at real scale** (epoch minutes, real money, a full day of
  minutes). That is the only step that reaches the four traps above.
