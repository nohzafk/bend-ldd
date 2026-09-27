# language.md — the rules of a def, the runtime, and the limits

What writing Bend terms actually costs. Every rule here was paid for by a
failed build, and the failure is quoted beside it. Read `bend guide` first,
then `~/.bend/bend2/base.bend` — the standard library is a working example of
every rule below, and it ships facts you can import instead of proving.

**Syntax and types are not in this file.** `bend guide` is their authority and
it ships with the compiler, so a copy here could only drift from it. Proofs
are in `proofs.md`. Calling a core from JavaScript is in `js-host.md`.

Three parts: the rules a def obeys, the effects and the runtime, and what the
language is and is not for. A rule that turns out wrong is reversed in place,
and says so.

# Part 1 — The rules of a def

## 1.1 `match` heads a def body, and its scrutinee is a parameter

Not a style rule. `match` compiles to a tree of lambda-matches, and a
lambda-match applied to a value is a banned form in that compilation. The
comment above the check cites the `match_flatten` design (`bend2/bend.ts:2716`,
citing VictorTaelin's gist); the checks are at `bend.ts:2771` (computed
scrutinee) and `bend.ts:2871` (a let-bound local). The parser refuses a `match`
that is not in head position at all (`bend.ts:1855`).

- **A computed value cannot be matched.** `match String.starts_with(s, p):`
  fails with `a match cannot scrutinize a computed value: give it its own def`.
  A pair destructuring `(a, b) = f(x)` is a match too, and is refused the same
  way. Give the value its own def, where it is a parameter -- which is why the
  same name appears as `x` and as `x_go` / `x_from`.
- **A projection cannot be matched either, and there is no projection.**
  `match rec.field:` is refused, and `rec.field` in expression position fails
  with `expected : a defined name`. Read fields by destructuring, which is why
  one-line extractors exist:
  `def name_of(r: T) -> String: match r: case T{name, _, _}: name`.
- **No match inside a case arm.** Several things to inspect travel in
  together: `match a b:` splits on several scrutinees at once, with nested
  patterns (`case 1n+f CS{Job{step, dur, people}, t, ...}`), and `case 0n _:`
  is allowed.
- **Expose every argument the checker has to compute through.**
  `Nat.cmp(a, b)` only reduces when *both* arguments are constructors, so a
  lemma about `cmp` usually needs a joint match (`match x m:`), not a nested
  one. The obvious two-lemma proof of `x <= x + m` (split on `x`, then on `m`)
  cannot be written as two defs at all (1.2); as one `match x m:` it is four
  cases and no lemmas.
- **A branch on a computed Bool goes to a def that takes the Bool as a
  parameter and matches it**, the way Base's `List.filter.put` does it. A state
  record whose next step matches a stored Bool also compiles -- a fuel loop
  with one state constructor per phase is the shape a hand-written parser
  takes -- but it hides the decision from a proof (proofs.md 1.5).
- **The match consumes its scrutinee.** A value that is matched and then built
  again needs the `+` mark where it was bound:
  `case 1n+f Step{+miss, ...}: match miss: ... Missing{miss}` passes.
- **`match a b:` lists its scrutinees in the order the parameters are
  declared.** `def not_succ_le(bp: Nat, a: Nat, h: ...)` with `match a bp:`
  is refused with `a match on a parameter or field (this name is a def or a
  consumed binder: give the value its own def)`; declared `(a: Nat, bp: Nat,
  h: ...)`, the same match checks.
- **A proof inside a tuple pattern takes no `+`.** `case (+k, +e):` on a
  dependent pair `&k:Nat -> {Nat.add(a, k) == b : Nat}` is refused with
  `expected : an annotated term (cannot infer)`; `case (+k, e):` checks. Mark
  the data, and use the proof once (an equation used twice is passed as a
  def parameter marked `+`, which works).
- **Two arms of the same constructor need not mark their binders alike.** A
  report that they must did not reproduce.
  All three check: `case ZzN{n}: ... case ZzN{+n}: ...` in a plain `match`; the
  same two arms in a joint `match a b:`; and with a `List<&2, Nat>` field
  consumed twice in one arm and once in the other. Mark each arm for its own
  uses. (A duplicate arm is dead code either way -- the first match wins.)
- **Nested patterns work and pay for themselves**: `case SCon{Chr{x}, t}:`
  binds the code point, and a list binds as `case h <> t:`. Nested
  constructors nest inside fields (`case T{_, Some{ds}, _}`), and a list's
  element constructor can be matched inside the list pattern
  (`case Some{iv} <> t:`), but a `Con` pattern cannot carry a `<>` inside it:
  `case Con{n <> t}:` is refused, write `case n <> t:`. A tuple pattern
  destructures a nested dependent pair: `case (+pre, w, post, eq, c):`.
- **A character can be matched as a literal, not only bound.** `case SCon{Chr{44}, t}:`
  checks, and so does a joint match that pins a two-character sequence
  (`case SCon{Chr{13}, SCon{Chr{10}, t}} ...:`), which is how a parser sees a CRLF.
  Base never does this -- it binds `Chr{x}` and compares the `U32`
  (`case SCon{Chr{x}, t}:`, then `U32.is_lt(x, 48)`), so nothing there demonstrates
  the form. The code in a pattern is a `U32` literal and takes no suffix:
  `Chr{44n}` is refused, `expected : U32 / observed : Nat`.
  **REVERSED: do not design a core around this.** A literal pattern does not
  reduce when the character is abstract, so a law about such a core is
  unprovable. Measured: a goal `{go(SCon{ch, t}, PhUnq{}, st, out) == R : Res}`
  with `ch : Char` is reported **unreduced**, the term printed as written --
  the checker can prove neither `ch == Chr{44}` nor `ch != Chr{44}`, so it
  commits to no arm. The same stuckness reaches one level up: a predicate
  written on those characters (`Clean(s)`, defined by matching `Chr{44}`,
  `Chr{34}`, `Chr{13}`, `Chr{10}`) does not reduce either, so the hypothesis
  every such law needs is itself inert. The concrete case is the control: the
  same goal at `SCon{Chr{97}, t}` checks by `{==}`. This is why Base never
  writes a literal character pattern -- it binds `Chr{x}` and compares the
  `U32`. A core whose laws must reason about characters has to **classify the
  character into a datatype (or a Bool) and match on that**: a datatype has
  constructors a proof can split into, and a `U32` code point has none. The
  cost of getting this wrong is a core that runs, passes its oracle, and cannot
  be proved at all.
- **A def in the same file takes no module prefix, and a rewrite needs an
  equation to rewrite.** Two facts that cost a round each while writing a proof
  over one's own core:
  - the module alias applies only to what comes from that module. A def of the
    file's own is `toK(p)`, not `C.toK(p)`, which is refused with
    `expected : a defined name`.
  - `%e : P` annotates a **goal**, so a def whose declared return type is a plain
    type (`-> C.Res`) has nothing for `%` to rewrite: it is refused with
    `expected : C.Res / observed : {... == ... : C.Res}`. State the step as an
    equation in the return type, and put the `%` rewrites there.
- **A constructor takes its fields positionally.** `SCon{c, t}`,
  `St{Nil{}, SNil{}, False{}, 1n}`, `Line{bad, rows}`. `SCon{head: c, tail: t}` is
  refused with `expected : a term / observed : ':'`. Named fields appear in a `type`
  declaration and nowhere else.
- **A joint `match` binds a dependent pair to one name, and the chain comes
  apart on its own.** `match s h:` with `case SCon{Chr{x}, t} hc:` is accepted --
  the second scrutinee binds whatever its type is, a `&` chain or a sigma
  included -- while writing the chain as a nested pattern there is refused with
  `expected : 2 patterns (one per scrutinee)`. To take the parts, match the
  evidence **alone**: `case (hse, hqu, hcr, hlf, ht):` destructures a chain, and
  `case (p, heq, ht):` a sigma, in a def or an accessor that takes the evidence as
  its parameter. `match h s:` is refused (the law's predicate is a def, so it is
  `a match on a parameter or field`), and `match s h:` is the form that works.
- **Matching on a parameter rewrites every hypothesis that mentions it**, which
  is what makes decision-as-parameter proofs work (proofs.md 1.5).

## 1.2 Definitions are a DAG, and recursion is self-recursion that decreases

**Narrowed.** This section used to say that nothing in a file can refer to
anything below it. That still holds for safe defs, but it no longer holds for
datatypes or for unsafe defs. One case per line:

| case | result |
|---|---|
| a safe def calls a safe def below it | refused: `expected : a filled definition (an unfilled law is a dead claim: live code cannot use it)`, `observed : g` |
| two safe defs call each other (`even`/`odd`) | refused, the same error at the first forward call |
| a safe def calls an unsafe def (`def g?`) below it | refused, the same error |
| `type Forest` holds a `Tree`, and `type Tree` is declared below it | checks, and runs |
| a def returns `Iv`, and `type Iv` is declared below it | checks, and runs |
| an `@unsafe def` calls an `@unsafe def` below it | checks, with `All terms check, but 3 defs rely on unsafe or foreign code` |
| `def even?` and `def odd?` call each other | checks, and runs (`even(7n)` is `odd`) |

`def f?(..)` is new sugar for `@unsafe def f(..)`. The error for a forward call
changed as well. It used to be `expected : a defined name`, and now it is the
unfilled-law error, because every name is declared up front. So the rule below
is for **safe** defs, and safe defs are what laws and proofs are made of.

No forward references and no mutual recursion among safe defs, so they form a
DAG. That is what makes the termination check per def (`bend.ts:3402`:
arguments are read left to right, each passed unchanged until one shrinks).

- **A safe def may only call defs defined above it.** base.bend
  forward-references through laws (`law Nat.read.go` at base.bend:2067 is
  called before its def). A user file cannot do this. Base's law-then-def
  arrangement looks available -- `law String.cmp` declares a type at
  base.bend:1781, `def String.cmp.fin` at 1786 calls it, `def String.cmp(a, b)`
  fills it at 1797 -- but in a user file it is refused at the call site:
  `expected : a filled definition (an unfilled law is a dead claim: live code cannot use it)`.
- **So no two defs call each other, and a helper cannot call its caller.** A
  terminal helper calling the loop def fails like any other forward call. End
  branches that terminate without re-entering the loop may sit above it;
  anything that re-enters is inlined into its branch body. Three ways out:
  - fold the cycle into one def with a joint match: `match fuel st:` with
    `case 1n+f Phase{...}` handles the fuel and the state in one match, the way
    base matches `match s n:`;
  - take the branch as a parameter;
  - pass the recursive result in as a function argument: a lemma's step takes
    `ih: A -> B`, and the recursive def calls it with `hh => self(rest, hh)`.
- **`Bool.or` breaks a two-def cycle for free.** `has(xs, s)` and a helper that
  decides whether to keep walking cannot call each other, and early returns
  need a match on a computed value. When there is no need for
  short-circuiting, `Bool.or(String.eq(h, s), has(t, s))` is one line, both
  arguments evaluated, and the recursion stays in one def. Neither `Bool.or`
  nor `Bool.and` short-circuits in its second argument.
- **Every self-call must decrease, and the shrinking argument comes first.**
  `expected : a decreasing self-call (arguments are read left to right: each passed unchanged until one shrinks)`
  -- "passed unchanged" means *a variable*, and the order of the def's own
  parameters decides. `exec_level(failed, lvl)` with `lvl` shrinking is
  refused, because position 1 is `mark(failed, n, ok)`, a computed
  accumulator; the same call as `exec_level(lvl, mark(failed, n, ok))` passes.
  A local binding does not fix it: in a `do` block `x = expr` is a *bind*
  (`{x : IO(--)}` desugared), not a `let`, so `failed2 = mark(failed, n, ok)`
  before the call produces `expected : a pattern (a binder or a constructor)`.
  Reordering the arguments is the fix.
- **A def that walks two structures is accepted when, reading the arguments
  left to right, one shrinks and the ones before it are unchanged.** Measured on
  a `check(iv, r)` shape with a joint `match iv r:`: `check(Iv{s, e}, rr)` --
  the first argument rebuilt in the same constructor from the same binders, the
  second shrinking -- checks. Rebuilding the first from a *changed* field is
  refused with `expected : a decreasing self-call (arguments are read left to
  right: each passed unchanged until one shrinks)`. So "passed unchanged" is
  read as the same head constructor over the same binders, which is what lets a
  walk carry a rebuilt first argument while the second shrinks.
- **A walk whose list is the shrinking argument needs no fuel**, even when the
  accumulator is computed: `collect_ivs(t, iv <> acc)` passes, because `t` is
  first and shrinks, so everything after it is free. But a transition that
  hides the list inside a constructor (`ivs_run(IC{t, acc, iv_of(h)})`) does
  not show the decrease. A fold over Maybes needs no state machine: map first
  (no branch, plain recursion), then fold, matching the element's constructor
  in the list pattern:

  ```python
  def maybes_of(+xs: List<&2, J.Json>) -> List<&2, Maybe<&2, C.Iv>>:
    match xs:
      case Nil{}:   Nil{}
      case h <> t:  iv_of(h) <> maybes_of(t)

  def collect_ivs(+ms: List<&2, Maybe<&2, C.Iv>>, +acc: List<&2, C.Iv>) -> Maybe<&2, List<&2, C.Iv>>:
    match ms:
      case Nil{}:          Some{acc}
      case Some{iv} <> t:  collect_ivs(t, iv <> acc)
      case None{} <> t:    None{}
  ```

- **When the number of steps can be computed, recurse on the count** (for
  example `ceil((hi - lo) / step)` candidates), and the fuel goes away.
- **A fuel is for loops where nothing else shrinks** -- a server loop that only
  carries a listener, or a walk over a graph. `App.run` starts its loop with
  `U32.to_nat(4294967295)`. A zero-arg `loop()` or a `Chan` passed unchanged is
  rejected, and hiding the call inside a lambda passed to another def does not
  help: the checker follows the closure. A hand-written parser therefore
  replaces recursion with an explicit stack of frames and a fuel counter. A big
  fuel numeral costs a proof (proofs.md 1.3).

  ```python
  def serve_loop(fuel: Nat, l: Listener) -> IO(Unit):
    match fuel:
      case 0n: ...
      case 1n+f: ... serve_loop(f, l2)
  ```

## 1.3 Quantity lives in the type

From the book (`basics-types`): `Type` is short for `Kind(&1)` and `Data` for
`Kind(&2)`. The number is how many uses a value allows.

- **`+` marks a reusable binding, and reuse means copying, so `+x` requires
  `Data`.** A binding used twice is refused with
  `expected : a / observed : a (consumed more than once)`. The mark goes on a
  def parameter (`def f(+a: Nat)`), on a pattern binding (`case 1n++p:` -- the
  second `+` is the mark; `case +h <> +t:`; `case Con{+h, t}:`), on a local
  (`+d = U32.sub(x, 48)`), and on a do-block binding (`+req : J.Json = ...`).
  Annotations inside the body count as uses, so a proof that rewrites with a
  parameter several times needs `+`. A law's binders take the mark instead of
  the proof's parameters (proofs.md 1.1).
- **A handle cannot be marked.** `Socket`, `File`, `Listener`, `Chan(...)` are
  `Kind(&1)`: marking one is an error, and being affine it must be threaded
  back out of whatever consumed it. That is why `TCP.send` and `TCP.accept`
  return `(handle & Result)` rather than `Result`.
- **Copy counts are part of list types.** `List<Char>` desugars to `&1`, so
  `String.to_list`, which returns `List<&2, Char>`, fails against it. A value
  built around a `List<T>` is `Type`, not `Data`, and cannot be walked twice or
  appear on both sides of a law; declare the lists `List<&2, T>` and the record
  `is Data` when a law must mention them.
- **A generic with several type parameters takes one quantity per parameter.**
  `Result<&2, &2, Err, Nat>` checks; `Result<&2, Err, Nat>` is refused with
  `expected : Result with 4 parameters`. Base's `Result` and `Either` take two
  types, so two quantities; `List` and `Maybe` take one. Omitting them all
  (`Maybe<Nat>`) also checks, and means `&1`: `+m: Maybe<Nat>` is refused
  with `expected : Data / observed : Type`.
- **The error for getting quantity wrong names the wrong value**: the
  context points at a different parameter, and says only
  `expected : Data / observed : Type`. A type alias used where a datatype is
  expected is declared `-> Data`, not `-> Type`.

## 1.4 Base's higher-order defs take closed templates

- **User defs can call Base's higher-order defs with lambdas** --
  `List.filter(~Char, ~(c => Char.is_digit(c)), xs)` works. But every `~`
  argument must be closed at compile time: a lambda that captures a runtime
  value is refused with
  `done is a variable here, not comptime: pass it at run time`. So a walk whose
  predicate needs state cannot use `List.filter`, `List.all`, `List.find` or
  `List.contains`; it is hand written.
- **Reversed in part: a law can quantify over
  a template parameter of your own def.** This used to say a generic lemma
  over template parameters is impossible to state. That still holds for
  Base's `List.filter(~A, ~f, t)` with `A` and `f` as the lemma's own
  parameters. But for a def written with a template function parameter,
  `def all_ok(~f: Nat -> Bool, xs: List<&2, Nat>) -> Bool`, the law
  `for ~f: Nat -> Bool ... {f(x) == True{} : Bool}` states, its proof
  (`def head_ok(f, x, t, h)`, the proof's parameters without `~`) checks, an
  induction that passes `~f` along checks, and a project instantiates the
  theorem with its own closed def (`head_ok(~small, x, t, h)`). Controls: a
  false law over `~f` (`all_ok(~f, [x]) == True` for every `f`) is refused
  with `expected : Bool.and(all_always~f(x), True{}) / observed : True{}`,
  since `f(x)` stays abstract; the instantiated use checks. A template def is
  not exported by the bundler, so a tool that writes `.d.ts` must skip it. A
  function cannot instead be stored in a `Data` field: `type Rule is Data:
  Rule{f: Nat -> Bool}` is refused with `expected : Data / observed : Type`.
  This is what makes a library generic over its caller's rules.
- **A template argument's signature must match the parameter's exactly,
  `+` marks included.** A def `plan_rule(+tag: Nat, r: Raw)` does not
  instantiate `~rule: Nat -> Raw -> Maybe<&2, Err>`; write the rule with plain
  parameters and mark only its inner helpers. A project with no rules passes a
  def that ignores both (`no_rule(tag, r) = None{}`), and a host, which cannot
  call a template def (the bundler skips it), gets a closed wrapper
  (`check0(s, r) = check(~no_rule, s, r, None{})`).
- **`List.append` and `List.length` take their quantity and type as plain
  parameters** (`List.append(&2, C.Iv, xs, ys)`), not as `~` templates, so a
  lemma over variables can use them.

## 1.5 What these rules do not justify

Three kinds of thing get conflated when a compiler is new. Keep them apart:

1. **Rules with a reason.** Everything in this Part. They cost a round each and
   are then free.
2. **Broken diagnostics.** The compiler limits in 3.4. They are filed.
3. **Verbosity.** A projection def, a `_go` helper, a state record instead of a
   nested match. This is what the language compiles to, and a language written
   to be produced mechanically pays nothing for it.

Only the middle kind is worth a change. Nothing in the third bucket is.

---

# Part 2 — Effects and the runtime

## 2.1 An effect is a def that imports a host file

- **One def with two imports runs in both lanes** (guide, *Top level*):

  ```bend
  def Stdin.read_line() -> IO(String):
    import "./effs/stdin_read_line.c"
    import "./effs/stdin_read_line.js"
  ```

  The C twin is not optional for a binary: without it, `bend prog.bend -o out`
  fails with `Error: no .c import: <def>`. The `.js` twin is the one the run
  lane uses, and neither lane needs the other's file to run.
- **bend accepts only a `.c` or `.js` path**, so TypeScript is compiled first,
  and the runtime evaluates the file as a *script*:
  `SyntaxError: Unexpected keyword 'export'`. The artifact may have no
  top-level ESM syntax; an entry file assigns the one name bend looks up on
  `globalThis`.
- **An effect's JS function name must equal the def name**: `Tz.convert` ->
  `tz_convert`. The file name is irrelevant.
- **An effect that needs an npm package** is evaluated inside bend's own
  bundle, so `require("luxon")` resolves from `/$bunfs/root/bend` and fails
  there, local `node_modules` or not. Bundle the package into the artifact, or
  require its CommonJS entry by absolute path; compiling first
  (`bend main.bend -o main.js && bun main.js`) runs outside the bundle.
- **An effect that returns a plain value returns it bare.** `io_done` is the
  `Done` constructor of a `Result`; wrapping a list in it hands the other side
  a `Done` where a `Con` was promised
  (`TypeError: ... evaluating 'us_0["nat_in"]'`).
- **Strings cross as bytes.** `io_text(bytes, n)` takes a length in bytes, and
  `String.length` counts UTF-16 code units, so a length from `.length` cuts any
  non-ASCII answer short; take it from `TextEncoder`.
- **The build names the foreign code**:
  `All terms check, but 3 defs rely on unsafe or foreign code: ...`. The trust
  boundary is in the build output.
- **When a patch fails to compile, the old binary runs.** `>/dev/null` on a
  bend build has cost a whole round of debugging; read the build output.

## 2.2 Park, never block

`~/.bend/bend2/effs/` has no stdin effect: no `read_line`, no `getline`. The
"input" in the guide's effect list is App keyboard and mouse; `IO.args()` does
answer the command line. Reading stdin means adding an effect, and the rule
that makes it work is the one that cost the most here.

**A host function must park the computation, never block it.** Both lanes run
one event loop, so an effect that blocks inside its host function stalls every
other computation in the program. Same program, a ticker every 300 ms beside a
stdin reader whose data arrives late:

| blocking `readSync` in the JS effect | parked with `io_park_on` |
|---|---|
| `0.07 tick 11`, then nothing until `1.99` | `0.08 tick 11`, `0.38 tick 10`, … |
| the loop froze 3.9 s; ticks 10..0 all ran at the end | interleaved, line for line like the native lane |

**The C side**

- `io_wait_on(w, fd, evts, time, more)` parks and returns `IO_PARK`; the loop
  calls `more` when the fd is ready, or the deadline passes. `evts` is 0 for
  "no fd" -- **the fd itself may be 0**, since the poll loop adds an fd
  whenever `a->evts != 0`.
- `io_sys_end(w, n)` puts `errno` in `w->code` and returns the count, so
  `w->size = io_sys_end(w, read(...))` and `w->code == EAGAIN` is the test for
  parking again.
- **Give the wait a deadline when the fd may be a FIFO**:
  `io_wait_on(w, 0, POLLIN, io_tick() + 250000000ull, more)` wakes the effect
  four times a second, so its own `read` finds the EOF that `poll` will not
  report (below). `io_tick()` is nanoseconds.
- `w->data`, `w->size`, `w->made`, `w->hand` and `w->code` are the effect's own
  state across parks; `word` is the runtime's (the parked fd).
- `io_eff(CID_<NAME>, run, need)` registers it, and **the compiler generates
  that CID** from the def's name -- you only reference it.
- A one-shot blocking read is shorter (no `IoWork`: allocate, read to EOF,
  `io_str`, return) and it freezes the loop just as hard, so it is only for a
  program with nothing else to do.

**The JS side**

- `io_park_on(fd, out, k, more, at)` parks, and **returning `undefined` from
  the parked step means "park me again"**. `at` is a deadline the way `time` is
  in the C lane; `performance.now() + 250` is what lets a macOS FIFO be read to
  the end.
- A `need` function (`{read: true}`, `{time: true}`) parks *before* the first
  call. That is how `io_sleep` works, whose JS body is empty.
- `io_sys()` is a `bun:ffi` dlopen of libSystem -- `read`, `recv`, `poll`,
  `fcntl`, `errno`, `strerror`, … The `fcntl` wrapper hides the arm64 variadic
  calling convention, so `fcntl(0, F_SETFL, … | O_NONBLOCK)` works there too.
- The lane is one thread -- `--threads` and `--gpu` do nothing, pure code runs
  sequentially -- but its **effect loop is real**: it polls and it has timers.
  A `readSync` inside an effect is what makes it look otherwise.
- **A Bun event loop does not run while the interpreter holds the thread**, so
  a server cannot be `Bun.serve` polled by Bend; base's TCP parks on the
  listener fd instead, which is what a hub HTTP server built on it uses.

**macOS: a FIFO's close is invisible to `poll`**

Not a Bend bug, but it decides which stdin sources work. The same probe, with
no Bend in the program, on three machines:

| | `poll` | `select` |
|---|---|---|
| Linux 5.15 | `revents=0x10` | True |
| macOS | never returns > 0 | True |
| iSH | never | never |

**Only a FIFO with a name fails.** `fstat` answers `S_ISFIFO` for a named FIFO
and an anonymous pipe alike, so the difference is the name, not the object
type. `producer | bend prog`, `< file`, a terminal and `<(cmd)` (an anonymous
pipe, in zsh and bash on macOS) all see EOF; `mkfifo` plus `< fifo` does not.
iSH emulates syscalls, so its column is its own limit, not Linux's. Both Bend
lanes wait with `poll`, so on macOS a FIFO never sees EOF, and unsetting
`O_NONBLOCK` changes nothing. A wait with a deadline works around it (above):
the effect re-reads, and the read sees the EOF.

## 2.3 Two lanes, two hosts: effects cannot share by file scope

- **The native lane splices every effect into one C translation unit, so
  effect symbols are shared.** One effect declares
  `extern void in_hold(const char*, size_t);` and calls another effect's
  helpers as ordinary functions. **The JS lane wraps every effect in its own
  IIFE**: a symbol from another effect's file is a free variable there, reads
  as `undefined`, and the first call crashes the process with no message. The
  fix is a bridge on `globalThis`: one effect publishes
  `globalThis.inHold`, `globalThis.stdMessageTake` and `globalThis.stdFill`,
  and every other effect calls them through it. The access happens at call
  time, so the order the IIFEs run in does not matter.
- **Module state survives between calls.** Bend loads an effect module once and
  calls into it per request, so a JS `Map` at file scope keeps its entries.
- **An IoWork's fields are free only within one step.** A deadline stored in
  `w->made` was rewritten by the runtime across parks, and the effect timed
  out early. State that must survive a park goes in a file-level static.
- **Parked and waking is not the same as reading.** After a park, the waking
  step must pull bytes from fd 0 before it can parse anything. A wait loop that
  only re-parses the buffer it already had runs dry and reports a false
  timeout, on both lanes. Expose a fill function (C: one non-blocking read
  until EAGAIN, EOF exits; JS: the same through `globalThis`), and call it
  right after waking.
- **When both ends of a pipe number their requests from 1, the first outbound
  id collides with the client's first pending request**, and the client
  swallows the request as an answer to its own call. An effect that sends
  requests numbers its own counter from high ground.
- **EOF must not end the process while a complete frame may still be in the
  buffer.** A fill that exits on `read() == 0` races the frame it just buffered
  and loses it -- invisible while the peer's pipe stays open, and fatal for a
  file or a client that half-closes. Fill only reports (bytes arrived / would
  block / EOF); the caller re-checks the buffer first and shuts down only when
  nothing is pending.
- An effect that does request/response correlation should return the whole
  response message, and let a JSON library pick the field out of it. The fewer
  things the two lanes must agree on by hand, the better.
- **The lanes are not the same speed at waiting.** The C lane waits on the file
  descriptor; the JS lane sleeps until a deadline, so the deadline is the
  latency. A 250 ms default deadline costs 250 ms per exchange; 5 ms is a
  better start for a request/response loop.

## 2.4 Byte-level framing lives in the effects

Any protocol that counts bytes -- a header plus an exact body length -- is byte
work, and byte work lives in the effects. Bend never sees a header. A Bend-side
scanner would be O(n) per byte through `String.drop`, and the byte count of a
frame is not the codepoint count of the Bend string that carries it.

The transport is two effects:

- One reads: it returns a message with the framing removed, and ends the
  process when stdin closes. Its byte buffer persists across calls, because one
  `read` can return bytes of a later message.
- One writes: the framing added, the length taken from `io_cstr`, which returns
  bytes, not codepoints.

The runtime helpers that make this short: `io_cstr(e, term, &len)` turns a
String term into bytes plus a byte length, `io_out(stdout, data, len)` writes
them, `io_bytes(text)` is the JS twin of `io_cstr`, and `io_text(bytes, len)`
is the JS twin of `io_str`, which decodes UTF-8 the way WHATWG does: valid
UTF-8 survives the round trip, a broken byte becomes U+FFFD.

---

# Part 3 — Strengths, limits and what the compiler cannot do

## 3.1 What the language is good at

- **The core is small**: no manifest, no `pub`, no module declarations, types
  inferred, records and matching and reuse marks and `do` blocks. Programs
  come out shorter than the same behaviour in a conventional typed language.
- **The foreign boundary is yours to place.** A protocol state machine can live
  inside the checked language, leaving only a thin system-call shell in the
  host.
- **One binary checks, runs and builds**, and the interpreter is a real edit
  loop.
- **The capability is real.** "For any two distinct names, this resolves in
  this order" or "for every input, the answer is exactly the candidates that
  fit" can be stated and proved -- which a type system cannot say.

## 3.2 What it is not good at yet

- No forward references and no mutual recursion among safe defs, so a file's
  defs are ordered bottom-up (datatypes may come in any order, and unsafe
  defs may recurse mutually, 1.2); `match` cannot stand in a `do` block, so
  every step that inspects a value becomes its own def; the reuse marker has
  its own rules and its own misleading errors.
- A thin standard library and a young ecosystem. Bend's own language server is
  formatting-only; a community one adds diagnostics and hover but no
  completion; libraries (JSON, HTTP) come from the hub, named `name@version`.
- The two lanes are not the same language (2.3).
- **A symbolic goal over an unfolded loop is expensive to write.** A rewrite
  restates the whole goal, and a goal over a wide state runs to
  thousands of characters, so such proofs end up generated. The first laws of
  a project are pleasant and the symbolic ones cost ten times more: the most
  valuable kind of proof is the most expensive kind -- unless the core is
  shaped as in 3.5, which keeps goals short.

## 3.3 What laws buy, and what they do not

- **Laws find design problems; tests find bugs.** Laws force the pure core out
  of the live path (a law file cannot import effects), force one source of
  truth where two computations must agree, and turn "what must this
  guarantee?" into a review that finds specification gaps.
- **They rarely find a bug in code that already works.** The bugs that ship
  live where the checker cannot see: the effects, the wire, the disagreement
  between two lanes. But restructuring a core so that a law *can* be proved
  often removes runtime failures on the way (a fuel loop that hung on a zero
  step, rows returned in reverse).
- **The risk is not correctness but cost**: if a new law costs enough, the
  specification stops growing.

## 3.4 What the compiler cannot do

These are limits of the checker, not of the method. Each is worth a
workaround; none is worth redesigning a core around.

| limit | what it costs |
|---|---|
| a large numeral | a big fuel numeral the checker must unfold overflows its stack, so a program looping on a large fuel cannot prove anything about that loop; the cost is a fuel parameter on every decision function, so a law can pass a small one |
| a rewrite | it must restate the whole goal, so a goal over a wide state makes a long annotation. **Write the motive with the program's own source terms, not the printer's normal form**: the checker compares up to computation, so the annotation may name the term the program constructed (proofs.md 1.2, `references/examples/issue964.bend`). What is left is length, not impossibility. |
| the printed goal | it cannot always be written back: a hub def prints by content hash, which does not lex; a local module prints by file name, while the annotation needs the import alias; the empty list prints as `[]`, while the constructor is `Nil{}`. This is a printer limit, not an annotation limit -- name the term as the program writes it (proofs.md 1.2) |
| a quantity error | it names the wrong value |
