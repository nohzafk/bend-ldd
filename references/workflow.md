# Bring one function under proof

The workflow, in order, for a function that must be right for every input
rather than for the cases somebody thought of. It does not assume a host: the
core is `core.bend`, `LAWS.bend` and `PROOF.bend`, and the gate is the checker.
If a JavaScript program is the caller, read `references/js-host.md` as well, for
the project layout, the module build, the bridge and the test at real scale.

Before starting, read `SKILL.md`, then `references/language.md` and
`references/proofs.md` as the checker refuses things. They are the rules of the
language and of the method. This file is the order to apply them
in.

## The core validates

A core has two layers. The **validating layer** takes the raw input, exactly as
the host has it (cumulative bounds, plain ids), and returns either a validated
value or the **first** error. The **computing layer** takes only validated
values. Parse, don't validate: the validated type should make invalid states
unwritable, so the computing layer and its laws need no preconditions.

- **What counts as valid is a specification decision.** State it as a small
  predicate the human approves with the laws, not as checks someone wrote in the
  bridge.
- **Errors are data.** Give each kind of error its own constructor, carrying
  where it happened (`NotIncreasing{index, prev, up}`). The host gets a
  discriminated union, and its compiler makes every caller handle every error.
- **Report the first error only.** One error keeps the error laws short, and it
  is enough for a caller to fix the input and try again.
- **Overflow is an error too.** If a result could pass the Nat bound, prove a
  bound on it (`charge(plan, n) <= n * max_price`), and have the core check that
  bound and return an error. Do not leave a hand-reasoned check in the bridge.

The validating layer needs four laws, all at the level of the predicate and
cheaper to prove than the computing layer's:

1. **Sound:** a value that validates satisfies the predicate.
2. **Complete:** raw input that satisfies the predicate validates; nothing
   valid is rejected.
3. **Meaning-preserving:** validating and converting does not change what the
   input means. For example, the price of every unit is the same under the raw
   reading and under the validated form.
4. **Accurate:** the error reported names a real defect, at the place it names.

Composed, they give one law with no hypothesis: for every raw input, the answer
is the specified result when the input is valid, and an accurate error when it
is not. Once this is done, the bridge has no business logic left. It is the
codec and the wording of errors, plus the IO.

## The workflow

### 0. The gate

A core is `core.bend`, `LAWS.bend`, `PROOF.bend` and, beside them, a mutant
table and a `test.sh` whose order is the order to keep. `references/js-host.md`
lists the files in full for a JavaScript caller.

Each step below has a check you can run, and each check runs under a 5 s limit
(the `bend-check` wrapper in SKILL.md, and the timeouts inside the falsifier and
the mutant harness). Run the check before moving on. The checker answers in well
under a second, so check after every edit, not at the end. A check that runs
longer is a problem in the statement or the core's shape, never a limit to
raise.

### 1. Write down what the function must guarantee

Read the function and every test that pins it — or, for a new core, write down
what it must decide and who decides it. List the guarantees as candidate laws:
- **exact characterisation**: sound *and* complete (a filter that returns nothing is sound)
- **independence from irrelevant order**
- **monotonicity**
- **bounds on outputs**
- **agreement** between two ways of computing the same thing

Also list every edge case the TS handles specially, such as inverted ranges,
empty inputs and zero. Each is either kept (and a law should say so) or
deliberately changed (and the human must hear about it).

### 2. Write the core function in `core.bend`, shaped for the proof

The shape decides how hard the proofs are. Before copying an algorithm you
already have, look for the form with the shortest induction. A reformulation
can remove work *and* a hypothesis from the law: a core whose invariant is
local is stated without a hypothesis, while one that has to reconstruct a
global property carries one. Bend will not find that reformulation for you —
the checker judges the shape you hand it and never proposes one — so this is
the step to spend time on. The rules that shape it:
- one `match` per def, at its head, on a parameter
- a computed decision goes to a def **as a parameter** (`keep(x, rest, ok)`, `place(r, ...)`), so a proof can split on it
- a recursive call needed in only one branch is passed as a function (`v => add(rest, v)`), because two defs cannot call each other
- no forward calls: order defs bottom-up (datatypes may come in any order)
- **a fold over a large input gets a second, parallel entry point** whose law
  says it answers what the first one does: the cut is decided by a projection
  of the machine, and the law holds for every piece size. `language.md` 3.5 has
  the shape, the numbers, and the traps
- **do not call Base's `Nat.min` / `Nat.max`**: at run time they recurse once per unit and overflow the JS stack near 1e5. Pick with one comparison (`pick(Nat.is_le(a, b), a, b)`) and prove it equal to `Nat.min` (js-host.md)

Check: `bend core.bend` compiles. Then check **equivalence with the function
being replaced**, if there is one: compare the two on every small input, by
brute force, and classify every difference. "Same, or same without inverted
windows" is a finding to report; anything else is a bug. `references/js-host.md`
says how to call a core from a program, and it needs the user's permission to
add a tool.

When the core takes a different shape from the TS (widths instead of bounds,
say), the comparison script has to convert between them. That conversion is
the bridge's logic, and it is not proved. Run the comparison again in step 7
through the **real** bridge, against a verbatim copy of the old function.

### 3. State the laws in `LAWS.bend`, and falsify them before anyone approves

A law quantifies over all inputs (`for ws: ...`); a law about literals is a unit
test.

The core takes the host's raw input and returns a validated value or the
**first** error (see "The core validates" above). So besides the computing
laws, draft:
- the validity predicate, for the human to approve;
- the four validating laws: sound, complete, meaning-preserving and accurate.

Edge cases the old code mishandled become either rules in the predicate or
error constructors, not checks in the bridge. Add the small predicate each law needs (`covered`, `chain`, `all_cov`) to
`core.bend`, short enough to check by reading. Say "x is in xs" as a split, and
"a <= b" as `b == a + k` or a Bool equation.

Check the statements: `bend LAWS.bend` should report one TODO per new law.

Then **falsify** each law on hundreds of small inputs. `bunx bend-falsify` needs
the package installed, so **ask the user before you add it**: write a spec that
emits literal instances, and run `bunx bend-falsify spec.ts` (`--each` lists
every counterexample). lawcheck needs no spec and generates its own, so try it
first — it needs a bendlib submodule at `vendor/bendlib`.
Edge cases first: empty, zero, equal bounds, one element, inverted.

Draw the instances **around the law's hypotheses**, so that most instances
satisfy them. Uniformly random inputs rarely do, and Bend will not tell you
when a law is under-tested: a law with no reachable instance looks exactly like
a law that holds, and a bug can survive thousands of instances. A passing
falsifier run is evidence about the instances you chose, not about the core.
So build the instances from the hypotheses, and then plant a bug and confirm
the falsifier catches it. Run the default mode, and
use `--each` sparingly: it checks one instance per checker run, about 0.15 s
each, and prints its progress.

Then **control the falsifier**. Plant a bug in a copy of the core, point the spec
at it, and require a counterexample. A falsifier that never failed proves
nothing. If a planted bug survives, first check whether it is **equivalent**:
`n < w ? n : w` and `n <= w ? n : w` are the same minimum. Compare the two
functions directly before calling it a gap in the laws.

Then **sketch the proof of the main law**: which argument to induct on, and
which lemma each case needs. Do it before asking for approval, because the
sketch can change the core's shape. A specification whose invariant is global —
a running maximum, a range sum — needs a more expensive proof than one whose
invariant is local, and can need a hypothesis the cheaper form does not. Bend
reports neither: a core that is expensive to prove is not a core the checker
complains about. Found after approval, that change has to be approved again.

A counterexample at this stage is the most valuable output of the whole
workflow: it is a specification bug, found before any proof. A law is a
translation of the human's intent, and the intent is where the ambiguity is — a
law written from one reading of a boundary condition is false under the other
reading, and no proof will say so, because the checker will simply refuse. This
is why falsify before you prove: a counterexample here is that ambiguity found
at its cheapest, before there is a proof to rewrite.

### 4. Get the human's approval — the one step that needs a person

Show each law in one line of plain language, why it matters, and what
falsification found. Ask about any design choice the laws depend on (for
example, "does the core sort, or does the host?"), and about every edge case
from step 1 that the old code got wrong or left open: refuse it at the bridge,
or give it a meaning in the core. Mention any change of shape the proof sketch
suggests. The human may approve fewer laws than you propose; state only those
in `LAWS.bend`. Use a structured question
if one is available. **Write no proof until the laws are approved.** The human
reviews laws, not code; a proof of the wrong statement is worthless.

### 5. Prove, one line at a time

Proofs go in `PROOF.bend`, one `# ---- name ----` section per law, with a
`def Laws.<law>(...)` at the end.
- Induct on the argument the function recurses on.
- Each error's `expected:` is the next goal. Copy it into the `%rewrite : P` annotation.
- `%e : P` replaces `e`'s **right-hand side** with its left. Most failed rewrites are the wrong direction; wrap in `Equal.sym` or state the lemma the other way.
- `consumed more than once` means add `+` on that binder (parameter or pattern, e.g. `case 1n++j:`).
- An impossible case closes by rewriting into a `Tag` type, not by matching on an equation (proofs.md 1.4).
- A step that must recurse into its caller is inlined: two defs cannot call each other.

Facts about Base (`Nat` order, `min`/`max`, lists) go to **bend-mathlib**, the
submodule on branch `ours` -- look there first, and read `PUBLIC_API.lock`
beside the modules for the index. Only what mathlib cannot state goes to a
local facts file of your own; add a line to that file's gate with a false-fact
check that must be refused.

Check: `bend PROOF.bend --verdict` prints `ALL PROOFS CHECK` and exits 0, so the
proofs pass bend's checker and the BendTT kernel (proofs.md 1.1). An unsafe or
foreign def anywhere in the proof, imports included, turns that into
`SOME PROOFS FAIL` (exit 1). An unsafe def proves anything.

### 6. Give every law a mutant

In `check_mutants.ts`, import the harness from the `bend-falsify` package —
again, ask the user before you add it — and add one mutant per law: one line of `core.bend` changed so that the law becomes
false, the def its proof must fail in, and an `at` — the law's binders at small
literals. The tool reads the law's statement out of `LAWS.bend` and substitutes
them, so the counterexample is an instance of the law by construction rather
than a claim you asserted. Reach for `counter`, a claim of your own, only when
the law's shape is one `at` cannot state. Prefer a mutation in the real
function over one in the predicate. A law proved from other laws names their
sections in `with: [...]`.

Check: `bun check_mutants.ts`. Every instance holds on the core and fails on
the mutant, every control checks, and every mutant fails in the def named. A
mutant that fails in `core.<def>`, or with "consumed more than once", does not
compile. It is caught for the wrong reason, so make it compile first; a `+` on
a pattern binder is often enough.

### 7. Record what was learned

- A measured rule of the language goes in `references/language.md`, with the error and the measurement.
- A reversed rule is reversed loudly.
- Update the project README: layout, the law count, and what moved.

Check: the whole gate, and every other gate that uses a tool you changed. With
a JavaScript caller the last steps are in `references/js-host.md`; without one,
the gate ends at the mutants.

## What to report to the user

Report in the user's language, in plain terms:
- **each law**, and that it is proved;
- **what falsification caught before proving**;
- **any behaviour that changed** relative to the code being replaced, with the
  brute-force numbers, where there was code to replace;
- **anything found at real scale**;
- **gate results**.

Commit only when the whole workflow is done. Push only when the user asks.
