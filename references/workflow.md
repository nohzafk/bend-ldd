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
  predicate whose rules the human approves as decisions, not as checks someone wrote in the
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

Each step below has a check you can run, and each check runs under a limit of
10 s of CPU, about 5 s of wall time (the `bend-check` wrapper in SKILL.md, and
the limits inside the falsifier and the mutant harness). Run the check before moving on. The checker answers in well
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

**Turn the list into decisions and put them to the human now, before any law
is drafted.** The human decides behaviour, not statements; most humans will
not read a law, and should not have to. A decision is:
- a **scenario** in the system's own terms — what happens, who sees it ("a
  second client asks the daemon to shut down while a turn is running");
- the **options**, each with what the user or caller would observe and what
  goes wrong if it is the other way;
- your **recommendation** first.

Every choice a law will encode is a decision here: what is refused and with
which reason, which of two reasons wins when both hold, what an unknown or
stale input gets, what happens after the end state. So is every premise that
leaves a real-world case outside a guarantee — say it as "in case X this is
not guaranteed". What stays yours: how many laws, how they are phrased and
split, which premises are technical (distinct ids from an allocator), the
proof shape.

The approved decisions, numbered, are the specification the laws are drafted
from. Give them to the drafter verbatim. A choice the drafter meets that no
decision covers comes back as a new decision; it is not settled inside a law.

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
- the validity predicate, from the validity rules the human decided;
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

### 4. Check the laws against the decisions — the human's step is the decisions

The human approved decisions in step 1 and will not read the laws, so the
question here is whether the laws say what was decided. Your own description of
the laws cannot answer it: you wrote them from the decisions and will read the
decisions back into them.

**When it is needed.** Falsification and mutants check the laws against the
core, never against the decisions: a law that drifted from a decision passes
both. Back-translate when any of these holds:
- a law has a premise (`for h: ...`) — a narrow premise drops real cases while
  the law still reads right;
- `LAWS.bend` defines helper predicates the statements rely on — the meaning
  lives there;
- a law covers several decisions, or a decision needs several laws together;
- a subagent drafted the laws and you have only read its report.

Skip it only when every law is a direct equation with no premise and no helper
("state X, event Y, answers Z") that maps one-to-one to a decision; compare them
yourself and say in the report that it was skipped and why.

**Back-translate blind.** Give a fresh agent (an `evidence`-style judge) only
`LAWS.bend` with every `# Guarantees:` / `# Why it matters:` line stripped, and
the core it imports — never the decisions, never your summary. Ask for, in plain
words: what each law guarantees and under which premises, and what the laws
together leave unguaranteed (inputs no premise covers, behaviours no law
constrains). Then compare, decision by decision:
- a decision no law guarantees → a missing or too-weak law; fix and repeat;
- a law guaranteeing something no decision says → the drafter decided it; take
  it to the human as a new decision, or drop the law;
- an "unguaranteed" the human would assume holds → a gap; a new decision.

Report to the human, not the law text:
- each decision, the law(s) that guarantee it, and whether the back-translation
  agreed;
- any new decision the drafting or the back-translation produced, put the way
  step 1 puts decisions;
- the evidence in one line: falsification hits per premise, mutants caught.

The law text is available on request; never require it. Ask about any design
choice the laws depend on ("does the core sort, or does the host?") and every
edge case from step 1 the old code got wrong or left open as decisions. The
human may drop decisions; state only the laws they need. Use a structured
question if one is available. **Write no proof until the decisions are approved
and the back-translation matches.** A proof of the wrong statement is
worthless.

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

### 6. Mutate the core, and record mutants only where they pay

A proof already covers every input, so a mutant does not look for bugs in the
code. Two uses, with different costs.

**Explore: find what no law pins.** While drafting, change the core by hand —
flip a Bool, add or subtract one, swap two arguments, return an empty value —
and run the falsifier against each change (`CORE=<file>`). A change that no law
notices is a missing law or an equivalent mutant; the human decides which.
This is the use that finds real gaps. Nothing is recorded; the survivors
become decisions and laws.

**Record: a witness that the law is not empty.** A recorded row shows an
instance where the law's premises hold and its conclusion is false on the
mutated core (checks 1 to 3). Once that holds, no proof of the law can check
on the mutant — the kernel is sound — so the proof's failure there adds only
where it failed (`failsIn`). What the row proves is that the law can be false
and depends on the line changed: it is not a tautology, and its conclusion is
not carried by its premises alone. One row per law is enough for that.

A recorded row runs on every gate, so record one only where emptiness is not
plain from the statement. Treat the core's defs as black boxes: a premise-free
equation is empty only if it holds whatever those defs compute. Record one row
when:
- the law has a premise (`for h: ...`), including a `!=` premise: the
  conclusion may follow from the premises without the core;
- the conclusion holds a predicate or projection of a core result to a
  constant (`{sorted(C.ordered(es)) == True{}}`): the law is empty if that
  predicate is constant;
- a side reaches the core through a def of `LAWS.bend` that itself calls the
  core (a reference machine such as `ref_step`): that def may unfold to the
  computation it is compared with;
- the conclusion has another shape (`exs`, a `!=` conclusion).

Record none for any other premise-free equation: the two sides are different
terms over black boxes, so changing a def's output falsifies it. That covers a
core application against a literal, a Base expression or a reference def that
does not call the core; two different core applications; and a predicate or
projection of a core result against a non-constant reference. `with` is not a
reason to record one — it is how the proof is organized, not a sign that the
law could be empty. A law another proof names in `with` needs no row of its
own, as long as its section is named after it (bend-falsify 0078305 and
later).

Two kinds of empty law a recorded row does not catch:
- a premise nothing satisfies: bend-falsify passes such a row with the note
  `(premise false on the core)`. Count premise hits in the falsifier and read
  them;
- a premise the proof never uses: the law is weaker than what was proved.
  Drop the premise, or ask the human whether the narrowing was a decision.

When you record one, in `check_mutants.ts`, import the harness from the `bend-falsify` package —
again, ask the user before you add it — and add the mutant: one line of `core.bend` changed so that the law becomes
false, the def its proof must fail in, and an `at` — the law's binders at small
literals. The tool reads the law's statement out of `LAWS.bend` and substitutes
them, so the counterexample is an instance of the law by construction rather
than a claim you asserted. Reach for `counter`, a claim of your own, only when
the law's shape is one `at` cannot state. Prefer a mutation in the real
function over one in the predicate. A law proved from other laws names their
sections in `with: [...]`, so its section is checked with theirs.

Pick the smallest literals that make the law false, not just small ones: the
instances checked on the unmutated core are batched into one bend run under
one CPU limit, so one heavy instance can push its batch past the limit and back
to one run per instance.

Check: `bun check_mutants.ts`. Every instance holds on the core and fails on
the mutant, every control checks, and every mutant fails in the def named
(`failsIn`; a shared lemma is acceptable). A
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
