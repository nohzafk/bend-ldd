# The method in full

SKILL.md keeps one short paragraph per section below; this file holds each
in full. Read the section when SKILL.md's summary is not enough.

## Where Bend belongs

Put in Bend the part that is **small, pure, decides something, and is costly
when wrong**: matching, scheduling, allocation, billing and quota rules,
dependency resolution, a protocol's state machine. Keep in the host what the
checker cannot reach or the ecosystem lacks: IO, HTTP, time zones, parsing, npm
packages.

- **The host owns the program, the core is a library — the default.** The host
  owns IO and libraries and calls the pure core as a function;
  values cross in memory, no JSON is parsed in Bend, no effects to write.
- **Bend hosts, the host language is reached through effects** — only when the
  control loop is itself what must be proved, or the program needs the native C
  lane or the GPU.
- **An effect is for the outside world** — time, IO, state, randomness — **not
  for a library Bend lacks.** Compute in the host and hand the core plain data:
  an effect turns a pure computation into text in `IO`, where no law can reach
  it.
- **One schema owns the boundary: the core's Bend types.** Generate the host's
  types from them, so neither language can invent a field name and a rename in
  the core fails the host's typecheck.
- **The host's values cross through the schema boundary.** A universal codec
  turns any host value into a `Raw` without knowing a schema; the core checks it
  against a schema written in Bend, whose check is proved once for every schema,
  and words the first error with its path. The host rejects only what cannot
  become a Bend value at all.
- **The core accepts any input and reports the first error**, so validation is
  part of the specification and is proved, not hidden in the bridge's `if`s.
  `references/workflow.md` has the two layers and the four laws they need.
- **The core has no effects**, so its laws can import it.

## Use the checker's speed

The checker answers in well under a second — a 360-line proof file checks in
0.08 s, a mutant run with its scratch copy in about 65 ms — and Bend has no
tactics: nothing inside it searches for a proof. So the search moves outside it,
to agents, and the checker becomes the judge they run against, many times a
minute.

- **Falsify before you prove.** A candidate law instantiated at literals closes
  by `{==}` when it holds there, and fails naming the instance (`Location: c3`)
  and its two sides (`expected : 1n / observed : 0n`) when it does not. Check a
  few dozen small inputs — empty lists, zero, equal bounds, one element — as
  `def c1() -> {lhs(lit) == rhs(lit) : T}: {==}` in a scratch file, or through
  lawcheck. That is property-based testing with the checker as the runner and no
  framework to write; the checker stops at the first failing instance, so one
  run reports one counterexample. Keep the inputs small: a numeral it has to
  walk down is slow, and a large one overflows it.
- **Measure what the laws leave unconstrained.** Mutate every line of the core —
  flip a Bool, add or subtract one, swap two arguments, replace a result with
  `Nil{}` or `0n` — and check each mutant against all the laws. A survivor is
  behaviour no law pins down: either a law is missing, or it genuinely does not
  matter, and the human decides which. `lawcheck mutate` does this mechanically;
  a survivor can also be an equivalent mutant, so compare the two functions
  before calling it a gap. This does not say what the program *should* do; it
  says where nothing has been said yet.
- **Many agents, one judge.** Some propose invariants, some falsify them, the
  human approves the survivors, a swarm proves each law, and some mutate the
  core to find what no law constrains. The pipeline, with its stages, freezes,
  budgets and gate, is in `references/multi-agent.md`. The human reads laws, not
  code.

**Five seconds is the limit**, in the wrapper above and inside lawcheck and
bend-falsify. On a core shaped for proof the checker answers in a fraction of a
second, so checking after every edit costs nothing; a check that runs into
seconds is a signal rather than a price. A check past 5 s is not slow, it is
wrong: a large constant the checker walks (proofs.md 1.3), a fuel loop unfolded
into a goal, application code in a goal. Do not raise the limit — change the
statement or the shape of the
core. The speed has a precondition, **short goals**: a goal that unfolds a big
fuel overflows the checker, and a loop unfolded into its goal runs to thousands
of characters. Search one proof line at a time, because each error's `expected:`
is the next goal.

## How to prove things about a core

1. **State the law first, and spend the time there.** Once a statement is right
   the proof is usually mechanical; a rejected proof is more often a wrong
   statement than a hard one. Check the statements alone (`bend LAWS.bend`
   reports one TODO per law), and falsify each on concrete inputs, before
   writing any proof.
2. **A law quantifies over all inputs.** A law whose inputs are literals is
   closed by `{==}` — the checker runs the code — and that is a unit test
   wearing a proof. Keep examples as runtime tests. A law that only restates a
   definition is worth keeping when it guards a mistake someone has made before.
3. **Finding the invariants is a design review.** Ask what the core must
   guarantee, then write each as a law. The gaps found while looking are
   specification bugs, and they are found no other way.
4. **The specification is a small predicate, and the proofs are relative to
   it.** If the predicate is wrong, the proof proves the wrong thing. Keep it
   short enough to check by reading, then prove what it means, so its name is
   not the only evidence.
5. **The statement shapes how you think.** Say "x is in xs" as a witness split
   (`xs == pre ++ (x <> post)`), not a membership test: it says where `x` is,
   and it never compares two abstract values, which does not reduce. Say
   `a <= b` as `b == a + k`. Say "there is a window that contains it" as a
   dependent pair that names the window. Equations rewrite freely; Bools do not.
6. **Shape the program for the proof — it usually gets simpler.** A decision a
   proof must follow goes to a def as a **parameter** (`keep(x, rest, ok)`), so
   the proof can split on it. When the number of steps can be computed, recurse
   on the count, not on a fuel. Build a list by recursion on its source, so a
   law can say its order is the source's order.
7. **Every law needs a version of the core where it is false, and the proof must
   fail there.** A proof that checks in 0.07 s may be saying nothing. Mutate the
   core so the law no longer holds — not merely so the proof stops parsing — and
   require the proof to fail *inside its own lemmas*; check the unmutated copy
   from the same place. Isolate one law's proof per run, because the checker
   stops at the first failing def. bend-falsify's `runMutants` is the harness,
   with a table of mutants each naming the law's binders at literals (`at`).
   This runs from the laws to the code; measuring what the laws leave
   unconstrained runs the other way. A project needs both.
8. **Accumulate what you learn.** A fact about Base goes to **mathlib**: add the
   law there, keep `PUBLIC_API.lock` in step, push the fork. What mathlib cannot
   state goes to a local facts file whose gate must also refuse a false fact. A
   measured rule of the language goes to `references/language.md` with the error
   that taught it, written so it holds outside the program that found it. When a
   rule there turns out wrong, **reverse it loudly**: say it was reversed, what
   replaced it, and the control that shows the new claim is not too strong.

The gate for a Bend project is `bend PROOF.bend`, plus the mutant check. Run
both before committing. Parallelize the code whenever possible.

