# Many agents, one judge: a pipeline for writing proved Bend

Bend's checker judges a proof in a fraction of a second, and a proof that
checks needs no one to trust the agent that wrote it. So the work of writing
a proved core can be split across many agents, as long as they hand work over
through files and verdicts of the checker, never through trust in each other.
This document is the design of that pipeline. `SKILL.md` has the working rules
it relies on, and `workflow.md` is the same workflow for a single agent.

The human's only job is to decide what "correct" means, by approving laws.
Everything else is done by agents and judged by the checker.

## The principle

- **Hand over files, not claims.** Each stage produces files the next stage reads: candidate laws, a falsification spec and its report, proof sections, a mutant table. An agent's summary of its own work is not an input to anything.
- **The checker is the judge.** A proof is accepted when `bend` accepts it, whoever wrote it. There is no review of proof code.
- **Freeze what has been approved.** Once the human approves the laws and the core's shape, they are fixed for the rest of the run. An agent that thinks either should change escalates; it does not edit.
- **Check the checkers.** A falsifier that never fails, or a mutant that does not compile, says nothing. Every judging step has a control that must fail.

## The stages

### 1. Propose (parallel)

Two or three proposers read the requirement or the existing code. Each looks
from one angle:
- exact characterisation (sound and complete)
- independence from irrelevant order
- monotonicity
- bounds
- agreement between two computations
- the helpers the other laws are written in terms of

Each proposer drafts candidate laws, every one with a line of plain language
and the reason it matters. They also list the edge cases the existing code
gets wrong or leaves undefined, as decisions for the human.

Output: candidate laws, and edge-case decisions.

### 2. Falsify and sketch (one agent, itself checked)

The falsifier writes a generator of literal instances for each candidate, and
runs it with the checker as the runner. Instances are built **around the
law's hypotheses** (for example, rules drawn from the request's own ids),
because uniformly random inputs rarely satisfy them.

Before its results count, the falsifier plants a bug in a copy of the core and
shows a counterexample. It also sketches the proof of the main laws (which
argument to induct on, which lemma each case needs), because the sketch can
show that the core should have a different shape. That has to happen before
approval, not after.

Output: the surviving laws, their counterexamples, and any proposed change of
shape.

### 3. Approve (the human, the only manual gate)

The human sees each law in plain language, the counterexamples, the
edge-case decisions and any change of shape, as a structured question. The
answer fixes:
- `LAWS.bend`, recorded by its hash
- the core's data shape

Laws the human does not approve are not stated.

### 4. Prove (a swarm)

Each approved law goes to several provers. Each prover works in its own git
worktree, with a different strategy hint: which argument to induct on, which
orientation to state a lemma in, which auxiliary fact to prove first. A
coordinator runs the checker on every attempt and merges the first section
that checks; the rest are discarded.

Rules for provers:
- **Do not edit the core or the laws.** A prover that believes the core's shape is wrong reports it, and the run escalates.
- **Do not prove general facts locally.** A fact about Base (`Nat` order, lists, `min` and `max`) is requested from the **facts agent**. It is proved once, in bend-mathlib (the submodule on branch `ours`); only what mathlib cannot state goes to a local facts file, under that file's gate and with a false-fact check. Every prover then reuses it.
- **Keep a budget.** After K failed attempts on one law, the run escalates. First an agent reads the last `expected:` goals and reports where it is stuck; then the choice is to restate a lemma, add a fact, or return the law to the human as too hard.

### 5. Mutate and feed back

The mutator changes the core one line at a time: flip a Bool, add or subtract
one, swap two arguments, replace a result with an empty value. It runs every
mutant against every law, and sorts each survivor into one of three kinds:
- **Equivalent:** it computes the same function (compare the two directly). Drop it.
- **Does not compile:** it was caught for the wrong reason. Fix the mutant.
- **A real gap:** behaviour no law constrains. It becomes a candidate law and goes back to stage 3.

Each law also gets one recorded mutant that must fail inside the law's own
proof (`check_mutants.ts`).

### 6. Integrate

Re-check equivalence with the function being replaced, if there is one, and run
the whole gate. With a JavaScript caller, `js-host.md` adds the module, the
bridge and the test at real scale (proofs cannot see stack depth or time), and
each of those tools needs the user's permission to add.

## The gate the coordinator enforces

These run on every merge and at the end, whatever an agent reports:
- `bend PROOF.bend` prints `All terms check.`, with no TODO and no line about relying on unsafe code. An unsafe definition proves anything.
- `LAWS.bend` has the hash the human approved.
- Every law has a mutant, every mutated core compiles, and every mutant fails in the law's own proof.
- The falsifier's control finds its planted bug.
- the local facts file's gate passes, including its false-fact checks.

## What exists and what is missing

The parts exist:
- **bend-falsify** (github `nohzafk/bend-falsify`): the falsifier's runner
  (`bunx bend-falsify <spec.ts>`), and the per-law mutant harness
  (`runMutants`), with `with` for laws proved from other laws and a `counter`
  for every mutant.
- **bend-emit** (github `nohzafk/bend-emit`): builds the typed module the
  bridge imports.
- `workflow.md`: the single-agent version of every stage.
- The gate scripts in each project.

Claude Code has the agent primitives the pipeline needs: subagents, git
worktree isolation, background runs, continuing an agent by message, and
remote sessions for fanning out. A check costs 0.1 to 0.3 s, so dozens of
provers do not make the checker the bottleneck. Tokens are the cost.

What is missing is the coordinator: the layer that hands out tasks, runs the
checker on what comes back, merges the winners, enforces the freezes and the
budgets, and escalates. Schedule it with a deterministic script, not an agent,
so that its decisions can be audited, and leave the agents the work that
needs judgement.
