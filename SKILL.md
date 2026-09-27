---
name: bend-ldd
description: Law-driven development for Bend 2 — state the laws, falsify them, get them approved, prove them, then mutate the core to find what no law pins down. Use when writing a Bend core, porting a function into one, or reviewing Bend code; drafting or approving laws in LAWS.bend; writing PROOF.bend; running bend, lawcheck or bend-falsify; adding a Bend mutant; finding the input that breaks a function; or bringing a function under proof that has to be right for every input.
---

# Law-driven development in Bend

**Bend is designed to be written by agents.** Its guide says so in its first
paragraph: it gives humans "an ambiguity-free language to communicate their
intents to AIs", and a compiler "capable of mechanically checking that the AI
implemented these intents". Its convention is *law-driven development*: the laws
in `LAWS.bend` state what the program must do, the agent writes the code and
`PROOF.bend`, and `bend PROOF.bend` is the gate. Four things follow:

- **Verbosity is not a cost.** One def per `match`, a helper per inspected
  value, no forward references. Tedious for a person, free for an agent, and it
  leaves little room for an ambiguous program.
- **The checker is the reviewer.** A proof that checks needs no one to trust the
  agent that wrote it. Spend review time on the laws, not on the code.
- **The agent drafts the laws; the human approves them.** The guide has the
  human write `LAWS.bend` and the agent never touch it. Here the agent may
  propose laws — finding the invariants is part of the work — but each is shown
  to the human with the reason it matters, and no proof is written against it
  until the human approves it.
- **The checker is fast** — a proof file checks in a fraction of a second — so
  check after every step, not at the end, and let the error's `expected:` goal
  drive the next edit.

A Bend program is a proved core inside a host, and the line between them is IO,
not importance. Everything pure can move into the core, starting where a wrong
answer costs the most. The core is where Bend earns its cost: the checker proves
claims about **every** input, which no type system and no test suite does.

Before writing any Bend: run `bend guide`; read the four rules and three
principles below, and the map at the end of this file for what to read next (when the checker refuses a form, look up the rule before
working around it — it is usually refusing a shape that cannot be compiled, not
a bug); read `~/.bend/bend2/base.bend`, the standard library and a working
example of every rule; and look in **mathlib** before proving a fact about
`Nat`, `String`, `List`, `Bool` or comparison, since it is very likely already
there (`PUBLIC_API.lock` beside the modules is the index).

## The four rules you meet first

Each costs one failed build the first time. The error is what you will see; the
reason is in the section named.

| rule | the error | the fix | why |
| --- | --- | --- | --- |
| **A value used twice is marked `+`.** Parameters, pattern bindings (`case 1n++k:`, `case +h <> +t:`, `case (+pre, +w, ...)`), do-block bindings, and a law's binders — never a proof def's parameters. Type annotations inside the body count as uses. | `expected : x / observed : x (consumed more than once)` | add `+` where `x` is bound; for a proof, on the law's `for` | language.md 1.3 |
| **One `match` per def, at its head, on a parameter.** No match inside a case arm, no match on a computed value — a pair destructuring `(a, b) = f(x)` is a match too. | `a match cannot scrutinize a computed value: give it its own def` | give the value its own def, where it is a parameter; inspect several things at once with `match a b:` | language.md 1.1 |
| **A def comes before its use.** No forward call, so no mutual recursion. Datatypes are exempt: they may name each other in any order. | `expected : a filled definition (an unfilled law is a dead claim: live code cannot use it)` | order defs by dependency; when a step needs the recursive result, pass it in as a function argument (`ih: A -> B`) | language.md 1.2 |
| **A rewrite has a direction.** `%e : P` replaces an occurrence of `e`'s **right-hand side** with its left-hand side, at the `_` in `P`. `P` is the goal as it stands, `_` at exactly the subterm to replace. | `expected : {...} / observed : {...}` side by side | copy `expected:` into `P`; if the form to remove is on `e`'s left, state the lemma the other way (`Equal.sym`, or keep both orientations) | proofs.md 1.2 |

## Three principles

Almost every rule in `references/language.md` follows from one of these. Learn the
principles and the rules can be derived; meet the rules one at a time and they
read as friction. With the reasons, most rules are the language telling you what
it compiles to.

| principle | the rules it produces |
| --- | --- |
| `match` compiles to a tree of lambda-matches, and a lambda-match applied to a value is a banned form | the scrutinee is a parameter, one match heads a def, a match is not a term, no computed or let-bound scrutinee, a computed Bool goes to a def that takes it as a parameter |
| safe defs form a DAG, and recursion is self-recursion that decreases | no forward call, no mutual recursion, a helper cannot call its caller, a loop carries a shrinking first argument |
| quantity lives in the type (`Type` is `Kind(&1)`, `Data` is `Kind(&2)`) | `+` requires `Data`, a handle cannot be marked and must be threaded back out of its effect, angle brackets are for declared datatypes |

When one of these refuses you, suspect the shape, not the checker: it is
refusing a form that cannot be compiled.

## Think in invariants

A proof is mechanical once its statement is right. The statement is where the
design happens, and a proof protects exactly what its law states and nothing
more. Tests ask "does it work on these examples?"; laws ask "what must be true
of every answer?".

Ask each of these of every core:

- **Exact characterisation.** Exactly the right set: sound *and* complete. A filter that returns nothing is sound.
- **Agreement with an obvious specification.** A slow, obviously correct way to compute the same thing; the fast code must equal it.
- **Independence from what should not matter.** Order of inputs, batching, repetition (idempotence), how a merge is grouped (associativity, commutativity).
- **Monotonicity.** More input never costs less; one more constraint only removes answers; adding a grant never takes access away.
- **Preservation.** Sorted stays sorted, separated stays separated, totals are conserved.
- **Round trips.** `decode(encode(x)) == x`.
- **Bounds** on every output.
- **The helpers.** A law written in terms of a helper says nothing about bugs inside it, so pin the helpers too.

Ask what wrong implementation would still satisfy a law: if `return 0` or
`return []` would, the laws are incomplete. A counterexample to a draft law, or
a question no law answers, is a decision nobody had made — whether touching
windows are joined, whether an anonymous requester is covered by "any role",
what a plan charges past its last tier. Take each one to the human; an
implementation answers them by accident, and nobody knows a choice was made.
Write every law so a person can read it, with one line of plain language saying
what it guarantees and why it matters, because the human approves the
invariants, not the code.

## Where Bend belongs

Put in Bend the part that is **small, pure, decides something, and is costly
when wrong**; keep IO, HTTP, time zones, parsing and npm in the host. The core
accepts any input, reports the first error, and has no effects. The full rules:
`references/method.md` § Where Bend belongs.

One file in this skill is about a host, and only one: `references/js-host.md`,
for a JavaScript caller. Everything else, the whole workflow included, is
complete without one — a core with no caller is a normal thing to prove.

## The pieces, by role

- **The checker** is `bend`. The gate is `bend PROOF.bend` printing `All terms
  check.`, with no TODO and no line about relying on unsafe or foreign code. Wrap
  every check in a 5 s timeout, and keep the wrapper beside the project:

  ```sh
  #!/bin/sh
  # bend-check <file.bend> [args]: the checker under a 5 s limit. A check past
  # 5 s is a problem to fix, not a limit to raise -- a large constant the
  # checker walks (proofs.md 1.3), a fuel loop unfolded into a goal (proofs.md
  # 1.7), or application code run inside a goal (proofs.md 1.5). Rethink the statement or the
  # shape of the core.
  # macOS ships no `timeout`; coreutils provides it as `gtimeout`. Refuse to run
  # unchecked rather than pretend the limit is there.
  LIMIT=5
  TO=timeout; command -v timeout >/dev/null || TO=gtimeout
  if ! command -v "$TO" >/dev/null; then
    echo "bend-check: no timeout or gtimeout on PATH; install coreutils" >&2
    exit 127
  fi
  "$TO" "$LIMIT" bend "$@"
  rc=$?
  [ "$rc" = 124 ] && echo "bend-check: ran past $LIMIT s on: $*" >&2
  exit "$rc"
  ```
- **The standard library** is `~/.bend/bend2/base.bend`, and it ships facts you
  can import instead of proving.
- **mathlib** is bendlib's `bend-mathlib` package, pulled in as a git submodule
  at `vendor/bendlib` and imported by relative path **from `PROOF.bend`
  files only** — never let a
  `core.bend` import it; only a proof, a probe or a canary may. **Never publish
  a mathlib fact to the Bend hub:** a publication cannot be updated, so a wrong
  or superseded fact is stuck there for good. A fact mathlib cannot state goes
  to a small local facts file of your own, whose gate must also refuse a false
  fact.
- **lawcheck** is bendlib's `tools/lawcheck`. It generates literal instances and
  small mutants and runs them through the checker. Reach for it first. Add
  bendlib as a git submodule at `vendor/bendlib` and set
  `LAWCHECK=vendor/bendlib/tools/lawcheck/cli.ts`. The path is relative to the
  project, not to a bendlib checkout.
- **bend-falsify** is [github nohzafk/bend-falsify](https://github.com/nohzafk/bend-falsify).
  Its README is the spec — read it there; do not rely on a copy of it.
- **bend-emit** and **bend-schema** exist only for a JavaScript caller. Both
  are described in `references/js-host.md`; nothing above needs them.

Only `bend` and `bun` are required. Each tool above is reached when the step
needs it, and **installing one is the user's call: ask before you add a
dependency to their project.**

## Tool strategy: lawcheck first, bend-falsify for what it skips

**Run lawcheck on every law before you prove it.** It is the mechanical
falsifier and mutator, it needs no spec file, and it shrinks what it finds.

```sh
LAWCHECK=vendor/bendlib/tools/lawcheck/cli.ts

bun "$LAWCHECK" LAWS.bend --timeout 5000           # every law, open or proved
bun "$LAWCHECK" LAWS.bend --law ins_sorted          # one law
bun "$LAWCHECK" LAWS.bend --strict                  # a `~` becomes a failure
bun "$LAWCHECK" mutate LAWS.bend --timeout 5000     # small mutants
```

A `✓` means no counterexample turned up among the instances it tried; it proves
nothing. A `✗` is a counterexample: the law is false as stated, so fix the
statement before proving it. A `~` is a law it could not decide, with the
reason, and an `!` is one that errored. It exits 0 when nothing failed, 1 when
a law failed or a mutant survived, 2 on a usage error, so a `test.sh` can gate
on the exit code. `--strict` turns a `~` into a failure, which is the reading
this method wants: an undecided law is not a proved law.

`mutate` infers its target: it mutates the implementation the laws file
imports when that file imports exactly one module and defines nothing itself,
and otherwise its own defs. Pass `--impl <core.bend>` rather than rely on it. **lawcheck does
not reach every law:** on bend-schema it evaluates 4 of 22, and the other 18 are
skipped — 16 for a function-typed template binder (`no catalog functions for
~rule: …`) and 2 because the claim uses a premise's proof term. Go to
**bend-falsify** for those, and for tying a mutant to a law's own proof:

- **a function-typed binder** — lawcheck instantiates `~f` only from a small
  catalog of closed lambdas, and skips a signature outside it. A hand-written
  spec supplies the instances.
- **a witness-type claim** — an `exs`, or a claim that is neither an equation
  nor a single predicate application. Write the instance.
- **a claim that uses a premise's proof term** — lawcheck drops the premise and
  cannot decide the claim. Write the counterexample.

The 5 s rule is this skill's, and neither tool applies it by itself:
bend-falsify enforces it, and lawcheck defaults to 120 s unless given
`--timeout 5000`, which is why the commands above pass it. A check past the
limit is a problem in the Bend, never a limit to raise. **A mutant row names the law's binders at literals
with `at`** — the tool reads the law's statement out of `LAWS.bend` and
substitutes. Reach for `counter`, a claim of your own, only when the law's shape
is one `at` cannot state.

**Three report notes are gaps a human reviews, not passes:**

- `(counter not tied to the law)` — the counterexample is yours, so nothing
  checks that it is an instance of that law. A `counter` row is weaker than an
  `at` row.
- `(fails in a shared lemma, not the law's own section)` — the mutant broke a
  lemma every run keeps, so it does not tell this law's mutant from another's.
  Prefer a mutation that breaks inside the law's own section; when none exists,
  the note is the honest record.
- `(premise false on the core)` — the mutant's counterexample does not even
  satisfy the law's premises on the unmutated core, so the row says nothing
  about the law.

Read bend-falsify's README for the spec format, `runMutants`, the table fields,
and the rest of the report. It is the source of truth for that tool.

## Use the checker's speed

The checker answers in well under a second and Bend has no tactics, so the
search moves to agents and the checker judges. **Falsify before you prove**
(literal instances, or lawcheck). **Measure what the laws leave unconstrained**
(mutate the core; a survivor is a missing law or an equivalent mutant).
**Five seconds is the limit**: a check past 5 s is wrong, not slow; change the
statement or the core, never the limit. Details: `references/method.md` § Use
the checker's speed.

## How to prove things about a core

1. State the law first and falsify it before any proof.
2. A law quantifies over all inputs; a law at literals is a unit test.
3. Finding the invariants is a design review.
4. The specification is a small predicate; prove what it means.
5. State membership as a witness split, `a <= b` as `b == a + k`.
6. Shape the program for the proof: decisions as parameters, recurse on counts.
7. Every law needs a mutant where it is false, and its proof must fail there.
8. Accumulate: Base facts to mathlib, language rules to `references/language.md`.
   A fact that goes upstream goes to [bendlib](https://github.com/bendlib/bendlib)
   as its own branch off upstream `main`; a fact you keep goes to the submodule
   at `vendor/bendlib`. Never force-push a branch a submodule pins.

Each rule in full: `references/method.md` § How to prove things about a core.
The gate is `bend PROOF.bend` plus the mutant check; run both before committing.

## Map — what to read, and when

| read | when |
| --- | --- |
| **`bend guide`** | first, always: it owns the syntax and the types, and it ships with the compiler, so this skill does not repeat them |
| `~/.bend/bend2/base.bend` | whenever you need a form, or a fact you would otherwise prove |
| **`references/language.md`** | when the checker refuses a form: one rule per failure, grouped under the principle it comes from, then the effects and the runtime, then what the language is and is not for |
| **`references/proofs.md`** | when you state or write a law: the gate, the rewrite, what computes, how to state, how to test the proofs |
| **`references/workflow.md`** | when bringing one function under proof: the workflow in order, with the check to run at each step, and the two layers a core has |
| **`references/js-host.md`** | only when a JavaScript program is the caller: the project layout, the module build, the bridge, and the test at real scale |
| **`references/method.md`** | when a SKILL.md section's summary is not enough: where Bend belongs, the checker's speed, the eight proof rules in full |
| **`references/multi-agent.md`** | when splitting the work across agents: stages, freezes, budgets, and the gate a coordinator enforces |
| [bend-falsify's README](https://github.com/nohzafk/bend-falsify) | the spec format, the mutant table fields, and every report line |

`references/language.md` and `references/proofs.md` are language experience only:
every rule there was paid for by a failed build, and the failure is quoted next
to it. Neither repeats a compiler version, and `bend guide` is the authority for
anything they do not cover.
