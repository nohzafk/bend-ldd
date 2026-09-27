# bend-ldd — law-driven development in Bend 2

An agent skill for writing Bend 2 code that is **proved** rather than tested.

**[Bend](https://bend-lang.com)** is a dependently typed language whose checker
proves claims about *every* input, not the cases you thought to write down. A
**law** is one such claim, written in `LAWS.bend`. A **core** is the Bend file
that computes the answer. The skill's method is: state the laws, **falsify**
them (find an input that breaks one) before anyone approves them, prove them in
`PROOF.bend`, then **mutate** the core — break it on purpose — and check that
the law whose proof depended on that line now fails. The human decides what
"correct" means; the agent writes the code and the proofs; the checker decides.

## Install

```sh
npx skills add nohzafk/bend-ldd
```

`bend` is the one prerequisite; `bend guide` says how to install it, and it
comes with its own language reference. `bun` is the other thing worth having.

## The gate

Run before committing. `bend PROOF.bend`, through a wrapper that kills it at
5 s, prints `ALL PROOFS CHECK` and exits 0 (a TODO or any unsafe or
foreign code gives `SOME PROOFS FAIL`, exit 1). Every law has a mutant that fails inside that law's own proof.

The 5 s limit is this skill's, not the language's. On a core shaped for proof
the checker answers in a fraction of a second, so a check that runs into
seconds is a signal rather than a price: usually a large constant the checker
has to walk, a fuel loop unfolded into a goal, or application code run inside
one. Change the statement or the shape of the core; do not raise the limit.
`SKILL.md` has the wrapper.

## The tools

`bend` and `bun` are all you need to start. The rest are reached when the work
asks for one, and installing one is your call: ask before you add a dependency
to somebody's project.

| tool | what it is | reach for it when |
| --- | --- | --- |
| [`lawcheck`](https://github.com/bendlib/bendlib) | generates instances and mutants, and runs them through the checker | falsifying a law or mutating a core. Needs no spec file |
| [`bend-falsify`](https://github.com/nohzafk/bend-falsify) | takes instances and mutants you wrote, and ties each to the proof it should break | lawcheck skipped a law, or a mutant has to fail in a *specific* proof |
| [`bend-emit`](https://github.com/nohzafk/bend-emit) | builds the typed JavaScript module from a core | a JavaScript program is the caller |
| [`bend-schema`](https://github.com/nohzafk/bend-schema) | the codec and schemas where host values cross into Bend types | a JavaScript program is the caller |

## What is in it

`SKILL.md` is the method, and its map says when to read each file.
`references/language.md` has the rules of a def and the runtime. 
`references/proofs.md` has writing a proof, the half of Bend that `bend guide`
does not cover. `references/workflow.md` is the whole workflow in order, and
`references/js-host.md` and `references/multi-agent.md` are for a JavaScript
caller and for many agents at once.

## License

MIT.
