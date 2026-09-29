# proofs.md — writing Bend proofs

What writing a proof actually costs, and where the time goes. Every rule here
was paid for by a failed build, with the failure quoted beside it. Read
`bend guide` and `references/language.md` first: this file is the half of
writing Bend that the guide does not cover.

A proof that checks needs no one to trust whoever wrote it. That is the whole
reason to write one.

Where the time goes: of the builds that fail while writing proofs, almost none
is a proof step the checker rejects. They fail on a wrong belief about Base, on
the annotation form of `%` (writing the post-rewrite goal instead of the hole,
or putting the hole too high), on affinity, and on a path-qualified lemma name.
The failures that are *about mathematics* are structural: the statement was
shaped wrong (1.5), or the induction was on the wrong argument (1.6). Once the
statement is right, the rewriting itself is cheap.

## 1.1 Layout and the gate

```sh
bend PROOF.bend --verdict  # ALL PROOFS CHECK                  -> exit 0   (the gate)
bend PROOF.bend            # the same, bend's own checker only
bend LAWS.bend             # SOME PROOFS FAIL / 2 TODOs found. -> exit 1   (one per unproved law)
```

- **The gate is `--verdict`.** Plain `bend PROOF.bend` trusts one checker,
  `bend.ts`, a few thousand lines of TypeScript with no proof. `--verdict`
  runs it, then elaborates every def and type outside Base to BendTT and has
  a second checker, the kernel in `bend2/bendtt.lean`, check that text. The
  kernel's soundness argument is proved in Lean, so a pass rests on the
  kernel and the elaborator, not on `bend.ts`.
- **What `--verdict` can say.** `ALL PROOFS CHECK`; the unsafe error below; or
  a *mismatch*: bend's checker accepted what the kernel rejects. A mismatch
  is not a wrong proof -- it is a bug in bend's checker or a construct the
  elaborator cannot yet express, and bend asks for an issue. A def the
  elaborator cannot translate fails the verdict too; nothing is skipped.
- **It needs Lean once per bend release.** The first run builds the kernel
  with the elan toolchain bend names in its error (`leanprover/lean4:v4.x`,
  found under `~/.elan/toolchains/`, or `$BENDTT` set to a built kernel) and
  caches it in `~/.bend/bendtt/<hash>`. Measured on csv-lib: the build ~15 s, then
  0.14 s for the plain check against 0.24 s under `--verdict`. Build
  it outside a time-limited wrapper, then gate the proof file inside one.
- **Control it.** `BENDTT=/usr/bin/false bend PROOF.bend --verdict` must give
  the mismatch: that shows the kernel ran.
- **Mutants stay on the plain check.** A mutant has to break a proof in bend's
  checker; the kernel adds nothing there and costs a translation per run.

- `LAWS.bend` states the claims and imports the code; `PROOF.bend` imports
  `LAWS.bend` as `Laws` and proves them; `bend PROOF.bend --verdict` is the gate. A proof
  is a def named after its law: `law fee_monotone` in `LAWS.bend`
  is proved by `def Laws.fee_monotone(n, more, p): ...` in `PROOF.bend`. A law file cannot import a
  module that uses
  effects, so a core with laws is pure.
- `law X` with no `def X` is a TODO, and the count in the message is the
  number of unproved laws. **The exit code is reliable** -- measured, not
  assumed: `bend` exits 1 on a type error and on TODOs, 0 when everything
  checks. `@unsafe` (or `def f?`) skips the *termination*
  check; it is not a way to silence a TODO.
- **An unsafe def proves anything; the gate refuses it.** Three
  defs, one call:

  ```bend
  def lie?() -> {0n == 1n : Nat}:
    lie()
  def claim() -> {0n == 1n : Nat}:
    lie()
  # SOME PROOFS FAIL
  # Error: 2 defs rely on unsafe or foreign code:
  # - lie
  # - claim
  # exit 1
  ```

  A self-call that never shrinks is not checked, so the def type-checks at any
  type, a false equation included, and `def f?` makes it one character. The
  checker refuses it through imports too, and `--verdict` refuses it as well. Gate on exit 0 and `ALL PROOFS CHECK`
  (`ALL PROOFS CHECK` goes to stdout, a failure verdict to stderr, so capture `2>&1`); the `rely on unsafe` line names
  every def whose proof passes through the unsafe one. A project frozen on an
  older bend printed `All terms check, but ...` with exit 0 here, so its gate
  cannot be trusted for this.
- **A proof's parameters carry no annotation and no mark.** The law supplies
  the types: `def Laws.x(slot):`, not `def Laws.x(slot: C.Iv):` -- annotating
  is refused (`expected : a name, observed : ':'`), and so is marking
  (`expected : ':', observed : ','`). The reuse mark goes on the law's binder:

  ```bend
  law chain_symbolic:
    for +a: String          # the proof mentions a twice, so mark it here
    for +b: String
    {R.run(200n, ...) == ... : R.RRes}

  def Laws.chain_symbolic(a, b):  # no marks, no annotations
    %C.string_eq_refl(a) : {...}
    %C.string_eq_refl(a) : {...}
    {==}
  ```

  Forgetting it gives `expected : a / observed : a (consumed more than once)`,
  pointing at the def -- which reads as if the parameter should be marked, and
  it should, one level up.
- **A condition is a law binder**, and the proof rewrites with it. It is not an
  axiom: a caller that cannot produce it cannot use the theorem. Mark it `+`
  when the proof uses it more than once (else
  `expected : hab / observed : hab (consumed more than once)`); Base does the
  same for its own hypotheses (`law Equal.cong` binds `for  e: {a == b : A}`):

  ```bend
  law chain3_symbolic:
    for +a: String
    for +b: String
    for +c: String
    for +hab: {False{} == String.eq(a, b) : Bool}   # the condition
    {R.run(200n, ...) == ... : R.RRes}

  def Laws.chain3_symbolic(a, b, c, hab):
    %hab : {... _ ...}          # rewrites String.eq(a, b) to False{}
    ...
  ```

- **Another project's proofs can be imported for their lemmas.** A
  `PROOF.bend` that imports `../lib/PROOF.bend as SP` can call
  `SP.exact(s, r, None{})`; the imported file's laws are all filled, so it
  brings no open claim. A law file, whose claims are
  open, still cannot be imported for its facts.
- **A fact meant for reuse is a def whose return type is an equation**, not a
  law. A law file cannot be *imported* for its facts -- importing `LAWS.bend`
  elsewhere brings open claims. Type checking is the proof, an `import` gives
  every caller the lemma, and `%C.string_eq_refl(a)` fires in the importing
  file:

  ```bend
  def string_eq_refl(s: String) -> {True{} == String.eq(s, s) : Bool}:
    %string_cmp_refl(s) : {True{} == String.eq.fin(_) : Bool}
    {==}
  ```

## 1.2 `%lem(args) : P` — the rewrite, exactly

One line in a proof is a rewrite. The semantics, reverse-engineered and then
confirmed against every example in Base:

- It replaces an occurrence in the **goal** of the lemma's **right-hand side**
  with the lemma's **left-hand side**. So a useful lemma is written
  `{form-I-want == form-that-is-there}`: the form being eliminated goes on the
  right.
- `P` is the goal **as it stands**, with `_` at *exactly the subterm being
  rewritten*. Not the whole argument, not the post-rewrite goal -- the subterm.
  After an earlier rewrite, that subterm may sit on the other side of the
  equation from where you expect.
- **`P` need not be the goal's normal form: write the terms the program built.**
  The checker compares `P(b)` with the goal up to computation, so the annotation may
  name a term the program constructs -- `unit(a, "x")` -- instead of the 900-character
  normal form the printer shows. Issue #964 was closed on exactly this, its reproducer
  checking with a one-line motive: `%eq_refl(unit(a, "x")) : {True{} == go(7n,
  Hold{_, String.append(unit(a, "x"), ","), unit(a, "x")}) : Bool}`. This is what makes
  a proof over a program that builds data writable by hand at all; without it the
  annotation restates the built term on every rewrite line.
  `references/examples/issue964.bend` is the file, and it checks with no unsafe note.
- **`_` is for a proof's motive, never for a type.** The hole marks the occurrence
  being replaced, so it belongs in the annotation after `%`; a law or a def's return
  type carrying `_` is refused with `expected : a defined name / observed : _`.
- The error prints the goal the way the checker sees it, already reduced:

  ```
  - expected : {Nat.is_le(rp, Nat.add(mp, 1n+Nat.add(rp, 1n))) == True{} : Bool}
  - observed : {... what your annotation said ...}
  ```

  `expected:` is the current goal. **Copy its shape into the annotation** -- it
  is the cheapest way to learn what the goal is after a case split.
- **Orientation is a choice you make when you state a hypothesis or lemma.**
  `h : {Nat.add(a, k) == b : Nat}` eliminates `b`; written
  `{b == Nat.add(a, k)}` it eliminates `add(a, k)` instead. A lemma meant to
  turn a comparison into its answer is stated `{True{} == String.eq(s, s)}`;
  the other orientation is a valid theorem that will not fire. Keep both
  orientations of a load-bearing lemma (`add_assoc` and
  `add_assoc_r`), or flip one inline with `Equal.sym`. The flip as a term is
  `Equal.sym(A, a, b, h)` for `h : {a == b}`, and its type is `{b == a}`, so as
  a rewrite it eliminates its **first** argument: a hypothesis bound as
  `hlf : {U32.is_eq(x, 10) == False{} : Bool}` eliminates `False{}`, and
  `%Equal.sym(Bool, U32.is_eq(x, 10), False{}, hlf)` eliminates
  `U32.is_eq(x, 10)` instead. Every generated `_sym` twin in mathlib is that
  call, which is why they read backwards (`reverse_go_spec_sym(s, acc)` is
  `Equal.sym(String, String.reverse.go(s, acc), String.append(String.reverse(s),
  acc), reverse_go_spec(s, acc))`). Getting this the
  wrong way round is the most common cause of a rejected line, and it is never
  the checker's fault.
- **A library lemma's orientation is its `law` line, not the def beside it.**
  mathlib writes each load-bearing fact twice: `law reverse_go_spec` is
  `{String.reverse.go(s, acc) == String.append(String.reverse(s), acc)}`, while
  `internal_reverse_go_spec` -- the def a few lines above it -- is the same
  equation the other way round, and `reverse_go_spec_sym` is the flip again
  (`_sym` is the convention's name for it). Reading the internal def or its
  comment and assuming the public orientation follows costs a rejected line in a
  file that looks right; one `grep -A4 '^law reverse_go_spec:'` before writing
  the rewrite says which form fires.
- **Every `_` in `P` is the same hole.** One rewrite replaces as many
  occurrences as `P` marks, so an affine hypothesis that must replace a
  variable in four places is used once:
  `%e : {Nat.is_le(1n+np, Nat.div(a, 1n+_)) == Nat.is_le(1n+Nat.add(_, Nat.mul(np, 1n+_)), a) : Bool}`
  (`div_le_small`).
- **Orientation is part of the term.** `String.cmp(x, y)` and
  `String.cmp(y, x)` are different terms, so a hypothesis
  `{False{} == String.eq(a, b)}` will not fire on a goal holding
  `String.eq(b, a)` -- which is what makes such theorems worth having. A
  hypothesis may be written in a law's surface form (`String.eq(a, b)`) and
  still fire on the normalized goal (`String.eq.fin(String.cmp(a, b))`): the
  two are the same term.
- **Two defs with the same body are two terms.** The checker's normal form
  keeps a def's head when its body cannot reduce (1.3), and a def that matches
  an abstract argument is stuck, so `esc_rev.push(q, c, acc)` and
  `esc_char(q, c, acc)` -- the same arms under two names -- stay distinct in it.
  A lemma stated with one never fires on a goal holding the other, and no
  annotation repairs it. That is a reason to shape a core rather than work
  around it: where two lanes need one step, call one def (`esc_rev` was
  rewritten to call `esc_char`, which also deleted a helper).
- **A constructor hides the hole, so lift the equation out of it.** A rewrite
  replaces a goal's occurrence of a lemma's right-hand side, and an occurrence
  inside a constructor is not one it reaches. The shape that bites is an
  equation between two constructor applications --
  `h : {Some{Err{p1, w1}} == Some{Err{p2, w2}} : Maybe<Err>}` -- where what the
  proof needs is the equation of the parts. Congruence gives it: write the
  stripping function as a def (`m => why_or(m)` for the `why` inside `Err`,
  `m => maybe_why(m)` for the `Some{why}` a defect is written as) and derive
  the equation with `Equal.cong(A, B, m => f(m), x, y, h)`. What comes out is a
  theorem to hand to the goal as a term -- `same_why_m(..., h)`, the shape an
  induction case closes with (`i1(h)`) -- not a rewrite either. Measured in
  bend-schema's tag-key round on bend 2.0.32: the proof has such an equation in
  hand and no `%` line for it, and `same_why`/`same_why_m` are a line each.

## 1.3 What computes, and what does not

- **The successor cases of arithmetic are definitional.** `Nat.mul(1+n, p)`
  unfolds to `Nat.add(p, Nat.mul(n, p))`, `Nat.cmp(1+a, 1+b)` to
  `Nat.cmp(a, b)`, `Nat.add(1+a, k)` to `1+Nat.add(a, k)`. A proof can be
  arranged so that a whole branch closes by `{==}` with no rewriting -- usually
  a sign the statement is right.
- **`Nat.add(mp, 1+x)` does not reduce** (the recursion is on the first
  argument, a variable). Every fact of that shape is a theorem you import:
  `add_succ`, `add_assoc`, `add_comm`.
- **`Nat.div.fin` / `Nat.mod.fin` reduce on a computing call**, so a theorem
  about a pair-returning function can be stated with no `let`.
- **A def that matches its argument does not reduce on an abstract one.** A
  `cons_row(c, r)` that matches `r` is stuck on `r = report(rest)`; a lemma that
  matches `r` and closes by `{==}` states what it does, oriented to eliminate
  the stuck call.
- **The checker runs an entire fuel loop when the input is ground.** A claim
  about concrete data closes by `{==}` because the normaliser walks the loop to
  its exit. With an abstract value the loop stops at the first comparison
  (1.7).
- **A big numeral the checker must unfold crashes it; one that sits in the goal
  does not.** `RangeError: Maximum call stack size exceeded`, inside
  `term_higher` / `term_snf`, from the size of a fuel numeral alone -- same
  20-line program, only the number changed:

  | fuel | result |
  |---|---|
  | `4n`, `40n`, `1000n`, `10000n` | clean `expected`/`observed` |
  | `100000n` | `RangeError` |
  | `4294967295n` | `RangeError` |

  So a program that loops on `U32.to_nat(4294967295)` -- what long-running
  programs are told to use -- fails to *prove* anything about itself, by
  exhausting the checker's stack rather than reporting a stuck term
  (a large numeral walked down exhausts the checker's stack). But a goal
  holding `Nat.div(_, 1000000n)` checks in
  0.06 s, and the checker accepts `1000000n` where `1n+999999n` is expected
  (`div_mono(..., 999999n)`): the crash is a numeral walked down, not a
  numeral present.
- **A def that computes a large constant hangs every literal instance that
  reaches it.** A `limit()` of 2^48-1 must be built as
  `Nat.add(Nat.mul(65535n, Nat.add(4294967295n, 1n)), 4294967295n)` because a
  literal stops at 2^32-1. A literal instance closed by `{==}` ran past
  20 s when the def read `limit()`, and in 0.2 s once the limit was a
  parameter. Take such a constant as a parameter (`f_under(x, lim)`), state
  the laws for every value of it, and instantiate it in one wrapper
  (`f(x) = f_under(x, limit())`): the laws get stronger, and no goal carries the constant.
- **Equality has no reflexivity.** `String.eq(s, s)` does not reduce when `s`
  is abstract: the goal stays `String.eq.fin(String.cmp(s, s))`, and the
  checker reports `expected : String.eq.fin(String.cmp(s, s)) / observed : True{}`.
  The same holds for `Nat.is_eq(n, n)` (`Cmp.is_eq(Nat.cmp(n, n))`). Base
  states no reflexivity lemma, so nothing about an abstract value's equality
  with itself comes for free. The ladder is short -- `String.eq` ->
  `String.cmp` -> `Char.cmp` -> `U32.cmp` -> `Word.cmp` -- and every step is
  a short induction:

  | claim | proof |
  |---|---|
  | `{EQ{} == Bool.cmp(b, b)}` | two cases |
  | `{EQ{} == Word.cmp(n, w, w)}` | induct on `n`, then split `w` |
  | `{EQ{} == U32.cmp(x, x)}` | `match x: case U32{w}:`, lemma at `32n` |
  | `{((c, c), EQ{}) == Char.cmp(c, c)}` | `match c: case Chr{x}:`, then `U32` |
  | `{((s, s), EQ{}) == String.cmp(s, s)}` | induct on `s`, split `h` to `Chr{x}` |
  | `{True{} == String.eq(s, s)}` | rewrite with the `String.cmp` law |

  `case SCon{h, t}`'s `h` must be split to `Chr{x}` before `Char.cmp` moves (a
  `Char` is one constructor wrapping a `U32`), and `Word.cmp` recurses on the
  width, so `1n+p` is the induction and `WCon{ab, at}` the case.
- **`Nat.sub(c, 0n)` and `Nat.is_le(0n, c)` do not reduce on an abstract
  `c`**: both recurse on `c` first. A lemma whose base case is `a = 0` still
  has to split `c` (`match a c:` with `0n 0n`, `0n 1n+j`), or it is refused
  with `expected : Bool.and(Cmp.is_le(Nat.cmp(0n, c)), ...)`. Measured on
  `split_r` (`a + b <= c` iff `a <= c` and `b <= c - a`).
- **A law's `Nat` is unbounded; the runtime's is not.** Proofs are about the
  mathematical `Nat`, and the runtime stops at 2^48-1. So a law that
  holds "for every input" does not cover overflow: a proved-monotone fee still
  ends the program on an input whose product passes the bound. Where inputs can
  be large, bound them at the boundary, in the host, before they reach the core.
- **Two *different* abstract values do not compare.** `String.eq(a, b)` does
  not reduce, and no lemma says distinct abstract values stay distinct. A
  claim that needs it takes the answer as a hypothesis (1.1), one per pair the
  code compares. That is the honest form of the limit: the claim is verified
  for inputs whose names are distinct, and not for arbitrary ones.

- **A proof over an abstract value enumerates its constructors, so adding a
  constructor breaks it, in every project that does.** A match on an abstract
  `r` is stuck until `r` is split, so a proof that makes `check` and
  `conforms` compute writes every case out. Adding a constructor to a
  datatype breaks every such proof -- the library's and its callers' -- each
  refused with `expected : cases for core.RBool`. Each was the nearest existing case
  (`RStr`) copied: where the new constructor behaves like an old one, copy
  that one's case mechanically.

  **A catch-all arm does not shorten the table.** In a proof, `case C.STEnd{} x:`
  after `case C.STEnd{} C.RNil{}:` gives `x` the type `Raw<> - RNil{}` (the
  context prints it so), but `x` is still abstract: `check` and `conforms`
  are stuck on it, and `{==}` is refused with
  `expected : Bool.not(Maybe.is_some(..., C.check(..., C.STEnd{}, r, prev))) /
  observed : C.conforms(..., C.STEnd{}, r, prev)`. Each constructor must be
  its own arm for the goal to compute. So generate the arms: a table is
  mechanical (the constructors, and for each the leaf and the reason it
  reports), and a generator that keeps the hand-written arms turns a new
  constructor into one directive and no other edit.

- **A fact about two names often needs both orders of `String.eq`.** Reading a
  key compares `String.eq(k, name)`; reading past it in another walk compares
  `String.eq(name, k)`, and Base has no symmetry lemma for strings. Asking both
  (`Bool.not(String.eq(m, n))` and the reverse) in the code is cheaper than proving the symmetry.

## 1.4 Impossible cases close by rewriting, not by matching

**This section is reversed.** It used to say a case whose hypothesis
is false cannot be discharged. That is wrong; only its first step is right.

`{a == b : A}` is a built-in equality, **not a datatype**, so it cannot be
matched:

```bend
def false_not_true(e: {True{} == False{} : Bool}) -> Empty:
  match e:
# Error: - expected : a datatype
#        - observed : {True{} == False{} : Bool}
```

But it can be *rewritten with*, and a rewrite through a type-valued function
turns the goal `Empty` into one that is inhabited:

```bend
def Tag(b: Bool) -> Type:
  match b:
    case False{}: Unit
    case True{}:  Empty

def to_empty(e: {False{} == True{} : Bool}) -> Empty:
  %e : Tag(_)      # the goal Empty is Tag(True); e turns it into Tag(False)
  Unit{}
```

From `Empty`, `Empty.absurd` gives any goal. The same works for `Nat`:
`Pos(0n)` is `Empty` and `Pos(1n+p)` is `Unit`, so `{1n+e == 0n}` is absurd
When the goal is an equation there is a shorter
road through congruence: with `pick(u, v, b)` returning `u` on `False` and `v`
on `True`, `Equal.cong(Bool, A, b => pick(A, u, v, b), False{}, True{}, e)`
*is* a proof of `{u == v : A}`. Both were checked against a control: with a
true hypothesis `{True{} == True{}}` in place of `e`, the checker refuses
(`expected : Empty, observed : Unit`;
`expected : {0n == 1n}, observed : {1n == 1n}`), so neither proves anything it
should not.

So **implication-shaped lemmas are writable.** `{True{} == Bool.and(a, b)}`
gives `{True{} == b}`: match on `a`; in the `False` arm the hypothesis has
become `{True{} == False{}}`, which `to_empty` turns into `Empty`, and
`Empty.absurd` closes the arm.

## 1.5 Choosing the statement

The statement decides the proof: once it is right, most proofs check on the
first or second try.

- **A decision a proof must follow goes through a parameter.** A Bool computed
  in one step and matched in the next is, by then, a field with nothing tying
  it to the call that made it; a law over abstract inputs can follow it only
  one unfolded step at a time (1.7). Written the way Base writes `List.filter`,
  the decision stays visible:

  ```bend
  def keep(+slot: Iv, rest: List<&2, Iv>, ok: Bool) -> List<&2, Iv>:
    match ok:
      case False{}: rest
      case True{}:  slot <> rest

  def fitting(+people: ..., xs: List<&2, Iv>) -> List<&2, Iv>:
    match xs:
      case Nil{}:      Nil{}
      case +h <> t:    keep(h, fitting(people, t), all_ok(people, h))
  ```

  A lemma takes the decision `b` *and* `e : {b == all_ok(people, h)}`, then
  matches on `b`: in the `True` arm the checker shows
  `e : {True{} == all_ok(people, h)}`, in the other `{False{} == ...}`. The
  caller passes `all_ok(people, h)` for `b` and `{==}` for `e`. No comparison
  is computed.
- **A predicate computed as a `Type` is a usable premise: take it apart once
  per step.** *This reverses an earlier entry here, which said such a class must
  arrive as a datatype.* State the class as a def matched on the input, whose
  cons case is a chain of dependent pairs: the facts about this element, then
  the predicate on the tail. In the proof, match the input, destructure the
  premise once, and hand the tail's piece to the recursive call:

  ```bend
  def Clean(s: String) -> Type:          # in LAWS.bend
    match s:
      case SNil{}:
        Unit
      case SCon{Chr{x}, t}:
        {U32.is_eq(x, 44) == False{} : Bool} & ... & Clean(t)

  def walk(s: String, h: Laws.Clean(s), ...) -> {...}:   # in PROOF.bend
    match s:
      case SNil{}:
        {==}
      case SCon{Chr{+x}, t}:
        (hse, hqu, hcr, hlf, ht) = h     # each piece used once
        ...
        walk(t, ht, ...)
  ```

  Every piece is used exactly once, so the premise never needs `+` (which a
  `Type` refuses: `expected : Data / observed : Type`). `consumed more than once`
  on such a premise means one proof passed the same `h` to two consumers -- a
  `match` and a helper lemma, say -- not that the statement is unprovable. Keep
  the facts as equations on a comparison (`{U32.is_eq(x, 44) == False{} :
  Bool}`), not a Bool predicate: a comparison of an abstract character does not
  reduce, and the equation is what a rewrite turns into a branch the program
  takes. Measured on csv-lib: the whole proof checks this way, with no mirror
  datatype and no conversion from the premise to one.
- **A state machine a proof walks reads one token per case.** A case that looks
  two tokens ahead (`case TCon{KCR{}, TCon{KLF{}, t}} PhUnq{}:`) does not reduce
  when the tail is abstract, even in a phase where the lookahead does not
  matter: the match tree tests the second token before it reaches the phase, and
  the second token of an abstract tail is a stuck `classify(c)`. Turn the
  lookahead into a phase (a CR seen, its meaning not yet known) so every case
  inspects one token. Then a proof over "every input from every state" is one
  case split per token, and a lemma quantified over the phase and the state
  (`@ph2 -> @st2 -> ...`, passed in as `ih`) serves all of them. Measured on
  csv-lib: with the lookahead no quoted-field proof could step past a CR; after
  the change the oracle and falsifier were unchanged and all six laws closed.
- **A step that reads part of a state takes that part, not the state.**
  `close_rec(st, out)` matching `started_of(st)` stays stuck on an abstract
  flag, so two states that differ only in position give two different stuck
  terms, and no rewrite makes them one. Passing `row_of(st)`, `fld_of(st)` and
  the flag as separate arguments makes both reduce to the same term. A law that
  compares two runs ("a blank line adds nothing") then needs a lemma over the
  state's constructor fields -- `C.St{r, f, g, l1, c1, ...}` against
  `C.St{r, f, g, l2, c2, ...}` -- that position never changes the answer.

- **Carry a witness, not a test.** `a <= b` read as `b == Nat.add(a, k)` makes
  every hypothesis an equation `%` rewrites freely; transitivity is four lines
  that way, and `is_le` comes back at the end through one lemma
  (`le_add`, `lt_add`). Membership is a split: "if
  `x` is in `xs` and fits, it is in the answer" needs an `elem` test that
  compares two abstract values, which does not reduce; stated as

  ```bend
  for hc: {List.append(&2, C.Iv, pre, x <> post) == C.cands(...) : List<&2, C.Iv>}
  for hx: {True{} == C.all_ok(people, x) : Bool}
  {C.slots(...) == List.append(&2, C.Iv, C.fitting(people, pre), x <> C.fitting(people, post)) : ...}
  ```

  the proof inducts on `pre`, never compares two values, and says more than
  membership: where `x` lands. It needs one lemma, that the filter's step
  commutes with append (`keep(h, a ++ b, k) == keep(h, a, k) ++ b`, two cases
  on `k`). Choose the witness form for what it states, not to avoid a wall:
  impossible cases are closable (1.4).
- **An existential is a dependent pair.**
  `&wpre: L -> &w: Iv -> &wpost: L -> {wins == wpre ++ (w <> wpost)} & {True{} == contains(w, slot)}`
  says "some window in `wins` contains the slot, and here is where". Build it
  as a tuple, `(Nil{}, w, rest, {==}, e)`, and extend a tail's witness in its
  own def: a computed pair cannot be matched (language.md 1.1).
- **Replace fuel with a computed count** (language.md 1.2): no large numeral in any goal,
  and `Nat.div(_, 0n)` is `0n`, so a zero step ends instead of spinning the
  fuel down. A fuel loop on `step = 0` runs 2^32 rounds: measured, still
  running at 30 s.
- **Build a list by recursion on its source, and state its order as a law.** A
  fold that prepends to an accumulator reverses its input, and a consumer that
  pairs rows with labels by index then shifts every number by a row while
  still looking plausible.
- **A law whose goal makes the checker run application code does not finish.**
  A parser over JSON text in the goal, the decoded value in the goal, and the
  decoded value with a small fuel were all tried; none returned within twenty
  seconds, and which part is expensive was not isolated (two attributions were
  tried and both were wrong). Check such a seam by running both sides against
  each other instead.
- **A pair of consistency laws pins agreement, not meaning.** `check_exact`
  (`conforms` iff `check` finds nothing) and the round-trip laws hold for any
  change that is wrong in the *same direction on both sides*, so a fully green
  gate can accept a core that has started accepting something else. Measured:
  a repeated key was meant to be refused, and the correctness def that decides
  it tested the keys *after* the one in hand instead of the one in hand, so
  `conforms` returned `True` for `{"a":1,"a":2}` and `check` returned nothing.
  Both sides were wrong together, so `check_exact` and `check_accurate` held;
  the falsify instances passed on the broken core; and a mutant that makes
  `check` return `Nothing` tests the *report*, not the refusal, so it does not
  catch it either. What caught it was a law asserting the refusal at a
  concrete value — `{conforms(s, r) == False}` together with
  `{check(s, r) == Some{Err{path, why}}}` — for explicit constructors, and it
  had to be written *before* the rest was trusted, because nothing else in the
  gate pins that meaning. So: when a change is about what the core accepts,
  write the law that states the acceptance itself, and prefer two mutants that
  break it in two different ways (the report, and the test) over one.

## 1.6 Writing the proof

- **Induct on the argument the function recurses on.** `Nat.mul` recurses on
  its first argument, so mul monotonicity inducts on the *number*, not on the
  increment -- then both sides become `Nat.add(p, _)` by unfolding alone and
  the hypothesis is already under that `add(p, _)`. Inducting on the increment
  instead needs transitivity, and a longer proof. `Nat.divmod.go` recurses on
  `n`, so monotonicity of `Nat.div` inducts on `n` and every step is
  definitional: `Nat.add(1+a, k)` steps in lockstep with `a`.
- **State the lemma so the recursive branch's goal is definitionally the
  hypothesis.** A recursive call's conclusion is often *syntactically* the
  induction hypothesis, because the branch has already fixed the constructors;
  then only the hypothesis has to be transported, best as its own small def
  whose goal is the equation. If it is not, the missing piece is usually a
  congruence lemma (`add(p, _)` preserves `<=`), itself two cases.
- **Rearrange a sum by induction on its leftmost variable, not by a chain of
  `assoc`/`comm`.** `Nat.add` recurses on the left, so for
  `((t + (1 + (k + c))) + p) == ((t + ((1 + p) + k)) + c)` the successor case
  is one rewrite with the hypothesis, and only the `0n` case needs two lemmas.
  The chain version fights each lemma's orientation line by line.
- **Generalise an accumulator before inducting.** A fold with an accumulator is
  proved for every accumulator
  (`total(go(us, acc)) == total(acc) + total(report(us))`), then instantiated
  at the starting value.
- Then the arithmetic library you feared you needed -- distributivity,
  subtraction, cancellation -- often turns out not to be needed at all, and
  what is needed is short: the division equation, monotonicity of `Nat.div`
  and distributivity are each one induction.

## 1.7 Proofs over a loop

**The rewrite works.** A fuel loop whose states carry a `Bool` computed in the
previous step (`SE{eq: String.eq(h, d), ...}`, matched as `SE{True{}, ...}`
next round) can be reasoned about with an abstract value: run `bend`, read the
goal it reports, and write it into `%e : P` with `_` where the stuck comparison
sits. The comparison is replaced and the loop carries on. For a two-element
input that is two lines, and the claim closes for every pair of names.

- The goal is the loop *unfolded*: the state constructor with the stuck
  comparison inside and the fuel reduced to a numeral, e.g.
  `run(195n, ME{String.eq.fin(String.cmp(a, a)), [b], a, ...})`. Each line is
  as long as the state is wide, and grows with the accumulator. This is
  mechanical, and a script can generate the lines from the goals the checker
  prints.
- **State such a law over `run(f, st)`, not over the wrapper that bakes the
  fuel in.** The wrapper is what makes the numeral crash (1.3) unavoidable, and a
  bound the input actually needs is not a weaker statement.
- **Out of reach** is a comparison between two different abstract values
  (1.3): a scan asking whether `b` is already in `done = [a]` sits at
  `ME{String.eq.fin(String.cmp(a, b)), ...}` and stays there unless a
  hypothesis supplies the answer. Concrete values decide by computation, which
  is why a law on concrete data closes by `{==}` while the same theorem over
  variables does not.

When the loop can be restructured, 1.5's decision-as-parameter and computed
count avoid all of this, and keep goals short enough to write by hand.

## 1.8 Facts you do not have to prove

`~/.bend/bend2/base.bend` is 64 KB and contains, already proved:

| | |
|---|---|
| `Equal.cong`, `Equal.sym`, `Equal.trans` | equational reasoning |
| `Empty.absurd` | ex falso -- fed by a rewrite (1.4) |
| `Nat.ge_refl`, `Nat.max_ge_l`, `Nat.max_ge_r` | the only proved facts about `Nat` order |
| `Pair.fst`, `Pair.snd`, `Nat.div.fin`, `Nat.mod.fin` | projections |
| `law X:` + `def X(...)` | how a proved law is written |

`law Nat.ge_refl` is proved with `True{}` on the left, so it cannot rewrite a
goal; one bridge def in the other orientation makes it usable, and that bridge
is how `is_le` facts are built on `is_ge` ones. `Cmp.is_le` is **not**
`Cmp.is_ge` pointwise -- they differ on `LT{}` and `GT{}`; the relation is
`is_le(a,b) == is_ge(b,a)`, arguments swapped.

Keep everything Base does not state in one lemma directory of your own:
comparison reflexivity, `Nat` order and witnesses,
`Nat.add`, `Nat.divmod` (the division equation, monotonicity), `Nat.sub`,
cancellation, distributivity, `String` and `List` append and reverse. They are
deliberately not filed upstream -- the author may not want to carry them, and
adding them later is cheap.

## 1.9 Testing the proofs

A proof that checks in 0.07 s may be proving less than you think.

- **Make each law false and require its proof to fail.** Mutate the core so the
  law no longer holds -- not merely so the proof stops parsing -- and require
  the failure inside that law's own lemmas. Check the unmutated copy from the
  same place too, so the failure is known to be the mutation and not the
  location.
- **Isolate the law under test.** The checker stops at the first failing def,
  in file order, and proofs built on the same definitions break together -- one
  mutation of a shared predicate can fail four proofs at once. So check one
  law's section of `PROOF.bend` at a time, with the shared lemmas, and match
  `Location: <def>`.
- **A scratch copy mirrors the tree** (the project beside its imports): a
  relative import does not resolve from a bare temp directory, and the error it
  gives has no `Location` to match.
- **A failure in a shared lemma is a weaker signal.** When a mutation changes a
  helper every proof describes, the proof fails in the lemma about the helper,
  not in the law's own induction. It still shows the proof depends on the
  code.

A harness can do all of this: split `PROOF.bend` into one section per law
plus sections of shared lemmas, keep one law's section (and the shared ones)
and drop every other law from `LAWS.bend`. Three rules follow,
each learned from a control that failed unmutated:

- **A section belongs to one law.** Four laws' proofs under one header made
  all four controls fail: the kept `LAWS.bend` had one law, and the other
  three `def Laws.X` were refused with
  `expected : '->' (a def with no return type fills a law; no law named Laws.X is in scope)`.
- **`def Laws.X` sits in X's own section**, not in a section of helpers it
  shares with another law, for the same reason.
- **A lemma two laws use goes in a shared section**, or the second law's
  run keeps the first law's section too (which brings that law along).

---
