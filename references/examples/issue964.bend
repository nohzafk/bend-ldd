import Base

# Issue 964's reproducer, with the motive its closing comment gives.
#
# The claim under test: `P` need not be the printed normal form. The checker
# compares `P(b)` with the goal up to computation, so the motive may be written
# with the PROGRAM'S OWN SOURCE TERMS. That is what matters here: the goal
# embeds a term `unit` builds (a JSON fragment), and writing the printer's
# normal form by hand would mean restating a 900-character term on every
# rewrite line.
#
# Verified on bend 2.0.31: `All terms check.`, exit 0, no unsafe note.
#
# Reflexivity of `String.eq` is taken as a hypothesis rather than proved, so the
# file is self-contained and proves nothing about strings -- the point is the
# motive, and a hypothesis isolates it. (An earlier version imported
# bend-mathlib's `eq_refl_sym` and checked just as cleanly; the author of the
# issue filled it with an `@unsafe` stub and said so. Either way the motive line
# is identical.)

# a config unit as JSON, built by the program before it is sent
def unit(name: String, body: String) -> String:
  String.append(String.append("{\"name\":\"", name),
    String.append("\",\"body\":\"", String.append(body, "\"}")))

type St is Data:
  Walk{acc: String, other: String}
  Hold{ok: Bool, acc: String, other: String}

def go(fuel: Nat, st: St) -> Bool:
  match fuel st:
    case 0n _:
      False{}
    case 1n+f Walk{+acc, +other}:
      go(f, Hold{String.eq(acc, other), String.append(acc, ","), other})
    case 1n+f Hold{True{}, +acc, +other}:
      True{}
    case 1n+f Hold{False{}, +acc, +other}:
      go(f, Walk{acc, other})

# What the program asks of `go` at the state it built: the two units it made are
# the same, so `go` says yes.
law composed:
  for +a: String
  for +h: {True{} == String.eq(unit(a, "x"), unit(a, "x")) : Bool}
  {True{} == go(7n, Hold{String.eq(unit(a, "x"), unit(a, "x")), String.append(unit(a, "x"), ","), unit(a, "x")}) : Bool}

# The motive names `unit(a, "x")` and `String.append(unit(a, "x"), ",")` -- the
# terms the program builds, not what the printer would show -- with `_` at the
# occurrence being replaced. `%h` rewrites that occurrence (the lemma's right
# side) to `True{}`, the state becomes `Hold{True{}, ..}`, `go` reduces it to
# `True{}`, and `{==}` closes the goal.
def composed(a, h):
  %h : {True{} == go(7n, Hold{_, String.append(unit(a, "x"), ","), unit(a, "x")}) : Bool}
  {==}
