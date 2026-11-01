# MISTAKE 2: "Claude, the carry logic is hard to follow. Round every share
# down, then give the leftover cents to the first account."
#
# A common real-world shortcut. The shares now add up to the total (LAW 1
# holds), but with n accounts the first can receive up to n - 1 extra cents:
# $99.99 over seven equal accounts pays the first $14.31 against an exact
# $14.2843, almost three cents over. LAW 2 (fairness) is false for this
# code, so no proof of it can exist.
#
# This is main.bend with the split changed (marked below).

import Base

# The total weight. Shared with SPEC.bend's statement of the laws.
def sum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(h, sum(t))

# One zero per account: what a split with no weight at all pays.
def zeros(xs: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      0n <> zeros(t)

# CHANGED: every share rounded down on its own, carry ignored
# The split proper, for a total weight W = 1 + bp (so bp = W - 1, and the
# division never sees zero). `carry` is the remainder from the accounts
# already paid.
def go(+total: Nat, +bp: Nat, ws: List<&2, Nat>, +carry: Nat) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      Nat.div(Nat.mul(w, total), 1n+bp) <> go(total, bp, rest, carry)

# CHANGED: the leftover goes to the first account
def to_first(xs: List<&2, Nat>, extra: Nat) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      Nat.add(h, extra) <> t

def leftover(+total: Nat, +bp: Nat, +ws: List<&2, Nat>) -> List<&2, Nat>:
  +floors = go(total, bp, ws, 0n)
  to_first(floors, Nat.sub(total, sum(floors)))

def split(+total: Nat, +ws: List<&2, Nat>, weight: Nat) -> List<&2, Nat>:
  match weight:
    case 0n:
      zeros(ws)
    case 1n+bp:
      leftover(total, bp, ws)

# allocate(total, weights): one share per weight. With no weight at all
# (every weight zero, or no accounts) nothing can be split: every share is
# zero, and the caller must treat the total as unallocated.
def allocate(+total: Nat, +ws: List<&2, Nat>) -> List<&2, Nat>:
  split(total, ws, sum(ws))
