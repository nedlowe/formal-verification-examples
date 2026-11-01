# MISTAKE 1: "Claude, simplify the allocator. Just work out each account's
# share directly as weight * total / W, there's no need to carry anything."
#
# Each share is still within a cent of its exact amount (LAW 2 holds), but
# the cents that every share rounds away are never paid to anyone:
# $100.00 over three equal accounts pays [$33.33, $33.33, $33.33] = $99.99.
# LAW 1 (conservation) is false for this code, so no proof of it can exist.
#
# This is main.bend with one line changed (marked below).

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

# The split proper, for a total weight W = 1 + bp (so bp = W - 1, and the
# division never sees zero). `carry` is the remainder from the accounts
# already paid.
def go(+total: Nat, +bp: Nat, ws: List<&2, Nat>, +carry: Nat) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      # CHANGED: no carry; the remainder is dropped
      Nat.div(Nat.mul(w, total), 1n+bp) <> go(total, bp, rest, carry)

def split(+total: Nat, +ws: List<&2, Nat>, weight: Nat) -> List<&2, Nat>:
  match weight:
    case 0n:
      zeros(ws)
    case 1n+bp:
      go(total, bp, ws, 0n)

# allocate(total, weights): one share per weight. With no weight at all
# (every weight zero, or no accounts) nothing can be split: every share is
# zero, and the caller must treat the total as unallocated.
def allocate(+total: Nat, +ws: List<&2, Nat>) -> List<&2, Nat>:
  split(total, ws, sum(ws))
