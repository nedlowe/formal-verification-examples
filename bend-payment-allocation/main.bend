# Payment allocation: split a total, in whole minor units (cents), across
# accounts in proportion to their weights, losing and inventing nothing.
#
# The method carries the rounding remainder from each account to the next.
# With W the sum of the weights, account i receives
#
#   share_i = (carry + w_i * T) div W      carry' = (carry + w_i * T) mod W
#
# starting from carry = 0. Every step is an exact equation
#
#   share_i * W + carry' = carry + w_i * T,   with carry, carry' < W
#
# which is what makes the laws in LAWS.bend provable: the shares add up to
# exactly T, and each share is less than one cent away from the exact
# pro-rata amount w_i * T / W.
#
# This file is the program. LAWS.bend states what it must do; PROOF.bend
# proves that it does. Edit this file freely, but `bend PROOF.bend` must
# print ALL PROOFS CHECK before the change is committed.

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
      +x = Nat.add(carry, Nat.mul(w, total))
      Nat.div(x, 1n+bp) <> go(total, bp, rest, Nat.mod(x, 1n+bp))

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
