# Definitions the laws are written in. Like LAWS.bend, this file belongs to
# the human reviewer: change it and you change what the laws mean.

import Base
import ./vendor/Natural.bend as N

# a < b, as evidence: a proof of 1 + a <= b
def Lt(a: Nat, b: Nat) -> Kind(&2):
  N.Natural.Le(1n+a, b)

# Fair(T, W, ws, ss): the shares ss match the weights ws one for one, and
# each share s for weight w is within one unit of the exact pro-rata amount
# w * T / W. Multiplying through by W, that is
#
#   s * W < w * T + W      (s is below w*T/W + 1)
#   w * T < s * W + W      (s is above w*T/W - 1)
#
# A list of the wrong length is not fair: there is no proof of Empty.
def Fair(+total: Nat, +weight: Nat, ws: List<&2, Nat>, ss: List<&2, Nat>) -> Type:
  match ws ss:
    case Nil{} Nil{}:
      Unit
    case Nil{} s <> st:
      Empty
    case w <> wt Nil{}:
      Empty
    case +w <> wt +s <> st:
      ((Lt(Nat.mul(s, weight), Nat.add(Nat.mul(w, total), weight))
        & Lt(Nat.mul(w, total), Nat.add(Nat.mul(s, weight), weight)))
        & Fair(total, weight, wt, st))

# ZeroKept(ws, ss): every account with weight zero receives zero.
def ZeroKept(ws: List<&2, Nat>, ss: List<&2, Nat>) -> Type:
  match ws ss:
    case Nil{} _:
      Unit
    case w <> wt Nil{}:
      Unit
    case w <> wt s <> st:
      (ZeroKept.one(w, s) & ZeroKept(wt, st))

def ZeroKept.one(w: Nat, s: Nat) -> Type:
  match w:
    case 0n:
      {s == 0n : Nat}
    case 1n+p:
      Unit
