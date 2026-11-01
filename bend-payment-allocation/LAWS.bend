# LAWS: what payment allocation must never get wrong.
#
# The human owns this file. The AI (or anyone) changing main.bend must keep
# every law below proven in PROOF.bend; `bend PROOF.bend` is the commit gate.
#
# Every law that splits money assumes some weight to split by: the weights
# add up to 1 + bp for some bp, which is to say to a positive number W.

import Base
import ./main.bend as Alloc
import ./SPEC.bend as Spec

# LAW 1, conservation: the shares add up to exactly the total. No cent is
# lost to rounding, and none is invented.
law conserves:
  for +total: Nat
  for +ws: List<&2, Nat>
  for -bp: Nat
  for e: {Alloc.sum(ws) == 1n+bp : Nat}
  {Alloc.sum(Alloc.allocate(total, ws)) == total : Nat}

# LAW 2, fairness: there is exactly one share per account, and each share is
# less than one unit (one cent) away from its exact pro-rata amount
# weight * total / W. Rounding may move a share up or down, never further.
law fair:
  for +total: Nat
  for +ws: List<&2, Nat>
  for -bp: Nat
  for e: {Alloc.sum(ws) == 1n+bp : Nat}
  Spec.Fair(total, 1n+bp, ws, Alloc.allocate(total, ws))

# LAW 3, zero in, zero out: an account with weight zero receives nothing,
# whatever the total and whatever the other weights.
law zero_weight_gets_zero:
  for +total: Nat
  for +ws: List<&2, Nat>
  Spec.ZeroKept(ws, Alloc.allocate(total, ws))
