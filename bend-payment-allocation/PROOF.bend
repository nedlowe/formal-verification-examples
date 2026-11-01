# PROOF: why main.bend obeys LAWS.bend. Checked by `bend PROOF.bend`.
#
# The whole argument rests on one equation per account. With W = 1 + bp and
# x = carry + w * total, main.bend pays q = x div W and carries r = x mod W:
#
#   q * W + r == carry + w * total,   r <= bp            (div.spec)
#
# Summed over the accounts it telescopes (kept), which pins the shares'
# total to exactly `total` (Laws.conserves). On its own it bounds each
# share to within one unit of w * total / W (fair.one, Laws.fair), and
# that bound leaves a zero-weight account nothing (Laws.zero_weight_gets_zero).
#
# Bend has no tactics: each step below is an explicit equation or
# inequality, chained with Equal.trans / N.Natural.le_transitive.

import Base
import ./vendor/Natural.bend as N
import ./main.bend as Alloc
import ./SPEC.bend as Spec
import ./LAWS.bend as Laws

# Division
# --------
# Base's Nat.divmod(x, 1 + bp) answers (q, r) with q * (1 + bp) + r == x
# and r <= bp. Nat.divmod.go(n, m, d, r) counts n down: d is the quotient
# so far, r the remainder so far, and m how far r is from rolling over, so
# m + r == bp throughout.

def DivOk(bp: Nat, t: Nat, p: Nat & Nat) -> Type:
  ({Nat.add(Nat.mul(Pair.fst(Nat, Nat, p), 1n+bp), Pair.snd(Nat, Nat, p)) == t : Nat}
    & N.Natural.Le(Pair.snd(Nat, Nat, p), bp))

def DivOk.cast(-bp: Nat, -t1: Nat, -t2: Nat, -p: Nat & Nat, e: {t1 == t2 : Nat}, ok: DivOk(bp, t1, p)) -> DivOk(bp, t2, p):
  %e : DivOk(bp, _, p)
  ok

# the target after n more steps: n + (r + d * (1 + bp)); Nat.add recurses on
# its first argument, so a step of n is a step of the sum
def div.go(+n: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +inv: {Nat.add(m, r) == bp : Nat})
  -> DivOk(bp, Nat.add(n, Nat.add(r, Nat.mul(d, 1n+bp))), Nat.divmod.go(n, m, d, r)):
  match n:
    case 0n:
      (N.Natural.add_commutative(Nat.mul(d, 1n+bp), r),
        N.Natural.le_congruent(r, Nat.add(r, m), r, bp, N.Natural.le_add_right(r, m), {==},
          Equal.trans(Nat, Nat.add(r, m), Nat.add(m, r), bp, N.Natural.add_commutative(r, m), inv)))
    case 1n+np:
      match m:
        case 0n:
          DivOk.cast(bp,
            Nat.add(np, 1n+Nat.add(bp, Nat.mul(d, 1n+bp))),
            1n+Nat.add(np, Nat.add(r, Nat.mul(d, 1n+bp))),
            Nat.divmod.go(np, r, 1n+d, 0n),
            Equal.trans(Nat,
              Nat.add(np, 1n+Nat.add(bp, Nat.mul(d, 1n+bp))),
              1n+Nat.add(np, Nat.add(bp, Nat.mul(d, 1n+bp))),
              1n+Nat.add(np, Nat.add(r, Nat.mul(d, 1n+bp))),
              N.Natural.add_successor(np, Nat.add(bp, Nat.mul(d, 1n+bp))),
              Equal.cong(Nat, Nat, z => 1n+Nat.add(np, Nat.add(z, Nat.mul(d, 1n+bp))), bp, r, Equal.sym(Nat, r, bp, inv))),
            div.go(np, r, 1n+d, 0n, bp, Equal.trans(Nat, Nat.add(r, 0n), r, bp, N.Natural.add_zero(r), inv)))
        case 1n+mp:
          DivOk.cast(bp,
            Nat.add(np, 1n+Nat.add(r, Nat.mul(d, 1n+bp))),
            1n+Nat.add(np, Nat.add(r, Nat.mul(d, 1n+bp))),
            Nat.divmod.go(np, mp, d, 1n+r),
            N.Natural.add_successor(np, Nat.add(r, Nat.mul(d, 1n+bp))),
            div.go(np, mp, d, 1n+r, bp,
              Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, N.Natural.add_successor(mp, r), inv)))

# the division spec, for a divisor 1 + bp
def div.spec(+x: Nat, +bp: Nat) -> DivOk(bp, x, Nat.divmod(x, 1n+bp)):
  DivOk.cast(bp, Nat.add(x, 0n), x, Nat.divmod(x, 1n+bp), N.Natural.add_zero(x),
    div.go(x, bp, 0n, 0n, bp, N.Natural.add_zero(bp)))

# Conservation
# ------------
# final(...) is the remainder go(...) leaves after the last account. The
# invariant: for a carry c <= bp, the shares times W, plus that last
# remainder, are exactly c + (sum of weights) * total.

def final(+total: Nat, +bp: Nat, ws: List<&2, Nat>, +carry: Nat) -> Nat:
  match ws:
    case Nil{}:
      carry
    case w <> rest:
      final(total, bp, rest, Nat.mod(Nat.add(carry, Nat.mul(w, total)), 1n+bp))

def Kept(+total: Nat, +bp: Nat, +ws: List<&2, Nat>, +carry: Nat) -> Type:
  (N.Natural.Le(final(total, bp, ws, carry), bp)
    & {Nat.add(Nat.mul(Alloc.sum(Alloc.go(total, bp, ws, carry)), 1n+bp), final(total, bp, ws, carry))
        == Nat.add(carry, Nat.mul(Alloc.sum(ws), total)) : Nat})

# ((a + b) + c) == f + (g + e), given b + c == d + e and a + d == f + g
def kept.alg(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, +g: Nat,
  e2: {Nat.add(b, c) == Nat.add(d, e) : Nat}, e1: {Nat.add(a, d) == Nat.add(f, g) : Nat})
  -> {Nat.add(Nat.add(a, b), c) == Nat.add(f, Nat.add(g, e)) : Nat}:
  Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Nat.add(f, Nat.add(g, e)),
    N.Natural.add_associative(a, b, c),
    Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(a, Nat.add(d, e)), Nat.add(f, Nat.add(g, e)),
      Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(b, c), Nat.add(d, e), e2),
      Equal.trans(Nat, Nat.add(a, Nat.add(d, e)), Nat.add(Nat.add(a, d), e), Nat.add(f, Nat.add(g, e)),
        Equal.sym(Nat, Nat.add(Nat.add(a, d), e), Nat.add(a, Nat.add(d, e)), N.Natural.add_associative(a, d, e)),
        Equal.trans(Nat, Nat.add(Nat.add(a, d), e), Nat.add(Nat.add(f, g), e), Nat.add(f, Nat.add(g, e)),
          Equal.cong(Nat, Nat, z => Nat.add(z, e), Nat.add(a, d), Nat.add(f, g), e1),
          N.Natural.add_associative(f, g, e)))))

# one account: x = carry + w * total splits as q * W + r (e1), and the rest
# of the accounts keep the invariant from carry r (k)
def kept.fin(+total: Nat, +bp: Nat, +w: Nat, +rest: List<&2, Nat>, +carry: Nat,
  e1: {Nat.add(Nat.mul(Nat.div(Nat.add(carry, Nat.mul(w, total)), 1n+bp), 1n+bp), Nat.mod(Nat.add(carry, Nat.mul(w, total)), 1n+bp))
        == Nat.add(carry, Nat.mul(w, total)) : Nat},
  k: Kept(total, bp, rest, Nat.mod(Nat.add(carry, Nat.mul(w, total)), 1n+bp)))
  -> Kept(total, bp, w <> rest, carry):
  (lf, e2) = k
  +x = Nat.add(carry, Nat.mul(w, total))
  +q = Nat.div(x, 1n+bp)
  +r = Nat.mod(x, 1n+bp)
  +s = Alloc.sum(Alloc.go(total, bp, rest, r))
  +rf = final(total, bp, rest, r)
  (lf, Equal.trans(Nat,
    Nat.add(Nat.mul(Nat.add(q, s), 1n+bp), rf),
    Nat.add(Nat.add(Nat.mul(q, 1n+bp), Nat.mul(s, 1n+bp)), rf),
    Nat.add(carry, Nat.mul(Nat.add(w, Alloc.sum(rest)), total)),
    Equal.cong(Nat, Nat, z => Nat.add(z, rf), Nat.mul(Nat.add(q, s), 1n+bp), Nat.add(Nat.mul(q, 1n+bp), Nat.mul(s, 1n+bp)),
      N.Natural.mul_add_left(q, s, 1n+bp)),
    Equal.trans(Nat,
      Nat.add(Nat.add(Nat.mul(q, 1n+bp), Nat.mul(s, 1n+bp)), rf),
      Nat.add(carry, Nat.add(Nat.mul(w, total), Nat.mul(Alloc.sum(rest), total))),
      Nat.add(carry, Nat.mul(Nat.add(w, Alloc.sum(rest)), total)),
      kept.alg(Nat.mul(q, 1n+bp), Nat.mul(s, 1n+bp), rf, r, Nat.mul(Alloc.sum(rest), total), carry, Nat.mul(w, total), e2, e1),
      Equal.cong(Nat, Nat, z => Nat.add(carry, z),
        Nat.add(Nat.mul(w, total), Nat.mul(Alloc.sum(rest), total)), Nat.mul(Nat.add(w, Alloc.sum(rest)), total),
        Equal.sym(Nat, Nat.mul(Nat.add(w, Alloc.sum(rest)), total), Nat.add(Nat.mul(w, total), Nat.mul(Alloc.sum(rest), total)),
          N.Natural.mul_add_left(w, Alloc.sum(rest), total))))))

def kept.step(+total: Nat, +bp: Nat, +w: Nat, +rest: List<&2, Nat>, +carry: Nat,
  d: DivOk(bp, Nat.add(carry, Nat.mul(w, total)), Nat.divmod(Nat.add(carry, Nat.mul(w, total)), 1n+bp)),
  ih: N.Natural.Le(Nat.mod(Nat.add(carry, Nat.mul(w, total)), 1n+bp), bp)
    -> Kept(total, bp, rest, Nat.mod(Nat.add(carry, Nat.mul(w, total)), 1n+bp)))
  -> Kept(total, bp, w <> rest, carry):
  (e1, l1) = d
  kept.fin(total, bp, w, rest, carry, e1, ih(l1))

def kept(+total: Nat, +bp: Nat, +ws: List<&2, Nat>, +carry: Nat, lc: N.Natural.Le(carry, bp)) -> Kept(total, bp, ws, carry):
  match ws:
    case Nil{}:
      (lc, Equal.sym(Nat, Nat.add(carry, 0n), carry, N.Natural.add_zero(carry)))
    case w <> rest:
      +x = Nat.add(carry, Nat.mul(w, total))
      kept.step(total, bp, w, rest, carry, div.spec(x, bp), l => kept(total, bp, rest, Nat.mod(x, 1n+bp), l))

# With carry 0 and W = 1 + bp: S * W + rf == W * total with rf <= bp, so
# S <= total (rf >= 0) and total <= S (rf < W): S == total.
def conserves.fin(+total: Nat, +bp: Nat, +ws: List<&2, Nat>, e: {Alloc.sum(ws) == 1n+bp : Nat}, k: Kept(total, bp, ws, 0n))
  -> {Alloc.sum(Alloc.go(total, bp, ws, 0n)) == total : Nat}:
  (lf, kept_eq) = k
  +s = Alloc.sum(Alloc.go(total, bp, ws, 0n))
  +rf = final(total, bp, ws, 0n)
  +sw = Nat.mul(s, 1n+bp)
  +ws_t = Nat.mul(1n+bp, total)
  +exact: {Nat.add(sw, rf) == ws_t : Nat} =
    Equal.trans(Nat, Nat.add(sw, rf), Nat.mul(Alloc.sum(ws), total), ws_t,
      kept_eq, Equal.cong(Nat, Nat, z => Nat.mul(z, total), Alloc.sum(ws), 1n+bp, e))
  below: N.Natural.Le(s, total) =
    N.Natural.le_of_scaled_le(bp, s, total, 0n,
      N.Natural.le_congruent(sw, Nat.add(sw, rf), Nat.mul(1n+bp, s), Nat.add(ws_t, 0n),
        N.Natural.le_add_right(sw, rf),
        N.Natural.mul_commutative(s, 1n+bp),
        Equal.trans(Nat, Nat.add(sw, rf), ws_t, Nat.add(ws_t, 0n), exact, Equal.sym(Nat, Nat.add(ws_t, 0n), ws_t, N.Natural.add_zero(ws_t)))),
      N.Natural.zero_le(bp))
  above: N.Natural.Le(total, s) =
    N.Natural.le_of_scaled_le(bp, total, s, rf,
      N.Natural.le_congruent(ws_t, ws_t, ws_t, Nat.add(Nat.mul(1n+bp, s), rf),
        N.Natural.le_reflexive(ws_t), {==},
        Equal.trans(Nat, ws_t, Nat.add(sw, rf), Nat.add(Nat.mul(1n+bp, s), rf),
          Equal.sym(Nat, Nat.add(sw, rf), ws_t, exact),
          Equal.cong(Nat, Nat, z => Nat.add(z, rf), sw, Nat.mul(1n+bp, s), N.Natural.mul_commutative(s, 1n+bp)))),
      lf)
  N.Natural.le_antisymmetric(s, total, below, above)

# 0 is not 1 + p: rewrite through a motive that is Empty at 0 and Unit after
def IsSucc(n: Nat) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+p:
      Unit

def zero_ne_succ(-p: Nat, e: {0n == 1n+p : Nat}) -> Empty:
  %Equal.sym(Nat, 0n, 1n+p, e) : IsSucc(_)
  Unit{}

# allocate splits by sum(ws); naming that sum `weight` lets us match on it
def conserves.split(+total: Nat, +ws: List<&2, Nat>, +weight: Nat, -bp: Nat,
  e0: {Alloc.sum(ws) == weight : Nat}, e: {Alloc.sum(ws) == 1n+bp : Nat})
  -> {Alloc.sum(Alloc.split(total, ws, weight)) == total : Nat}:
  match weight:
    case 0n:
      Empty.absurd({Alloc.sum(Alloc.zeros(ws)) == total : Nat},
        zero_ne_succ(bp, Equal.trans(Nat, 0n, Alloc.sum(ws), 1n+bp, Equal.sym(Nat, Alloc.sum(ws), 0n, e0), e)))
    case 1n+wp:
      conserves.fin(total, wp, ws, e0, kept(total, wp, ws, 0n, N.Natural.zero_le(wp)))

def Laws.conserves(total, ws, bp, e):
  conserves.split(total, ws, Alloc.sum(ws), bp, {==}, e)

# Fairness
# --------
# From q * W + r == carry + w * total with carry, r <= bp:
#   q * W <= carry + w * total <= bp + w * total   so q * W < w * total + W
#   w * total <= q * W + r <= q * W + bp           so w * total < q * W + W

def fair.one(+total: Nat, +bp: Nat, +w: Nat, +carry: Nat, +q: Nat, +r: Nat,
  +e1: {Nat.add(Nat.mul(q, 1n+bp), r) == Nat.add(carry, Nat.mul(w, total)) : Nat},
  lc: N.Natural.Le(carry, bp), l1: N.Natural.Le(r, bp))
  -> (Spec.Lt(Nat.mul(q, 1n+bp), Nat.add(Nat.mul(w, total), 1n+bp))
      & Spec.Lt(Nat.mul(w, total), Nat.add(Nat.mul(q, 1n+bp), 1n+bp))):
  +qw = Nat.mul(q, 1n+bp)
  +wt = Nat.mul(w, total)
  # q * W <= bp + w * total, which is 1 + q * W <= (1 + bp) + w * total
  up: N.Natural.Le(qw, Nat.add(bp, wt)) =
    N.Natural.le_transitive(qw, Nat.add(carry, wt), Nat.add(bp, wt),
      N.Natural.le_congruent(qw, Nat.add(qw, r), qw, Nat.add(carry, wt), N.Natural.le_add_right(qw, r), {==}, e1),
      N.Natural.le_add_both_right(carry, bp, wt, lc))
  # w * total <= q * W + bp, which is 1 + w * total <= q * W + (1 + bp)
  down: N.Natural.Le(wt, Nat.add(qw, bp)) =
    N.Natural.le_transitive(wt, Nat.add(qw, r), Nat.add(qw, bp),
      N.Natural.le_congruent(wt, Nat.add(wt, carry), wt, Nat.add(qw, r), N.Natural.le_add_right(wt, carry), {==},
        Equal.trans(Nat, Nat.add(wt, carry), Nat.add(carry, wt), Nat.add(qw, r),
          N.Natural.add_commutative(wt, carry), Equal.sym(Nat, Nat.add(qw, r), Nat.add(carry, wt), e1))),
      N.Natural.le_add_both_left(qw, r, bp, l1))
  (N.Natural.le_congruent(1n+qw, 1n+Nat.add(bp, wt), 1n+qw, Nat.add(wt, 1n+bp), up, {==},
      N.Natural.add_commutative(1n+bp, wt)),
    N.Natural.le_congruent(1n+wt, 1n+Nat.add(qw, bp), 1n+wt, Nat.add(qw, 1n+bp), down, {==},
      Equal.sym(Nat, Nat.add(qw, 1n+bp), 1n+Nat.add(qw, bp), N.Natural.add_successor(qw, bp))))

def fair.step(+total: Nat, +bp: Nat, +w: Nat, +rest: List<&2, Nat>, +carry: Nat, lc: N.Natural.Le(carry, bp),
  d: DivOk(bp, Nat.add(carry, Nat.mul(w, total)), Nat.divmod(Nat.add(carry, Nat.mul(w, total)), 1n+bp)),
  ih: N.Natural.Le(Nat.mod(Nat.add(carry, Nat.mul(w, total)), 1n+bp), bp)
    -> Spec.Fair(total, 1n+bp, rest, Alloc.go(total, bp, rest, Nat.mod(Nat.add(carry, Nat.mul(w, total)), 1n+bp))))
  -> Spec.Fair(total, 1n+bp, w <> rest, Alloc.go(total, bp, w <> rest, carry)):
  (e1, +l1) = d
  +x = Nat.add(carry, Nat.mul(w, total))
  (fair.one(total, bp, w, carry, Nat.div(x, 1n+bp), Nat.mod(x, 1n+bp), e1, lc, l1), ih(l1))

def fair.go(+total: Nat, +bp: Nat, +ws: List<&2, Nat>, +carry: Nat, lc: N.Natural.Le(carry, bp))
  -> Spec.Fair(total, 1n+bp, ws, Alloc.go(total, bp, ws, carry)):
  match ws:
    case Nil{}:
      Unit{}
    case w <> rest:
      +x = Nat.add(carry, Nat.mul(w, total))
      fair.step(total, bp, w, rest, carry, lc, div.spec(x, bp), l => fair.go(total, bp, rest, Nat.mod(x, 1n+bp), l))

# the law's W is 1 + bp; the split's is 1 + wp; the two sums agree, so wp == bp
def fair.split(+total: Nat, +ws: List<&2, Nat>, +weight: Nat, -bp: Nat,
  e0: {Alloc.sum(ws) == weight : Nat}, e: {Alloc.sum(ws) == 1n+bp : Nat})
  -> Spec.Fair(total, 1n+bp, ws, Alloc.split(total, ws, weight)):
  match weight:
    case 0n:
      Empty.absurd(Spec.Fair(total, 1n+bp, ws, Alloc.zeros(ws)),
        zero_ne_succ(bp, Equal.trans(Nat, 0n, Alloc.sum(ws), 1n+bp, Equal.sym(Nat, Alloc.sum(ws), 0n, e0), e)))
    case 1n+wp:
      same: {1n+wp == 1n+bp : Nat} = Equal.trans(Nat, 1n+wp, Alloc.sum(ws), 1n+bp, Equal.sym(Nat, Alloc.sum(ws), 1n+wp, e0), e)
      %same : Spec.Fair(total, _, ws, Alloc.go(total, wp, ws, 0n))
      fair.go(total, wp, ws, 0n, N.Natural.zero_le(wp))

def Laws.fair(total, ws, bp, e):
  fair.split(total, ws, Alloc.sum(ws), bp, {==}, e)

# Zero in, zero out
# -----------------
# With some weight, fairness already forces it: a share s for weight 0 has
# s * W < 0 * total + W, so s * W < W and s is 0. With no weight at all,
# every share is zero anyway.

def zero.one(+total: Nat, +wp: Nat, +w: Nat, +s: Nat,
  lt: Spec.Lt(Nat.mul(s, 1n+wp), Nat.add(Nat.mul(w, total), 1n+wp))) -> Spec.ZeroKept.one(w, s):
  match w:
    case 0n:
      match s:
        case 0n:
          {==}
        case 1n+sp:
          Empty.absurd({1n+sp == 0n : Nat},
            N.Natural.not_successor_le_self(wp,
              N.Natural.le_transitive(1n+wp, 1n+Nat.add(wp, Nat.mul(sp, 1n+wp)), wp,
                N.Natural.le_add_right(1n+wp, Nat.mul(sp, 1n+wp)), lt)))
    case 1n+p:
      Unit{}

def zero.fair(+total: Nat, +wp: Nat, +ws: List<&2, Nat>, +ss: List<&2, Nat>, f: Spec.Fair(total, 1n+wp, ws, ss))
  -> Spec.ZeroKept(ws, ss):
  match ws ss:
    case Nil{} _:
      Unit{}
    case w <> wt Nil{}:
      Unit{}
    case w <> wt s <> st:
      ((lt, gt), rest) = f
      (zero.one(total, wp, w, s, lt), zero.fair(total, wp, wt, st, rest))

def zero.zeros.one(w: Nat) -> Spec.ZeroKept.one(w, 0n):
  match w:
    case 0n:
      {==}
    case 1n+p:
      Unit{}

def zero.zeros(+ws: List<&2, Nat>) -> Spec.ZeroKept(ws, Alloc.zeros(ws)):
  match ws:
    case Nil{}:
      Unit{}
    case w <> rest:
      (zero.zeros.one(w), zero.zeros(rest))

def zero.split(+total: Nat, +ws: List<&2, Nat>, +weight: Nat, e0: {Alloc.sum(ws) == weight : Nat})
  -> Spec.ZeroKept(ws, Alloc.split(total, ws, weight)):
  match weight:
    case 0n:
      zero.zeros(ws)
    case 1n+wp:
      zero.fair(total, wp, ws, Alloc.go(total, wp, ws, 0n), fair.go(total, wp, ws, 0n, N.Natural.zero_le(wp)))

def Laws.zero_weight_gets_zero(total, ws):
  zero.split(total, ws, Alloc.sum(ws), {==})
