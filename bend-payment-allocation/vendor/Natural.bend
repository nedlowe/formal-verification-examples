import Base

def Natural.Le(a: Nat, b: Nat) -> Kind(&2):
  match a b:
    case 0n 0n:
      Unit
    case 0n 1n+bp:
      Unit
    case 1n+ap 0n:
      Empty
    case 1n+ap 1n+bp:
      Natural.Le(ap, bp)

def Natural.le_reflexive(n: Nat) -> Natural.Le(n, n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      Natural.le_reflexive(p)

def Natural.le_total(a: Nat, b: Nat) -> Or(Natural.Le(a, b), Natural.Le(b, a)):
  match a b:
    case 0n 0n:
      Inl{Unit{}}
    case 0n 1n+bp:
      Inl{Unit{}}
    case 1n+ap 0n:
      Inr{Unit{}}
    case 1n+ap 1n+bp:
      Natural.le_total(ap, bp)

def Natural.zero_le(n: Nat) -> Natural.Le(0n, n):
  match n:
    case 0n:
      Unit{}
    case 1n+p:
      Unit{}

def Natural.le_add_right(a: Nat, +b: Nat) -> Natural.Le(a, Nat.add(a, b)):
  match a:
    case 0n:
      Natural.zero_le(b)
    case 1n+p:
      Natural.le_add_right(p, b)

def Natural.le_add_both_left(c: Nat, a: Nat, b: Nat, proof: Natural.Le(a, b)) -> Natural.Le(Nat.add(c, a), Nat.add(c, b)):
  match c:
    case 0n:
      proof
    case 1n+p:
      Natural.le_add_both_left(p, a, b, proof)

def Natural.le_add_left_cancel(c: Nat, a: Nat, b: Nat, proof: Natural.Le(Nat.add(c, a), Nat.add(c, b))) -> Natural.Le(a, b):
  match c:
    case 0n:
      proof
    case 1n+p:
      Natural.le_add_left_cancel(p, a, b, proof)

def Natural.le_transitive(a: Nat, b: Nat, c: Nat, ab: Natural.Le(a, b), bc: Natural.Le(b, c)) -> Natural.Le(a, c):
  match a:
    case 0n:
      match c:
        case 0n:
          Unit{}
        case 1n+cp:
          Unit{}
    case 1n+ap:
      match b:
        case 0n:
          match ab:
        case 1n+bp:
          match c:
            case 0n:
              match bc:
            case 1n+cp:
              Natural.le_transitive(ap, bp, cp, ab, bc)

def Natural.le_antisymmetric(a: Nat, b: Nat, ab: Natural.Le(a, b), ba: Natural.Le(b, a)) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+bp:
      match ba:
    case 1n+ap 0n:
      match ab:
    case 1n+ap 1n+bp:
      Equal.cong(Nat, Nat, z => 1n+z, ap, bp, Natural.le_antisymmetric(ap, bp, ab, ba))

def Natural.le_gap_successor(+a: Nat, +b: Nat, witness: Exists(Nat, gap => {Nat.add(a, gap) == b : Nat})) -> Exists(Nat, gap => {Nat.add(1n+a, gap) == 1n+b : Nat}):
  (gap, equality) = witness
  (gap, Equal.cong(Nat, Nat, z => 1n+z, Nat.add(a, gap), b, equality))

def Natural.le_gap(a: Nat, b: Nat, proof: Natural.Le(a, b)) -> Exists(Nat, gap => {Nat.add(a, gap) == b : Nat}):
  match a b:
    case 0n 0n:
      (0n, {==})
    case 0n 1n+bp:
      (1n+bp, {==})
    case 1n+ap 0n:
      match proof:
    case 1n++ap 1n++bp:
      Natural.le_gap_successor(ap, bp, Natural.le_gap(ap, bp, proof))

def Natural.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, Natural.add_zero(p))

def Natural.add_successor(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), Natural.add_successor(p, b))

def Natural.double_add(n: Nat) -> {Nat.double(n) == Nat.add(n, n) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        Nat.double(1n+p),
        2n+Nat.add(p, p),
        Nat.add(1n+p, 1n+p),
        Equal.cong(Nat, Nat, z => 2n+z, Nat.double(p), Nat.add(p, p), Natural.double_add(p)),
        Equal.sym(Nat,
          Nat.add(1n+p, 1n+p), 2n+Nat.add(p, p),
          Equal.cong(Nat, Nat, z => 1n+z,
            Nat.add(p, 1n+p), 1n+Nat.add(p, p),
            Natural.add_successor(p, p))))

def Natural.successor_double(+p: Nat) -> {2n+Nat.double(p) == Nat.add(1n+p, 1n+p) : Nat}:
  Equal.trans(Nat,
    2n+Nat.double(p), 2n+Nat.add(p, p), Nat.add(1n+p, 1n+p),
    Equal.cong(Nat, Nat, z => 2n+z, Nat.double(p), Nat.add(p, p), Natural.double_add(p)),
    Equal.sym(Nat,
      Nat.add(1n+p, 1n+p), 2n+Nat.add(p, p),
      Equal.cong(Nat, Nat, z => 1n+z,
        Nat.add(p, 1n+p), 1n+Nat.add(p, p),
        Natural.add_successor(p, p))))

def Natural.add_commutative(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, Natural.add_zero(b))
    case 1n++p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), Natural.add_commutative(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), Natural.add_successor(b, p)))

def Natural.add_associative(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), Natural.add_associative(p, b, c))

def Natural.predecessor(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def Natural.successor_injective(+a: Nat, +b: Nat, proof: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  Equal.cong(Nat, Nat, Natural.predecessor, 1n+a, 1n+b, proof)

def Natural.IsZero(n: Nat) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      Empty

def Natural.zero_not_successor(+p: Nat, proof: {0n == 1n+p : Nat}) -> Empty:
  %proof : Natural.IsZero(_)
  Unit{}

def Natural.successor_not_zero(+p: Nat, proof: {1n+p == 0n : Nat}) -> Empty:
  Natural.zero_not_successor(p, Equal.sym(Nat, 1n+p, 0n, proof))

def Natural.add_left_cancel(c: Nat, +a: Nat, +b: Nat, proof: {Nat.add(c, a) == Nat.add(c, b) : Nat}) -> {a == b : Nat}:
  match c:
    case 0n:
      proof
    case 1n++p:
      Natural.add_left_cancel(p, a, b, Natural.successor_injective(Nat.add(p, a), Nat.add(p, b), proof))

def Natural.add_right_cancel(+a: Nat, +b: Nat, +c: Nat, proof: {Nat.add(a, c) == Nat.add(b, c) : Nat}) -> {a == b : Nat}:
  Natural.add_left_cancel(c, a, b,
    Equal.trans(Nat,
      Nat.add(c, a),
      Nat.add(a, c),
      Nat.add(c, b),
      Natural.add_commutative(c, a),
      Equal.trans(Nat,
        Nat.add(a, c),
        Nat.add(b, c),
        Nat.add(c, b),
        proof,
        Equal.sym(Nat, Nat.add(c, b), Nat.add(b, c), Natural.add_commutative(c, b)))))

def Natural.add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat,
    Nat.add(a, Nat.add(b, c)),
    Nat.add(Nat.add(a, b), c),
    Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), Natural.add_associative(a, b, c)),
    Equal.trans(Nat,
      Nat.add(Nat.add(a, b), c),
      Nat.add(Nat.add(b, a), c),
      Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, z => Nat.add(z, c), Nat.add(a, b), Nat.add(b, a), Natural.add_commutative(a, b)),
      Natural.add_associative(b, a, c)))

def Natural.add_middle_commute(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(a, b), Nat.add(c, d)),
    Nat.add(a, Nat.add(b, Nat.add(c, d))),
    Nat.add(Nat.add(a, c), Nat.add(b, d)),
    Natural.add_associative(a, b, Nat.add(c, d)),
    Equal.trans(Nat,
      Nat.add(a, Nat.add(b, Nat.add(c, d))),
      Nat.add(a, Nat.add(c, Nat.add(b, d))),
      Nat.add(Nat.add(a, c), Nat.add(b, d)),
      Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(b, Nat.add(c, d)), Nat.add(c, Nat.add(b, d)), Natural.add_swap(b, c, d)),
      Equal.sym(Nat,
        Nat.add(Nat.add(a, c), Nat.add(b, d)),
        Nat.add(a, Nat.add(c, Nat.add(b, d))),
        Natural.add_associative(a, c, Nat.add(b, d)))))

def Natural.add_last_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(a, b), c),
    Nat.add(a, Nat.add(b, c)),
    Nat.add(Nat.add(a, c), b),
    Natural.add_associative(a, b, c),
    Equal.trans(Nat,
      Nat.add(a, Nat.add(b, c)),
      Nat.add(a, Nat.add(c, b)),
      Nat.add(Nat.add(a, c), b),
      Equal.cong(Nat, Nat, z => Nat.add(a, z), Nat.add(b, c), Nat.add(c, b), Natural.add_commutative(b, c)),
      Equal.sym(Nat,
        Nat.add(Nat.add(a, c), b), Nat.add(a, Nat.add(c, b)),
        Natural.add_associative(a, c, b))))

def Natural.add_four_balance(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, c), Nat.add(b, d)) == Nat.add(Nat.add(b, c), Nat.add(a, d)) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(a, c), Nat.add(b, d)),
    Nat.add(Nat.add(a, b), Nat.add(c, d)),
    Nat.add(Nat.add(b, c), Nat.add(a, d)),
    Natural.add_middle_commute(a, c, b, d),
    Equal.trans(Nat,
      Nat.add(Nat.add(a, b), Nat.add(c, d)),
      Nat.add(Nat.add(b, a), Nat.add(c, d)),
      Nat.add(Nat.add(b, c), Nat.add(a, d)),
      Equal.cong(Nat, Nat, z => Nat.add(z, Nat.add(c, d)), Nat.add(a, b), Nat.add(b, a), Natural.add_commutative(a, b)),
      Natural.add_middle_commute(b, a, c, d)))

def Natural.eq_add_swap(+a: Nat, +b: Nat, +c: Nat, +d: Nat, proof: {Nat.add(b, a) == Nat.add(d, c) : Nat}) -> {Nat.add(a, b) == Nat.add(c, d) : Nat}:
  Equal.trans(Nat,
    Nat.add(a, b),
    Nat.add(b, a),
    Nat.add(c, d),
    Natural.add_commutative(a, b),
    Equal.trans(Nat,
      Nat.add(b, a),
      Nat.add(d, c),
      Nat.add(c, d),
      proof,
      Natural.add_commutative(d, c)))

def Natural.eq_add_congruent(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ac: {a == c : Nat}, bd: {b == d : Nat}) -> {Nat.add(a, b) == Nat.add(c, d) : Nat}:
  Equal.trans(Nat,
    Nat.add(a, b),
    Nat.add(c, b),
    Nat.add(c, d),
    Equal.cong(Nat, Nat, z => Nat.add(z, b), a, c, ac),
    Equal.cong(Nat, Nat, z => Nat.add(c, z), b, d, bd))

def Natural.eq_mul_congruent(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ac: {a == c : Nat}, bd: {b == d : Nat}) -> {Nat.mul(a, b) == Nat.mul(c, d) : Nat}:
  Equal.trans(Nat,
    Nat.mul(a, b), Nat.mul(c, b), Nat.mul(c, d),
    Equal.cong(Nat, Nat, z => Nat.mul(z, b), a, c, ac),
    Equal.cong(Nat, Nat, z => Nat.mul(c, z), b, d, bd))

def Natural.eq_cross_commute(+a: Nat, +b: Nat, +p: Nat, +n: Nat, proof: {a == b : Nat}) ->
  {Nat.add(Nat.mul(a, p), Nat.mul(b, n)) == Nat.add(Nat.mul(b, p), Nat.mul(a, n)) : Nat}:
  %proof : {Nat.add(Nat.mul(a, p), Nat.mul(_, n)) == Nat.add(Nat.mul(_, p), Nat.mul(a, n)) : Nat}
  {==}

def Natural.le_congruent(+a: Nat, +b: Nat, +c: Nat, +d: Nat, proof: Natural.Le(a, b), ac: {a == c : Nat}, bd: {b == d : Nat}) -> Natural.Le(c, d):
  %ac : Natural.Le(_, d)
  %bd : Natural.Le(a, _)
  proof

def Natural.le_both_from_eq(+a: Nat, +b: Nat, equality: {a == b : Nat}) -> Natural.Le(a, b) & Natural.Le(b, a):
  %equality : Natural.Le(a, _) & Natural.Le(_, a)
  (Natural.le_reflexive(a), Natural.le_reflexive(a))

def Natural.le_from_gap(+a: Nat, +b: Nat, +gap: Nat, equality: {Nat.add(a, gap) == b : Nat}) -> Natural.Le(a, b):
  Natural.le_congruent(a, Nat.add(a, gap), a, b, Natural.le_add_right(a, gap), {==}, equality)

def Natural.le_add_both_right(+a: Nat, +b: Nat, +c: Nat, proof: Natural.Le(a, b)) -> Natural.Le(Nat.add(a, c), Nat.add(b, c)):
  Natural.le_congruent(Nat.add(c, a), Nat.add(c, b), Nat.add(a, c), Nat.add(b, c),
    Natural.le_add_both_left(c, a, b, proof),
    Natural.add_commutative(c, a),
    Natural.add_commutative(c, b))

def Natural.le_add_inequalities(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ab: Natural.Le(a, b), cd: Natural.Le(c, d)) -> Natural.Le(Nat.add(a, c), Nat.add(b, d)):
  Natural.le_transitive(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d),
    Natural.le_add_both_right(a, b, c, ab),
    Natural.le_add_both_left(b, c, d, cd))

def Natural.le_balance(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat,
  first: Natural.Le(Nat.add(a, c), Nat.add(b, d)),
  second: Natural.Le(Nat.add(b, e), Nat.add(c, f))) -> Natural.Le(Nat.add(a, e), Nat.add(d, f)):
  Natural.le_add_left_cancel(Nat.add(b, c), Nat.add(a, e), Nat.add(d, f),
    Natural.le_congruent(
      Nat.add(Nat.add(a, c), Nat.add(b, e)),
      Nat.add(Nat.add(b, d), Nat.add(c, f)),
      Nat.add(Nat.add(b, c), Nat.add(a, e)),
      Nat.add(Nat.add(b, c), Nat.add(d, f)),
      Natural.le_add_inequalities(Nat.add(a, c), Nat.add(b, d), Nat.add(b, e), Nat.add(c, f), first, second),
      Natural.add_four_balance(a, b, c, e),
      Natural.add_middle_commute(b, d, c, f)))

def Natural.mul_zero(n: Nat) -> {Nat.mul(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Natural.mul_zero(p)

def Natural.mul_one(n: Nat) -> {Nat.mul(n, 1n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.mul(p, 1n), p, Natural.mul_one(p))

def Natural.one_mul(n: Nat) -> {Nat.mul(1n, n) == n : Nat}:
  Natural.add_zero(n)

def Natural.mul_add_left(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        Nat.add(c, Nat.mul(Nat.add(p, b), c)),
        Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))),
        Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)),
        Equal.cong(Nat, Nat, z => Nat.add(c, z), Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), Natural.mul_add_left(p, b, c)),
        Equal.sym(Nat,
          Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)),
          Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))),
          Natural.add_associative(c, Nat.mul(p, c), Nat.mul(b, c))))

def Natural.mul_successor_right(a: Nat, +b: Nat) -> {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        Nat.add(1n+b, Nat.mul(p, 1n+b)),
        Nat.add(1n+b, Nat.add(p, Nat.mul(p, b))),
        Nat.add(1n+p, Nat.add(b, Nat.mul(p, b))),
        Equal.cong(Nat, Nat, z => Nat.add(1n+b, z), Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), Natural.mul_successor_right(p, b)),
        Equal.cong(Nat, Nat, z => 1n+z, Nat.add(b, Nat.add(p, Nat.mul(p, b))), Nat.add(p, Nat.add(b, Nat.mul(p, b))), Natural.add_swap(b, p, Nat.mul(p, b))))

def Natural.mul_commutative(a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, Natural.mul_zero(b))
    case 1n++p:
      Equal.trans(Nat,
        Nat.add(b, Nat.mul(p, b)),
        Nat.add(b, Nat.mul(b, p)),
        Nat.mul(b, 1n+p),
        Equal.cong(Nat, Nat, z => Nat.add(b, z), Nat.mul(p, b), Nat.mul(b, p), Natural.mul_commutative(p, b)),
        Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), Natural.mul_successor_right(b, p)))

def Natural.mul_associative(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      Equal.trans(Nat,
        Nat.mul(Nat.add(b, Nat.mul(p, b)), c),
        Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)),
        Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))),
        Natural.mul_add_left(b, Nat.mul(p, b), c),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(b, c), z), Nat.mul(Nat.mul(p, b), c), Nat.mul(p, Nat.mul(b, c)), Natural.mul_associative(p, b, c)))

def Natural.mul_last_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(Nat.mul(a, c), b) : Nat}:
  Equal.trans(Nat,
    Nat.mul(Nat.mul(a, b), c),
    Nat.mul(a, Nat.mul(b, c)),
    Nat.mul(Nat.mul(a, c), b),
    Natural.mul_associative(a, b, c),
    Equal.trans(Nat,
      Nat.mul(a, Nat.mul(b, c)),
      Nat.mul(a, Nat.mul(c, b)),
      Nat.mul(Nat.mul(a, c), b),
      Equal.cong(Nat, Nat, z => Nat.mul(a, z), Nat.mul(b, c), Nat.mul(c, b), Natural.mul_commutative(b, c)),
      Equal.sym(Nat,
        Nat.mul(Nat.mul(a, c), b),
        Nat.mul(a, Nat.mul(c, b)),
        Natural.mul_associative(a, c, b))))

def Natural.mul_inner_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(Nat.mul(a, c), b) : Nat}:
  Equal.trans(Nat,
    Nat.mul(a, Nat.mul(b, c)),
    Nat.mul(Nat.mul(a, b), c),
    Nat.mul(Nat.mul(a, c), b),
    Equal.sym(Nat, Nat.mul(Nat.mul(a, b), c), Nat.mul(a, Nat.mul(b, c)), Natural.mul_associative(a, b, c)),
    Natural.mul_last_swap(a, b, c))

def Natural.mul_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(b, Nat.mul(a, c)) : Nat}:
  Equal.trans(Nat,
    Nat.mul(a, Nat.mul(b, c)),
    Nat.mul(Nat.mul(a, b), c),
    Nat.mul(b, Nat.mul(a, c)),
    Equal.sym(Nat,
      Nat.mul(Nat.mul(a, b), c), Nat.mul(a, Nat.mul(b, c)),
      Natural.mul_associative(a, b, c)),
    Equal.trans(Nat,
      Nat.mul(Nat.mul(a, b), c),
      Nat.mul(Nat.mul(b, a), c),
      Nat.mul(b, Nat.mul(a, c)),
      Equal.cong(Nat, Nat, z => Nat.mul(z, c), Nat.mul(a, b), Nat.mul(b, a), Natural.mul_commutative(a, b)),
      Natural.mul_associative(b, a, c)))

def Natural.mul_four_middle_commute(+a: Nat, +b: Nat, +c: Nat, +d: Nat) ->
  {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(Nat.mul(a, c), Nat.mul(b, d)) : Nat}:
  Equal.trans(Nat,
    Nat.mul(Nat.mul(a, b), Nat.mul(c, d)),
    Nat.mul(a, Nat.mul(b, Nat.mul(c, d))),
    Nat.mul(Nat.mul(a, c), Nat.mul(b, d)),
    Natural.mul_associative(a, b, Nat.mul(c, d)),
    Equal.trans(Nat,
      Nat.mul(a, Nat.mul(b, Nat.mul(c, d))),
      Nat.mul(a, Nat.mul(c, Nat.mul(b, d))),
      Nat.mul(Nat.mul(a, c), Nat.mul(b, d)),
      Equal.cong(Nat, Nat, z => Nat.mul(a, z), Nat.mul(b, Nat.mul(c, d)), Nat.mul(c, Nat.mul(b, d)), Natural.mul_swap(b, c, d)),
      Equal.sym(Nat,
        Nat.mul(Nat.mul(a, c), Nat.mul(b, d)),
        Nat.mul(a, Nat.mul(c, Nat.mul(b, d))),
        Natural.mul_associative(a, c, Nat.mul(b, d)))))

def Natural.mul_four_group(+a: Nat, +b: Nat, +c: Nat, +d: Nat) ->
  {Nat.mul(Nat.mul(a, b), Nat.mul(c, d)) == Nat.mul(a, Nat.mul(Nat.mul(b, c), d)) : Nat}:
  Equal.trans(Nat,
    Nat.mul(Nat.mul(a, b), Nat.mul(c, d)),
    Nat.mul(a, Nat.mul(b, Nat.mul(c, d))),
    Nat.mul(a, Nat.mul(Nat.mul(b, c), d)),
    Natural.mul_associative(a, b, Nat.mul(c, d)),
    Equal.cong(Nat, Nat, z => Nat.mul(a, z),
      Nat.mul(b, Nat.mul(c, d)), Nat.mul(Nat.mul(b, c), d),
      Equal.sym(Nat, Nat.mul(Nat.mul(b, c), d), Nat.mul(b, Nat.mul(c, d)), Natural.mul_associative(b, c, d))))

def Natural.fraction_sum_associative(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat) ->
  {Nat.add(Nat.mul(Nat.add(Nat.mul(a, e), Nat.mul(b, d)), f), Nat.mul(c, Nat.mul(d, e))) ==
   Nat.add(Nat.mul(a, Nat.mul(e, f)), Nat.mul(Nat.add(Nat.mul(b, f), Nat.mul(c, e)), d)) : Nat}:
  +ae: Nat = Nat.mul(a, e)
  +bd: Nat = Nat.mul(b, d)
  +bf: Nat = Nat.mul(b, f)
  +ce: Nat = Nat.mul(c, e)
  +af: Nat = Nat.mul(ae, f)
  +bdf: Nat = Nat.mul(bd, f)
  +bfd: Nat = Nat.mul(bf, d)
  +cde: Nat = Nat.mul(c, Nat.mul(d, e))
  +ced: Nat = Nat.mul(ce, d)
  Equal.trans(Nat,
    Nat.add(Nat.mul(Nat.add(ae, bd), f), cde),
    Nat.add(Nat.add(af, bdf), cde),
    Nat.add(Nat.mul(a, Nat.mul(e, f)), Nat.mul(Nat.add(bf, ce), d)),
    Equal.cong(Nat, Nat, z => Nat.add(z, cde),
      Nat.mul(Nat.add(ae, bd), f), Nat.add(af, bdf),
      Natural.mul_add_left(ae, bd, f)),
    Equal.trans(Nat,
      Nat.add(Nat.add(af, bdf), cde),
      Nat.add(Nat.add(af, bdf), ced),
      Nat.add(Nat.mul(a, Nat.mul(e, f)), Nat.mul(Nat.add(bf, ce), d)),
      Equal.cong(Nat, Nat, z => Nat.add(Nat.add(af, bdf), z), cde, ced,
        Equal.trans(Nat,
          cde, Nat.mul(Nat.mul(c, d), e), ced,
          Equal.sym(Nat, Nat.mul(Nat.mul(c, d), e), cde, Natural.mul_associative(c, d, e)),
          Natural.mul_last_swap(c, d, e))),
      Equal.trans(Nat,
        Nat.add(Nat.add(af, bdf), ced),
        Nat.add(Nat.add(af, bfd), ced),
        Nat.add(Nat.mul(a, Nat.mul(e, f)), Nat.mul(Nat.add(bf, ce), d)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.add(af, z), ced), bdf, bfd,
          Natural.mul_last_swap(b, d, f)),
        Equal.trans(Nat,
          Nat.add(Nat.add(af, bfd), ced),
          Nat.add(af, Nat.add(bfd, ced)),
          Nat.add(Nat.mul(a, Nat.mul(e, f)), Nat.mul(Nat.add(bf, ce), d)),
          Natural.add_associative(af, bfd, ced),
          Equal.trans(Nat,
            Nat.add(af, Nat.add(bfd, ced)),
            Nat.add(af, Nat.mul(Nat.add(bf, ce), d)),
            Nat.add(Nat.mul(a, Nat.mul(e, f)), Nat.mul(Nat.add(bf, ce), d)),
            Equal.cong(Nat, Nat, z => Nat.add(af, z), Nat.add(bfd, ced), Nat.mul(Nat.add(bf, ce), d),
              Equal.sym(Nat, Nat.mul(Nat.add(bf, ce), d), Nat.add(bfd, ced), Natural.mul_add_left(bf, ce, d))),
            Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(Nat.add(bf, ce), d)),
              af, Nat.mul(a, Nat.mul(e, f)), Natural.mul_associative(a, e, f)))))))

def Natural.mul_add_right(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  Equal.trans(Nat,
    Nat.mul(a, Nat.add(b, c)),
    Nat.mul(Nat.add(b, c), a),
    Nat.add(Nat.mul(a, b), Nat.mul(a, c)),
    Natural.mul_commutative(a, Nat.add(b, c)),
    Equal.trans(Nat,
      Nat.mul(Nat.add(b, c), a),
      Nat.add(Nat.mul(b, a), Nat.mul(c, a)),
      Nat.add(Nat.mul(a, b), Nat.mul(a, c)),
      Natural.mul_add_left(b, c, a),
      Equal.trans(Nat,
        Nat.add(Nat.mul(b, a), Nat.mul(c, a)),
        Nat.add(Nat.mul(a, b), Nat.mul(c, a)),
        Nat.add(Nat.mul(a, b), Nat.mul(a, c)),
        Equal.cong(Nat, Nat, z => Nat.add(z, Nat.mul(c, a)), Nat.mul(b, a), Nat.mul(a, b), Natural.mul_commutative(b, a)),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.mul(a, b), z), Nat.mul(c, a), Nat.mul(a, c), Natural.mul_commutative(c, a)))))

def Natural.le_mul_right_witness(+a: Nat, +b: Nat, +c: Nat, witness: Exists(Nat, gap => {Nat.add(a, gap) == b : Nat})) -> Natural.Le(Nat.mul(a, c), Nat.mul(b, c)):
  (+gap, equality) = witness
  Natural.le_from_gap(Nat.mul(a, c), Nat.mul(b, c), Nat.mul(gap, c),
    Equal.trans(Nat,
      Nat.add(Nat.mul(a, c), Nat.mul(gap, c)),
      Nat.mul(Nat.add(a, gap), c),
      Nat.mul(b, c),
      Equal.sym(Nat,
        Nat.mul(Nat.add(a, gap), c),
        Nat.add(Nat.mul(a, c), Nat.mul(gap, c)),
        Natural.mul_add_left(a, gap, c)),
      Equal.cong(Nat, Nat, z => Nat.mul(z, c), Nat.add(a, gap), b, equality)))

def Natural.le_mul_right(+a: Nat, +b: Nat, +c: Nat, proof: Natural.Le(a, b)) -> Natural.Le(Nat.mul(a, c), Nat.mul(b, c)):
  Natural.le_mul_right_witness(a, b, c, Natural.le_gap(a, b, proof))

def Natural.le_mul_left(+a: Nat, +b: Nat, +c: Nat, proof: Natural.Le(a, b)) -> Natural.Le(Nat.mul(c, a), Nat.mul(c, b)):
  Natural.le_congruent(Nat.mul(a, c), Nat.mul(b, c), Nat.mul(c, a), Nat.mul(c, b),
    Natural.le_mul_right(a, b, c, proof),
    Natural.mul_commutative(a, c),
    Natural.mul_commutative(b, c))

def Natural.signed_mul_nonnegative_gap(+p: Nat, +n: Nat, +m: Nat, +gap: Nat,
  nonnegative: Natural.Le(n, p)) ->
  Natural.Le(
    Nat.add(Nat.mul(p, m), Nat.mul(n, Nat.add(m, gap))),
    Nat.add(Nat.mul(p, Nat.add(m, gap)), Nat.mul(n, m))):
  +pm: Nat = Nat.mul(p, m)
  +nm: Nat = Nat.mul(n, m)
  +ng: Nat = Nat.mul(n, gap)
  +pg: Nat = Nat.mul(p, gap)
  +common: Nat = Nat.add(pm, nm)
  +left: Nat = Nat.add(pm, Nat.mul(n, Nat.add(m, gap)))
  +right: Nat = Nat.add(Nat.mul(p, Nat.add(m, gap)), nm)
  Natural.le_congruent(Nat.add(common, ng), Nat.add(common, pg), left, right,
    Natural.le_add_both_left(common, ng, pg, Natural.le_mul_right(n, p, gap, nonnegative)),
    Equal.sym(Nat,
      left, Nat.add(common, ng),
      Equal.trans(Nat,
        left, Nat.add(pm, Nat.add(nm, ng)), Nat.add(common, ng),
        Equal.cong(Nat, Nat, z => Nat.add(pm, z),
          Nat.mul(n, Nat.add(m, gap)), Nat.add(nm, ng),
          Natural.mul_add_right(n, m, gap)),
        Equal.sym(Nat,
          Nat.add(common, ng), Nat.add(pm, Nat.add(nm, ng)),
          Natural.add_associative(pm, nm, ng)))),
    Equal.sym(Nat,
      right, Nat.add(common, pg),
      Equal.trans(Nat,
        right, Nat.add(Nat.add(pm, pg), nm), Nat.add(common, pg),
        Equal.cong(Nat, Nat, z => Nat.add(z, nm),
          Nat.mul(p, Nat.add(m, gap)), Nat.add(pm, pg),
          Natural.mul_add_right(p, m, gap)),
        Natural.add_last_swap(pm, pg, nm))))

def Natural.signed_mul_nonnegative_gap_substitute(+p: Nat, +n: Nat, +m: Nat, +q: Nat, +gap: Nat,
  nonnegative: Natural.Le(n, p), equality: {Nat.add(m, gap) == q : Nat}) ->
  Natural.Le(Nat.add(Nat.mul(p, m), Nat.mul(n, q)), Nat.add(Nat.mul(p, q), Nat.mul(n, m))):
  %equality : Natural.Le(Nat.add(Nat.mul(p, m), Nat.mul(n, _)), Nat.add(Nat.mul(p, _), Nat.mul(n, m)))
  Natural.signed_mul_nonnegative_gap(p, n, m, gap, nonnegative)

def Natural.signed_mul_nonnegative_witness(+p: Nat, +n: Nat, +m: Nat, +q: Nat,
  nonnegative: Natural.Le(n, p),
  witness: Exists(Nat, gap => {Nat.add(m, gap) == q : Nat})) ->
  Natural.Le(Nat.add(Nat.mul(p, m), Nat.mul(n, q)), Nat.add(Nat.mul(p, q), Nat.mul(n, m))):
  (gap, equality) = witness
  Natural.signed_mul_nonnegative_gap_substitute(p, n, m, q, gap, nonnegative, equality)

def Natural.signed_mul_nonnegative(+p: Nat, +n: Nat, +q: Nat, +m: Nat,
  pn: Natural.Le(n, p), mq: Natural.Le(m, q)) ->
  Natural.Le(Nat.add(Nat.mul(p, m), Nat.mul(n, q)), Nat.add(Nat.mul(p, q), Nat.mul(n, m))):
  Natural.signed_mul_nonnegative_witness(p, n, m, q, pn, Natural.le_gap(m, q, mq))

def Natural.le_cross_scaled(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +k: Nat, proof: Natural.Le(Nat.add(a, c), Nat.add(b, d))) -> Natural.Le(Nat.add(Nat.mul(a, k), Nat.mul(c, k)), Nat.add(Nat.mul(b, k), Nat.mul(d, k))):
  Natural.le_congruent(Nat.mul(Nat.add(a, c), k), Nat.mul(Nat.add(b, d), k),
    Nat.add(Nat.mul(a, k), Nat.mul(c, k)), Nat.add(Nat.mul(b, k), Nat.mul(d, k)),
    Natural.le_mul_right(Nat.add(a, c), Nat.add(b, d), k, proof),
    Natural.mul_add_left(a, c, k),
    Natural.mul_add_left(b, d, k))

def Natural.signed_product_associative(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat) ->
  {Nat.add(
     Nat.mul(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), e),
     Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(b, c)), f)) ==
   Nat.add(
     Nat.mul(a, Nat.add(Nat.mul(c, e), Nat.mul(d, f))),
     Nat.mul(b, Nat.add(Nat.mul(c, f), Nat.mul(d, e)))) : Nat}:
  +ac: Nat = Nat.mul(a, c)
  +ad: Nat = Nat.mul(a, d)
  +bc: Nat = Nat.mul(b, c)
  +bd: Nat = Nat.mul(b, d)
  +A: Nat = Nat.mul(ac, e)
  +B: Nat = Nat.mul(ad, f)
  +C: Nat = Nat.mul(bc, f)
  +D: Nat = Nat.mul(bd, e)
  +expanded_left: Nat = Nat.add(Nat.add(A, D), Nat.add(B, C))
  +ordered_left: Nat = Nat.add(Nat.add(A, B), Nat.add(C, D))
  +expanded_right: Nat = Nat.add(
    Nat.add(Nat.mul(a, Nat.mul(c, e)), Nat.mul(a, Nat.mul(d, f))),
    Nat.add(Nat.mul(b, Nat.mul(c, f)), Nat.mul(b, Nat.mul(d, e))))
  Equal.trans(Nat,
    Nat.add(Nat.mul(Nat.add(ac, bd), e), Nat.mul(Nat.add(ad, bc), f)),
    expanded_left,
    Nat.add(Nat.mul(a, Nat.add(Nat.mul(c, e), Nat.mul(d, f))), Nat.mul(b, Nat.add(Nat.mul(c, f), Nat.mul(d, e)))),
    Natural.eq_add_congruent(
      Nat.mul(Nat.add(ac, bd), e), Nat.mul(Nat.add(ad, bc), f),
      Nat.add(A, D), Nat.add(B, C),
      Natural.mul_add_left(ac, bd, e), Natural.mul_add_left(ad, bc, f)),
    Equal.trans(Nat,
      expanded_left,
      Nat.add(Nat.add(A, B), Nat.add(D, C)),
      Nat.add(Nat.mul(a, Nat.add(Nat.mul(c, e), Nat.mul(d, f))), Nat.mul(b, Nat.add(Nat.mul(c, f), Nat.mul(d, e)))),
      Natural.add_middle_commute(A, D, B, C),
      Equal.trans(Nat,
        Nat.add(Nat.add(A, B), Nat.add(D, C)),
        ordered_left,
        Nat.add(Nat.mul(a, Nat.add(Nat.mul(c, e), Nat.mul(d, f))), Nat.mul(b, Nat.add(Nat.mul(c, f), Nat.mul(d, e)))),
        Equal.cong(Nat, Nat, z => Nat.add(Nat.add(A, B), z), Nat.add(D, C), Nat.add(C, D), Natural.add_commutative(D, C)),
        Equal.trans(Nat,
          ordered_left,
          expanded_right,
          Nat.add(Nat.mul(a, Nat.add(Nat.mul(c, e), Nat.mul(d, f))), Nat.mul(b, Nat.add(Nat.mul(c, f), Nat.mul(d, e)))),
          Natural.eq_add_congruent(
            Nat.add(A, B), Nat.add(C, D),
            Nat.add(Nat.mul(a, Nat.mul(c, e)), Nat.mul(a, Nat.mul(d, f))),
            Nat.add(Nat.mul(b, Nat.mul(c, f)), Nat.mul(b, Nat.mul(d, e))),
            Natural.eq_add_congruent(A, B, Nat.mul(a, Nat.mul(c, e)), Nat.mul(a, Nat.mul(d, f)),
              Natural.mul_associative(a, c, e), Natural.mul_associative(a, d, f)),
            Natural.eq_add_congruent(C, D, Nat.mul(b, Nat.mul(c, f)), Nat.mul(b, Nat.mul(d, e)),
              Natural.mul_associative(b, c, f), Natural.mul_associative(b, d, e))),
          Natural.eq_add_congruent(
            Nat.add(Nat.mul(a, Nat.mul(c, e)), Nat.mul(a, Nat.mul(d, f))),
            Nat.add(Nat.mul(b, Nat.mul(c, f)), Nat.mul(b, Nat.mul(d, e))),
            Nat.mul(a, Nat.add(Nat.mul(c, e), Nat.mul(d, f))),
            Nat.mul(b, Nat.add(Nat.mul(c, f), Nat.mul(d, e))),
            Equal.sym(Nat,
              Nat.mul(a, Nat.add(Nat.mul(c, e), Nat.mul(d, f))),
              Nat.add(Nat.mul(a, Nat.mul(c, e)), Nat.mul(a, Nat.mul(d, f))),
              Natural.mul_add_right(a, Nat.mul(c, e), Nat.mul(d, f))),
            Equal.sym(Nat,
              Nat.mul(b, Nat.add(Nat.mul(c, f), Nat.mul(d, e))),
              Nat.add(Nat.mul(b, Nat.mul(c, f)), Nat.mul(b, Nat.mul(d, e))),
              Natural.mul_add_right(b, Nat.mul(c, f), Nat.mul(d, e))))))))

def Natural.cross_shift_expansion(+a: Nat, +c: Nat, +b: Nat, +d: Nat, +u: Nat, +v: Nat, +k: Nat) ->
  {Nat.add(
     Nat.mul(Nat.add(Nat.mul(a, k), Nat.mul(u, b)), Nat.mul(d, k)),
     Nat.mul(Nat.add(Nat.mul(c, k), Nat.mul(v, d)), Nat.mul(b, k))) ==
   Nat.add(
     Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(c, b)), Nat.mul(k, k)),
     Nat.mul(Nat.add(u, v), Nat.mul(Nat.mul(b, d), k))) : Nat}:
  +ak: Nat = Nat.mul(a, k)
  +ck: Nat = Nat.mul(c, k)
  +ub: Nat = Nat.mul(u, b)
  +vd: Nat = Nat.mul(v, d)
  +dk: Nat = Nat.mul(d, k)
  +bk: Nat = Nat.mul(b, k)
  +kk: Nat = Nat.mul(k, k)
  +common: Nat = Nat.mul(Nat.mul(b, d), k)
  +t1: Nat = Nat.mul(ak, dk)
  +t2: Nat = Nat.mul(ub, dk)
  +t3: Nat = Nat.mul(ck, bk)
  +t4: Nat = Nat.mul(vd, bk)
  +n1: Nat = Nat.mul(Nat.mul(a, d), kk)
  +n2: Nat = Nat.mul(u, common)
  +n3: Nat = Nat.mul(Nat.mul(c, b), kk)
  +n4: Nat = Nat.mul(v, common)
  +left: Nat = Nat.add(Nat.mul(Nat.add(ak, ub), dk), Nat.mul(Nat.add(ck, vd), bk))
  +expanded: Nat = Nat.add(Nat.add(t1, t2), Nat.add(t3, t4))
  +grouped: Nat = Nat.add(Nat.add(t1, t3), Nat.add(t2, t4))
  +normalized: Nat = Nat.add(Nat.add(n1, n3), Nat.add(n2, n4))
  +right: Nat = Nat.add(Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(c, b)), kk), Nat.mul(Nat.add(u, v), common))
  Equal.trans(Nat,
    left, expanded, right,
    Natural.eq_add_congruent(
      Nat.mul(Nat.add(ak, ub), dk), Nat.mul(Nat.add(ck, vd), bk),
      Nat.add(t1, t2), Nat.add(t3, t4),
      Natural.mul_add_left(ak, ub, dk), Natural.mul_add_left(ck, vd, bk)),
    Equal.trans(Nat,
      expanded, grouped, right,
      Natural.add_middle_commute(t1, t2, t3, t4),
      Equal.trans(Nat,
        grouped, normalized, right,
        Natural.eq_add_congruent(
          Nat.add(t1, t3), Nat.add(t2, t4),
          Nat.add(n1, n3), Nat.add(n2, n4),
          Natural.eq_add_congruent(t1, t3, n1, n3,
            Natural.mul_four_middle_commute(a, k, d, k),
            Natural.mul_four_middle_commute(c, k, b, k)),
          Natural.eq_add_congruent(t2, t4, n2, n4,
            Natural.mul_four_group(u, b, d, k),
            Equal.trans(Nat,
              t4, Nat.mul(Nat.mul(v, b), dk), n4,
              Natural.mul_four_middle_commute(v, d, b, k),
              Natural.mul_four_group(v, b, d, k)))),
        Natural.eq_add_congruent(
          Nat.add(n1, n3), Nat.add(n2, n4),
          Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(c, b)), kk),
          Nat.mul(Nat.add(u, v), common),
          Equal.sym(Nat,
            Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(c, b)), kk),
            Nat.add(n1, n3),
            Natural.mul_add_left(Nat.mul(a, d), Nat.mul(c, b), kk)),
          Equal.sym(Nat,
            Nat.mul(Nat.add(u, v), common), Nat.add(n2, n4),
            Natural.mul_add_left(u, v, common))))))

def Natural.cross_shift_monotone(+a: Nat, +c: Nat, +b: Nat, +d: Nat,
  +e: Nat, +f: Nat, +u: Nat, +v: Nat, +k: Nat,
  proof: Natural.Le(Nat.add(Nat.mul(a, d), Nat.mul(c, b)), Nat.add(Nat.mul(e, b), Nat.mul(f, d)))) ->
  Natural.Le(
    Nat.add(Nat.mul(Nat.add(Nat.mul(a, k), Nat.mul(u, b)), Nat.mul(d, k)),
      Nat.mul(Nat.add(Nat.mul(c, k), Nat.mul(v, d)), Nat.mul(b, k))),
    Nat.add(Nat.mul(Nat.add(Nat.mul(e, k), Nat.mul(u, d)), Nat.mul(b, k)),
      Nat.mul(Nat.add(Nat.mul(f, k), Nat.mul(v, b)), Nat.mul(d, k)))):
  +left_base: Nat = Nat.add(Nat.mul(a, d), Nat.mul(c, b))
  +right_base: Nat = Nat.add(Nat.mul(e, b), Nat.mul(f, d))
  +square: Nat = Nat.mul(k, k)
  +common_left: Nat = Nat.mul(Nat.add(u, v), Nat.mul(Nat.mul(b, d), k))
  +common_right: Nat = Nat.mul(Nat.add(u, v), Nat.mul(Nat.mul(d, b), k))
  +left_normalized: Nat = Nat.add(Nat.mul(left_base, square), common_left)
  +right_normalized: Nat = Nat.add(Nat.mul(right_base, square), common_right)
  +left_shift: Nat = Nat.add(
    Nat.mul(Nat.add(Nat.mul(a, k), Nat.mul(u, b)), Nat.mul(d, k)),
    Nat.mul(Nat.add(Nat.mul(c, k), Nat.mul(v, d)), Nat.mul(b, k)))
  +right_shift: Nat = Nat.add(
    Nat.mul(Nat.add(Nat.mul(e, k), Nat.mul(u, d)), Nat.mul(b, k)),
    Nat.mul(Nat.add(Nat.mul(f, k), Nat.mul(v, b)), Nat.mul(d, k)))
  Natural.le_congruent(
    left_normalized,
    Nat.add(Nat.mul(right_base, square), common_left),
    left_shift, right_shift,
    Natural.le_add_both_right(
      Nat.mul(left_base, square), Nat.mul(right_base, square), common_left,
      Natural.le_mul_right(left_base, right_base, square, proof)),
    Equal.sym(Nat, left_shift, left_normalized, Natural.cross_shift_expansion(a, c, b, d, u, v, k)),
    Equal.trans(Nat,
      Nat.add(Nat.mul(right_base, square), common_left),
      right_normalized,
      right_shift,
      Natural.eq_add_congruent(
        Nat.mul(right_base, square), common_left,
        Nat.mul(right_base, square), common_right,
        {==},
        Equal.cong(Nat, Nat,
          z => Nat.mul(Nat.add(u, v), Nat.mul(z, k)),
          Nat.mul(b, d), Nat.mul(d, b),
          Natural.mul_commutative(b, d))),
      Equal.sym(Nat, right_shift, right_normalized,
        Natural.cross_shift_expansion(e, f, d, b, u, v, k))))

def Natural.cross_mul_expansion(+a: Nat, +b: Nat, +c: Nat, +e: Nat, +d: Nat, +f: Nat, +u: Nat, +v: Nat) ->
  {Nat.add(
     Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, v)), d),
     Nat.mul(Nat.add(Nat.mul(c, v), Nat.mul(e, u)), f)) ==
   Nat.add(
     Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(e, f)), u),
     Nat.mul(Nat.add(Nat.mul(b, d), Nat.mul(c, f)), v)) : Nat}:
  +au: Nat = Nat.mul(a, u)
  +bv: Nat = Nat.mul(b, v)
  +cv: Nat = Nat.mul(c, v)
  +eu: Nat = Nat.mul(e, u)
  +t1: Nat = Nat.mul(au, d)
  +t2: Nat = Nat.mul(bv, d)
  +t3: Nat = Nat.mul(cv, f)
  +t4: Nat = Nat.mul(eu, f)
  +n1: Nat = Nat.mul(Nat.mul(a, d), u)
  +n2: Nat = Nat.mul(Nat.mul(b, d), v)
  +n3: Nat = Nat.mul(Nat.mul(c, f), v)
  +n4: Nat = Nat.mul(Nat.mul(e, f), u)
  +left: Nat = Nat.add(Nat.mul(Nat.add(au, bv), d), Nat.mul(Nat.add(cv, eu), f))
  +expanded: Nat = Nat.add(Nat.add(t1, t2), Nat.add(t3, t4))
  +grouped: Nat = Nat.add(Nat.add(t1, t4), Nat.add(t2, t3))
  +normalized: Nat = Nat.add(Nat.add(n1, n4), Nat.add(n2, n3))
  +right: Nat = Nat.add(Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(e, f)), u), Nat.mul(Nat.add(Nat.mul(b, d), Nat.mul(c, f)), v))
  Equal.trans(Nat,
    left, expanded, right,
    Natural.eq_add_congruent(
      Nat.mul(Nat.add(au, bv), d), Nat.mul(Nat.add(cv, eu), f),
      Nat.add(t1, t2), Nat.add(t3, t4),
      Natural.mul_add_left(au, bv, d), Natural.mul_add_left(cv, eu, f)),
    Equal.trans(Nat,
      expanded,
      Nat.add(Nat.add(t1, t2), Nat.add(t4, t3)),
      right,
      Equal.cong(Nat, Nat, z => Nat.add(Nat.add(t1, t2), z),
        Nat.add(t3, t4), Nat.add(t4, t3), Natural.add_commutative(t3, t4)),
      Equal.trans(Nat,
        Nat.add(Nat.add(t1, t2), Nat.add(t4, t3)),
        grouped, right,
        Natural.add_middle_commute(t1, t2, t4, t3),
        Equal.trans(Nat,
          grouped, normalized, right,
          Natural.eq_add_congruent(
            Nat.add(t1, t4), Nat.add(t2, t3),
            Nat.add(n1, n4), Nat.add(n2, n3),
            Natural.eq_add_congruent(t1, t4, n1, n4,
              Natural.mul_last_swap(a, u, d), Natural.mul_last_swap(e, u, f)),
            Natural.eq_add_congruent(t2, t3, n2, n3,
              Natural.mul_last_swap(b, v, d), Natural.mul_last_swap(c, v, f))),
          Natural.eq_add_congruent(
            Nat.add(n1, n4), Nat.add(n2, n3),
            Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(e, f)), u),
            Nat.mul(Nat.add(Nat.mul(b, d), Nat.mul(c, f)), v),
            Equal.sym(Nat,
              Nat.mul(Nat.add(Nat.mul(a, d), Nat.mul(e, f)), u),
              Nat.add(n1, n4),
              Natural.mul_add_left(Nat.mul(a, d), Nat.mul(e, f), u)),
            Equal.sym(Nat,
              Nat.mul(Nat.add(Nat.mul(b, d), Nat.mul(c, f)), v),
              Nat.add(n2, n3),
              Natural.mul_add_left(Nat.mul(b, d), Nat.mul(c, f), v)))))))

def Natural.cross_mul_respects_eq(+a: Nat, +b: Nat, +c: Nat, +e: Nat, +d: Nat, +f: Nat, +u: Nat, +v: Nat,
  proof: {Nat.add(Nat.mul(a, d), Nat.mul(e, f)) == Nat.add(Nat.mul(c, f), Nat.mul(b, d)) : Nat}) ->
  {Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, v)), d), Nat.mul(Nat.add(Nat.mul(c, v), Nat.mul(e, u)), f)) ==
   Nat.add(Nat.mul(Nat.add(Nat.mul(c, u), Nat.mul(e, v)), f), Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, u)), d)) : Nat}:
  +A: Nat = Nat.add(Nat.mul(a, d), Nat.mul(e, f))
  +B: Nat = Nat.add(Nat.mul(c, f), Nat.mul(b, d))
  +left: Nat = Nat.add(Nat.mul(Nat.add(Nat.mul(a, u), Nat.mul(b, v)), d), Nat.mul(Nat.add(Nat.mul(c, v), Nat.mul(e, u)), f))
  +right: Nat = Nat.add(Nat.mul(Nat.add(Nat.mul(c, u), Nat.mul(e, v)), f), Nat.mul(Nat.add(Nat.mul(a, v), Nat.mul(b, u)), d))
  +left_expanded: Nat = Nat.add(Nat.mul(A, u), Nat.mul(Nat.add(Nat.mul(b, d), Nat.mul(c, f)), v))
  +right_expanded: Nat = Nat.add(Nat.mul(B, u), Nat.mul(Nat.add(Nat.mul(e, f), Nat.mul(a, d)), v))
  +left_canonical: Nat = Nat.add(Nat.mul(A, u), Nat.mul(B, v))
  +right_canonical: Nat = Nat.add(Nat.mul(B, u), Nat.mul(A, v))
  Equal.trans(Nat,
    left, left_expanded, right,
    Natural.cross_mul_expansion(a, b, c, e, d, f, u, v),
    Equal.trans(Nat,
      left_expanded, left_canonical, right,
      Natural.eq_add_congruent(
        Nat.mul(A, u), Nat.mul(Nat.add(Nat.mul(b, d), Nat.mul(c, f)), v),
        Nat.mul(A, u), Nat.mul(B, v),
        {==},
        Equal.cong(Nat, Nat, z => Nat.mul(z, v),
          Nat.add(Nat.mul(b, d), Nat.mul(c, f)), B,
          Natural.add_commutative(Nat.mul(b, d), Nat.mul(c, f)))),
      Equal.trans(Nat,
        left_canonical, right_canonical, right,
        Natural.eq_cross_commute(A, B, u, v, proof),
        Equal.trans(Nat,
          right_canonical, right_expanded, right,
          Natural.eq_add_congruent(
            Nat.mul(B, u), Nat.mul(A, v),
            Nat.mul(B, u), Nat.mul(Nat.add(Nat.mul(e, f), Nat.mul(a, d)), v),
            {==},
            Equal.cong(Nat, Nat, z => Nat.mul(z, v),
              A, Nat.add(Nat.mul(e, f), Nat.mul(a, d)),
              Natural.add_commutative(Nat.mul(a, d), Nat.mul(e, f)))),
          Equal.sym(Nat, right, right_expanded,
            Natural.cross_mul_expansion(c, e, a, b, f, d, u, v))))))

def Natural.sum_mul_associative(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +k: Nat) ->
  {Nat.add(Nat.mul(a, Nat.mul(b, k)), Nat.mul(c, Nat.mul(d, k))) ==
   Nat.mul(Nat.add(Nat.mul(a, b), Nat.mul(c, d)), k) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.mul(a, Nat.mul(b, k)), Nat.mul(c, Nat.mul(d, k))),
    Nat.add(Nat.mul(Nat.mul(a, b), k), Nat.mul(Nat.mul(c, d), k)),
    Nat.mul(Nat.add(Nat.mul(a, b), Nat.mul(c, d)), k),
    Natural.eq_add_congruent(
      Nat.mul(a, Nat.mul(b, k)), Nat.mul(c, Nat.mul(d, k)),
      Nat.mul(Nat.mul(a, b), k), Nat.mul(Nat.mul(c, d), k),
      Equal.sym(Nat, Nat.mul(Nat.mul(a, b), k), Nat.mul(a, Nat.mul(b, k)), Natural.mul_associative(a, b, k)),
      Equal.sym(Nat, Nat.mul(Nat.mul(c, d), k), Nat.mul(c, Nat.mul(d, k)), Natural.mul_associative(c, d, k))),
    Equal.sym(Nat,
      Nat.mul(Nat.add(Nat.mul(a, b), Nat.mul(c, d)), k),
      Nat.add(Nat.mul(Nat.mul(a, b), k), Nat.mul(Nat.mul(c, d), k)),
      Natural.mul_add_left(Nat.mul(a, b), Nat.mul(c, d), k)))

def Natural.matrix_distributive(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, +k: Nat, +j: Nat) ->
  {Nat.add(
     Nat.mul(a, Nat.add(Nat.mul(c, k), Nat.mul(e, j))),
     Nat.mul(b, Nat.add(Nat.mul(d, k), Nat.mul(f, j)))) ==
   Nat.add(
     Nat.mul(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), k),
     Nat.mul(Nat.add(Nat.mul(a, e), Nat.mul(b, f)), j)) : Nat}:
  +ack: Nat = Nat.mul(a, Nat.mul(c, k))
  +aej: Nat = Nat.mul(a, Nat.mul(e, j))
  +bdk: Nat = Nat.mul(b, Nat.mul(d, k))
  +bfj: Nat = Nat.mul(b, Nat.mul(f, j))
  +left: Nat = Nat.add(Nat.mul(a, Nat.add(Nat.mul(c, k), Nat.mul(e, j))), Nat.mul(b, Nat.add(Nat.mul(d, k), Nat.mul(f, j))))
  +expanded: Nat = Nat.add(Nat.add(ack, aej), Nat.add(bdk, bfj))
  +grouped: Nat = Nat.add(Nat.add(ack, bdk), Nat.add(aej, bfj))
  +right: Nat = Nat.add(Nat.mul(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), k), Nat.mul(Nat.add(Nat.mul(a, e), Nat.mul(b, f)), j))
  Equal.trans(Nat,
    left, expanded, right,
    Natural.eq_add_congruent(
      Nat.mul(a, Nat.add(Nat.mul(c, k), Nat.mul(e, j))),
      Nat.mul(b, Nat.add(Nat.mul(d, k), Nat.mul(f, j))),
      Nat.add(ack, aej), Nat.add(bdk, bfj),
      Natural.mul_add_right(a, Nat.mul(c, k), Nat.mul(e, j)),
      Natural.mul_add_right(b, Nat.mul(d, k), Nat.mul(f, j))),
    Equal.trans(Nat,
      expanded, grouped, right,
      Natural.add_middle_commute(ack, aej, bdk, bfj),
      Equal.trans(Nat,
        grouped,
        Nat.add(
          Nat.add(Nat.mul(Nat.mul(a, c), k), Nat.mul(Nat.mul(b, d), k)),
          Nat.add(Nat.mul(Nat.mul(a, e), j), Nat.mul(Nat.mul(b, f), j))),
        right,
        Natural.eq_add_congruent(
          Nat.add(ack, bdk), Nat.add(aej, bfj),
          Nat.add(Nat.mul(Nat.mul(a, c), k), Nat.mul(Nat.mul(b, d), k)),
          Nat.add(Nat.mul(Nat.mul(a, e), j), Nat.mul(Nat.mul(b, f), j)),
          Natural.eq_add_congruent(ack, bdk, Nat.mul(Nat.mul(a, c), k), Nat.mul(Nat.mul(b, d), k),
            Equal.sym(Nat, Nat.mul(Nat.mul(a, c), k), ack, Natural.mul_associative(a, c, k)),
            Equal.sym(Nat, Nat.mul(Nat.mul(b, d), k), bdk, Natural.mul_associative(b, d, k))),
          Natural.eq_add_congruent(aej, bfj, Nat.mul(Nat.mul(a, e), j), Nat.mul(Nat.mul(b, f), j),
            Equal.sym(Nat, Nat.mul(Nat.mul(a, e), j), aej, Natural.mul_associative(a, e, j)),
            Equal.sym(Nat, Nat.mul(Nat.mul(b, f), j), bfj, Natural.mul_associative(b, f, j)))),
        Natural.eq_add_congruent(
          Nat.add(Nat.mul(Nat.mul(a, c), k), Nat.mul(Nat.mul(b, d), k)),
          Nat.add(Nat.mul(Nat.mul(a, e), j), Nat.mul(Nat.mul(b, f), j)),
          Nat.mul(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), k),
          Nat.mul(Nat.add(Nat.mul(a, e), Nat.mul(b, f)), j),
          Equal.sym(Nat,
            Nat.mul(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), k),
            Nat.add(Nat.mul(Nat.mul(a, c), k), Nat.mul(Nat.mul(b, d), k)),
            Natural.mul_add_left(Nat.mul(a, c), Nat.mul(b, d), k)),
          Equal.sym(Nat,
            Nat.mul(Nat.add(Nat.mul(a, e), Nat.mul(b, f)), j),
            Nat.add(Nat.mul(Nat.mul(a, e), j), Nat.mul(Nat.mul(b, f), j)),
            Natural.mul_add_left(Nat.mul(a, e), Nat.mul(b, f), j))))))

def Natural.matrix_distributive_scaled(+a: Nat, +b: Nat, +c: Nat, +d: Nat, +e: Nat, +f: Nat, +k: Nat, +j: Nat, +h: Nat) ->
  {Nat.mul(Nat.add(
     Nat.mul(a, Nat.add(Nat.mul(c, k), Nat.mul(e, j))),
     Nat.mul(b, Nat.add(Nat.mul(d, k), Nat.mul(f, j)))), h) ==
   Nat.add(
     Nat.mul(Nat.add(Nat.mul(a, c), Nat.mul(b, d)), Nat.mul(h, k)),
     Nat.mul(Nat.add(Nat.mul(a, e), Nat.mul(b, f)), Nat.mul(h, j))) : Nat}:
  +left_inner: Nat = Nat.add(
    Nat.mul(a, Nat.add(Nat.mul(c, k), Nat.mul(e, j))),
    Nat.mul(b, Nat.add(Nat.mul(d, k), Nat.mul(f, j))))
  +first: Nat = Nat.add(Nat.mul(a, c), Nat.mul(b, d))
  +second: Nat = Nat.add(Nat.mul(a, e), Nat.mul(b, f))
  Equal.trans(Nat,
    Nat.mul(left_inner, h),
    Nat.mul(Nat.add(Nat.mul(first, k), Nat.mul(second, j)), h),
    Nat.add(Nat.mul(first, Nat.mul(h, k)), Nat.mul(second, Nat.mul(h, j))),
    Equal.cong(Nat, Nat, z => Nat.mul(z, h),
      left_inner, Nat.add(Nat.mul(first, k), Nat.mul(second, j)),
      Natural.matrix_distributive(a, b, c, d, e, f, k, j)),
    Equal.trans(Nat,
      Nat.mul(Nat.add(Nat.mul(first, k), Nat.mul(second, j)), h),
      Nat.add(Nat.mul(Nat.mul(first, k), h), Nat.mul(Nat.mul(second, j), h)),
      Nat.add(Nat.mul(first, Nat.mul(h, k)), Nat.mul(second, Nat.mul(h, j))),
      Natural.mul_add_left(Nat.mul(first, k), Nat.mul(second, j), h),
      Natural.eq_add_congruent(
        Nat.mul(Nat.mul(first, k), h), Nat.mul(Nat.mul(second, j), h),
        Nat.mul(first, Nat.mul(h, k)), Nat.mul(second, Nat.mul(h, j)),
        Equal.sym(Nat, Nat.mul(first, Nat.mul(h, k)), Nat.mul(Nat.mul(first, k), h), Natural.mul_inner_swap(first, h, k)),
        Equal.sym(Nat, Nat.mul(second, Nat.mul(h, j)), Nat.mul(Nat.mul(second, j), h), Natural.mul_inner_swap(second, h, j)))))

def Natural.mul_gap_one(+p: Nat, +n: Nat, +d: Nat, +gap: Nat, proof: {p == Nat.add(n, gap) : Nat}) ->
  {Nat.mul(p, d) == Nat.add(Nat.mul(d, gap), Nat.mul(n, d)) : Nat}:
  Equal.trans(Nat,
    Nat.mul(p, d), Nat.mul(Nat.add(n, gap), d), Nat.add(Nat.mul(d, gap), Nat.mul(n, d)),
    Equal.cong(Nat, Nat, z => Nat.mul(z, d), p, Nat.add(n, gap), proof),
    Equal.trans(Nat,
      Nat.mul(Nat.add(n, gap), d),
      Nat.add(Nat.mul(n, d), Nat.mul(gap, d)),
      Nat.add(Nat.mul(d, gap), Nat.mul(n, d)),
      Natural.mul_add_left(n, gap, d),
      Equal.trans(Nat,
        Nat.add(Nat.mul(n, d), Nat.mul(gap, d)),
        Nat.add(Nat.mul(n, d), Nat.mul(d, gap)),
        Nat.add(Nat.mul(d, gap), Nat.mul(n, d)),
        Natural.eq_add_congruent(
          Nat.mul(n, d), Nat.mul(gap, d), Nat.mul(n, d), Nat.mul(d, gap),
          {==}, Natural.mul_commutative(gap, d)),
        Natural.add_commutative(Nat.mul(n, d), Nat.mul(d, gap)))))

def Natural.positive_gap_not_equal(+p: Nat, +n: Nat, +k: Nat,
  gap: {p == Nat.add(n, 1n+k) : Nat}, equal: {p == n : Nat}) -> Empty:
  Natural.successor_not_zero(k,
    Natural.add_left_cancel(n, 1n+k, 0n,
      Equal.trans(Nat,
        Nat.add(n, 1n+k), p, Nat.add(n, 0n),
        Equal.sym(Nat, p, Nat.add(n, 1n+k), gap),
        Equal.trans(Nat,
          p, n, Nat.add(n, 0n),
          equal,
          Equal.sym(Nat, Nat.add(n, 0n), n, Natural.add_zero(n))))))

def Natural.le_mul_right_cancel_positive(+k: Nat, a: Nat, b: Nat, proof: Natural.Le(Nat.mul(a, 1n+k), Nat.mul(b, 1n+k))) -> Natural.Le(a, b):
  match a b:
    case 0n 0n:
      Unit{}
    case 0n 1n+bp:
      Unit{}
    case 1n+ap 0n:
      match proof:
    case 1n++ap 1n++bp:
      Natural.le_mul_right_cancel_positive(k, ap, bp,
        Natural.le_add_left_cancel(1n+k, Nat.mul(ap, 1n+k), Nat.mul(bp, 1n+k), proof))

def Natural.le_mul_left_cancel_positive(+k: Nat, +a: Nat, +b: Nat, proof: Natural.Le(Nat.mul(1n+k, a), Nat.mul(1n+k, b))) -> Natural.Le(a, b):
  Natural.le_mul_right_cancel_positive(k, a, b,
    Natural.le_congruent(Nat.mul(1n+k, a), Nat.mul(1n+k, b), Nat.mul(a, 1n+k), Nat.mul(b, 1n+k),
      proof,
      Natural.mul_commutative(1n+k, a),
      Natural.mul_commutative(1n+k, b)))

def Natural.mul_right_cancel_positive(+k: Nat, a: Nat, b: Nat, proof: {Nat.mul(a, 1n+k) == Nat.mul(b, 1n+k) : Nat}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n++bp:
      Empty.absurd({0n == 1n+bp : Nat}, Natural.zero_not_successor(Nat.add(k, Nat.mul(bp, 1n+k)), proof))
    case 1n++ap 0n:
      Empty.absurd({1n+ap == 0n : Nat}, Natural.successor_not_zero(Nat.add(k, Nat.mul(ap, 1n+k)), proof))
    case 1n++ap 1n++bp:
      Equal.cong(Nat, Nat, z => 1n+z, ap, bp,
        Natural.mul_right_cancel_positive(k, ap, bp,
          Natural.add_left_cancel(1n+k, Nat.mul(ap, 1n+k), Nat.mul(bp, 1n+k), proof)))

def Natural.mul_left_cancel_positive(+k: Nat, +a: Nat, +b: Nat, proof: {Nat.mul(1n+k, a) == Nat.mul(1n+k, b) : Nat}) -> {a == b : Nat}:
  Natural.mul_right_cancel_positive(k, a, b,
    Equal.trans(Nat,
      Nat.mul(a, 1n+k),
      Nat.mul(1n+k, a),
      Nat.mul(b, 1n+k),
      Natural.mul_commutative(a, 1n+k),
      Equal.trans(Nat,
        Nat.mul(1n+k, a),
        Nat.mul(1n+k, b),
        Nat.mul(b, 1n+k),
        proof,
        Natural.mul_commutative(1n+k, b))))

def Natural.two_unit_cross(+half_denominator: Nat, +whole_denominator: Nat,
  equality: {half_denominator == Nat.add(whole_denominator, whole_denominator) : Nat}) ->
  {Nat.mul(Nat.add(Nat.mul(1n, half_denominator), Nat.mul(1n, half_denominator)), whole_denominator) ==
   Nat.mul(1n, Nat.mul(half_denominator, half_denominator)) : Nat}:
  +twice_half: Nat = Nat.add(half_denominator, half_denominator)
  +twice_whole: Nat = Nat.add(whole_denominator, whole_denominator)
  Equal.trans(Nat,
    Nat.mul(Nat.add(Nat.mul(1n, half_denominator), Nat.mul(1n, half_denominator)), whole_denominator),
    Nat.mul(twice_half, whole_denominator),
    Nat.mul(1n, Nat.mul(half_denominator, half_denominator)),
    Equal.cong(Nat, Nat, z => Nat.mul(z, whole_denominator),
      Nat.add(Nat.mul(1n, half_denominator), Nat.mul(1n, half_denominator)), twice_half,
      Natural.eq_add_congruent(
        Nat.mul(1n, half_denominator), Nat.mul(1n, half_denominator),
        half_denominator, half_denominator,
        Natural.one_mul(half_denominator), Natural.one_mul(half_denominator))),
    Equal.trans(Nat,
      Nat.mul(twice_half, whole_denominator),
      Nat.add(Nat.mul(half_denominator, whole_denominator), Nat.mul(half_denominator, whole_denominator)),
      Nat.mul(1n, Nat.mul(half_denominator, half_denominator)),
      Natural.mul_add_left(half_denominator, half_denominator, whole_denominator),
      Equal.trans(Nat,
        Nat.add(Nat.mul(half_denominator, whole_denominator), Nat.mul(half_denominator, whole_denominator)),
        Nat.mul(half_denominator, twice_whole),
        Nat.mul(1n, Nat.mul(half_denominator, half_denominator)),
        Equal.sym(Nat,
          Nat.mul(half_denominator, twice_whole),
          Nat.add(Nat.mul(half_denominator, whole_denominator), Nat.mul(half_denominator, whole_denominator)),
          Natural.mul_add_right(half_denominator, whole_denominator, whole_denominator)),
        Equal.trans(Nat,
          Nat.mul(half_denominator, twice_whole),
          Nat.mul(half_denominator, half_denominator),
          Nat.mul(1n, Nat.mul(half_denominator, half_denominator)),
          Equal.cong(Nat, Nat, z => Nat.mul(half_denominator, z), twice_whole, half_denominator,
            Equal.sym(Nat, half_denominator, twice_whole, equality)),
          Equal.sym(Nat,
            Nat.mul(1n, Nat.mul(half_denominator, half_denominator)),
            Nat.mul(half_denominator, half_denominator),
            Natural.one_mul(Nat.mul(half_denominator, half_denominator)))))))

def Natural.not_successor_le_self(n: Nat, proof: Natural.Le(1n+n, n)) -> Empty:
  match n:
    case 0n:
      proof
    case 1n+p:
      Natural.not_successor_le_self(p, proof)

def Natural.le_double(+n: Nat) -> Natural.Le(n, Nat.double(n)):
  Natural.le_congruent(n, Nat.add(n, n), n, Nat.double(n), Natural.le_add_right(n, n), {==},
    Equal.sym(Nat, Nat.double(n), Nat.add(n, n), Natural.double_add(n)))

def Natural.le_scale_successor(+s: Nat, +h: Nat) -> Natural.Le(1n+s, Nat.mul(1n+s, 1n+h)):
  Natural.le_congruent(1n+s, Nat.mul(1n+h, 1n+s), 1n+s, Nat.mul(1n+s, 1n+h),
    Natural.le_add_right(1n+s, Nat.mul(h, 1n+s)), {==},
    Natural.mul_commutative(1n+h, 1n+s))

def Natural.le_of_scaled_gap(+s: Nat, +left: Nat, +right: Nat, +slack: Nat, +gap: Nat,
  gap_is: {Nat.add(right, gap) == left : Nat},
  scaled: Natural.Le(Nat.mul(1n+s, left), Nat.add(Nat.mul(1n+s, right), slack)),
  small: Natural.Le(slack, s)) -> Natural.Le(left, right):
  match gap:
    case 0n:
      Natural.le_congruent(right, right, left, right, Natural.le_reflexive(right),
        Equal.trans(Nat, right, Nat.add(right, 0n), left, Equal.sym(Nat, Nat.add(right, 0n), right, Natural.add_zero(right)), gap_is),
        {==})
    case 1n+h:
      +lifted: {Nat.mul(1n+s, left) == Nat.add(Nat.mul(1n+s, right), Nat.mul(1n+s, 1n+h)) : Nat} =
        Equal.trans(Nat, Nat.mul(1n+s, left), Nat.mul(1n+s, Nat.add(right, 1n+h)), Nat.add(Nat.mul(1n+s, right), Nat.mul(1n+s, 1n+h)),
          Equal.cong(Nat, Nat, z => Nat.mul(1n+s, z), left, Nat.add(right, 1n+h), Equal.sym(Nat, Nat.add(right, 1n+h), left, gap_is)),
          Natural.mul_add_right(1n+s, right, 1n+h))
      excess: Natural.Le(Nat.mul(1n+s, 1n+h), slack) =
        Natural.le_add_left_cancel(Nat.mul(1n+s, right), Nat.mul(1n+s, 1n+h), slack,
          Natural.le_congruent(Nat.mul(1n+s, left), Nat.add(Nat.mul(1n+s, right), slack),
            Nat.add(Nat.mul(1n+s, right), Nat.mul(1n+s, 1n+h)), Nat.add(Nat.mul(1n+s, right), slack),
            scaled, lifted, {==}))
      Empty.absurd(Natural.Le(left, right),
        Natural.not_successor_le_self(s,
          Natural.le_transitive(1n+s, slack, s,
            Natural.le_transitive(1n+s, Nat.mul(1n+s, 1n+h), slack, Natural.le_scale_successor(s, h), excess),
            small)))

def Natural.le_of_scaled_witness(+s: Nat, +left: Nat, +right: Nat, +slack: Nat,
  witness: Exists(Nat, gap => {Nat.add(right, gap) == left : Nat}),
  scaled: Natural.Le(Nat.mul(1n+s, left), Nat.add(Nat.mul(1n+s, right), slack)),
  small: Natural.Le(slack, s)) -> Natural.Le(left, right):
  (gap, gap_is) = witness
  Natural.le_of_scaled_gap(s, left, right, slack, gap, gap_is, scaled, small)

def Natural.le_of_scaled_order(+s: Nat, +left: Nat, +right: Nat, +slack: Nat,
  order: Or(Natural.Le(left, right), Natural.Le(right, left)),
  scaled: Natural.Le(Nat.mul(1n+s, left), Nat.add(Nat.mul(1n+s, right), slack)),
  small: Natural.Le(slack, s)) -> Natural.Le(left, right):
  match order:
    case Inl{below}:
      below
    case Inr{above}:
      Natural.le_of_scaled_witness(s, left, right, slack, Natural.le_gap(right, left, above), scaled, small)

def Natural.le_of_scaled_le(+s: Nat, +left: Nat, +right: Nat, +slack: Nat,
  scaled: Natural.Le(Nat.mul(1n+s, left), Nat.add(Nat.mul(1n+s, right), slack)),
  small: Natural.Le(slack, s)) -> Natural.Le(left, right):
  Natural.le_of_scaled_order(s, left, right, slack, Natural.le_total(left, right), scaled, small)

def Natural.le_decidable(a: Nat, b: Nat) -> Or(Natural.Le(a, b), Natural.Le(a, b) -> Empty):
  match a b:
    case 0n 0n:
      Inl{Unit{}}
    case 0n 1n+bp:
      Inl{Unit{}}
    case 1n+ap 0n:
      Inr{proof => proof}
    case 1n+ap 1n+bp:
      Natural.le_decidable(ap, bp)
