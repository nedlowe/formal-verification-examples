# demo: runs the allocator in main.bend on a few realistic splits, next to the
# naive method (round every account's share down on its own), which is the
# bug LAWS.bend exists to block.
#
#   bend demo.bend

import Base
import ./main.bend as Alloc

# The naive method: each share is w * total div W, independently. Every
# share is fair to within a cent, but the leftover cents vanish.
def naive.go(+total: Nat, +weight: Nat, ws: List<&2, Nat>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      Nat.div(Nat.mul(w, total), weight) <> naive.go(total, weight, rest)

def naive(+total: Nat, +ws: List<&2, Nat>) -> List<&2, Nat>:
  naive.go(total, Alloc.sum(ws), ws)

# Display
# -------

def pad2.pick(+c: Nat, small: Bool) -> String:
  match small:
    case True{}:
      "0" ++ Nat.show(c)
    case False{}:
      Nat.show(c)

def money(+cents: Nat) -> String:
  "$" ++ Nat.show(Nat.div(cents, 100n)) ++ "." ++ pad2.pick(Nat.mod(cents, 100n), Nat.is_lt(Nat.mod(cents, 100n), 10n))

def show.one(cash: Bool, +n: Nat) -> String:
  match cash:
    case True{}:
      money(n)
    case False{}:
      Nat.show(n)

def show.sep(+xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      ", "

def show.go(+cash: Bool, +xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case h <> t:
      show.one(cash, h) ++ show.sep(t) ++ show.go(cash, t)

def show(+cash: Bool, +xs: List<&2, Nat>) -> String:
  "[" ++ show.go(cash, xs) ++ "]"

def diff.pick(+cash: Bool, +total: Nat, +paid: Nat, short: Bool) -> String:
  match short:
    case True{}:
      "   <-- " ++ show.one(cash, Nat.sub(total, paid)) ++ " lost"
    case False{}:
      ""

def diff(+cash: Bool, +total: Nat, +paid: Nat) -> String:
  diff.pick(cash, total, paid, Nat.is_lt(paid, total))

def scenario(+title: String, +cash: Bool, +total: Nat, +ws: List<&2, Nat>) -> IO(Unit):
  +good = Alloc.allocate(total, ws)
  +bad = naive(total, ws)
  do IO<Unit>:
    IO.print(title)
    IO.print("  total    " ++ show.one(cash, total) ++ "   weights " ++ show(False{}, ws))
    IO.print("  allocate " ++ show(cash, good) ++ "   sum " ++ show.one(cash, Alloc.sum(good)))
    IO.print("  naive    " ++ show(cash, bad) ++ "   sum " ++ show.one(cash, Alloc.sum(bad)) ++ diff(cash, total, Alloc.sum(bad)))
    IO.print("")

def main() -> IO(Unit):
  do IO<Unit>:
    scenario("1. Split a $100.00 payment three ways", True{}, 10000n, [1n, 1n, 1n])
    scenario("2. Dividend of $1,234,567.89 over holdings of 5,000 / 12,500 / 82,500 shares", True{},
      123456789n, [5000n, 12500n, 82500n])
    scenario("3. A fill of 1,001 shares across orders for 300 / 300 / 400", False{}, 1001n, [300n, 300n, 400n])
    scenario("4. A $99.99 fee pool over seven equal investors", True{}, 9999n, [1n, 1n, 1n, 1n, 1n, 1n, 1n])
    scenario("5. $5.00 over weights 0 / 1 / 2: the zero-weight account gets nothing", True{}, 500n, [0n, 1n, 2n])
