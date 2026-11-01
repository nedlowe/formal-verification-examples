# Tutorial: proving a payment allocator in Bend

This tutorial explains Bend, and then walks through this example from the problem to the last proof. It assumes you know what formal verification is: specifications, proofs, and the idea of a checker accepting or rejecting them. It assumes nothing about Bend, dependent types or Lean.

By the end you should be able to read every file in this folder, change the code, and fix the proof when the checker objects.

1. [Bend in brief](#1-bend-in-brief)
2. [The problem](#2-the-problem)
3. [The program: `main.bend`](#3-the-program-mainbend)
4. [The rules: `SPEC.bend` and `LAWS.bend`](#4-the-rules-specbend-and-lawsbend)
5. [The proofs: `PROOF.bend`](#5-the-proofs-proofbend)
6. [Working with the checker](#6-working-with-the-checker)
7. [The commit gate](#7-the-commit-gate)
8. [What you are trusting](#8-what-you-are-trusting)
9. [Exercises](#9-exercises)

---

## 1. Bend in brief

Bend 2 (Higher Order Company, September 2026) is a programming language and a proof assistant in one. It compiles to C, CUDA, Metal and JavaScript, and its type checker is also a proof checker, in the same family as Lean, Rocq and Agda. Its pitch is "laws": you state rules in a file called `LAWS.bend`, and the compiler refuses the codebase until each rule has a proof. Bend 1, the 2024 GPU-parallelism language, is a different language; nothing below applies to it.

What follows covers only what this example uses. `bend guide` prints the official guide.

### Syntax

Bend looks like Python, with types everywhere:

```python
import Base

type Shape is Data:
  Circle{r: U32}
  Square{s: U32}

def area(x: Shape) -> U32:
  match x:
    case Circle{+r}:
      (3 * r * r : U32)
    case Square{+s}:
      (s * s : U32)
```

The points that matter in this repo:

- **Branching is `match`; there is no `if`.** To branch on a boolean, you match `True{}` and `False{}`.
- **Operators need a type.** `(a + b : U32)` is shorthand for `U32.add(a, b)`. Most of this repo calls `Nat.add` and `Nat.mul` directly instead, because that's how they appear inside proofs.
- **Bend infers almost nothing.** You annotate a lot, and you pass type arguments by hand: `Equal.trans(Nat, a, b, c, …)` names all three terms. The payoff is a fast checker and precise error messages.

### `Nat`: the number type the proofs use

Base defines natural numbers the textbook way:

```python
type Nat is Data:
  Zero{}
  Succ{pred: Nat}
```

`3n` is a literal, and the pattern `1n+p` means "a successor whose predecessor is `p`". Arithmetic is defined by recursion on the **first** argument:

```python
def Nat.add(a: Nat, b: Nat) -> Nat:
  match a:
    case 0n:
      b
    case 1n+p:
      1n+Nat.add(p, b)
```

That detail matters a lot when writing proofs. The checker can simplify `Nat.add(1n+p, b)` to `1n+Nat.add(p, b)` on its own, but `Nat.add(b, 1n+p)` doesn't simplify at all until you prove a lemma about it.

At runtime, none of this is unary. The compiler replaces `Nat.add`, `Nat.mul` and `Nat.divmod` with machine instructions on 48-bit values, and a result past 2⁴⁸ − 1 stops the program. So you reason about the simple definition and execute the fast one; [section 8](#8-what-you-are-trusting) covers what that costs in trust.

The other number types are `U32` and `F32`. Floating point can't be reasoned about at all (`F32` is axiomatic), which is one reason money here is whole cents in a `Nat`.

### Termination

Every function must provably terminate, because a function that loops forever could "prove" anything. Bend's rule is structural: a recursive call must pass a smaller piece of an argument, taken apart by `match`.

The check reads arguments left to right. Each one must be passed unchanged until one is strictly smaller; after that, the rest are free. That's why the allocator's signature reads `go(total, bp, ws, carry)`: `total` and `bp` are passed unchanged, `ws` shrinks, and `carry` can be anything. There is no mutual recursion, and no def can call a def defined below it. That second rule surprises everyone once.

### Quantities: `+`, `-` and nothing

Bend is **affine**: by default a variable can be used at most once, which is how it compiles without a garbage collector. Prefixes change that:

| Written | Meaning |
|---|---|
| `x` | used at most once |
| `+x` | reusable (needs a copyable, `Data`-kinded type) |
| `-x` | erased: may appear only in types and proofs, and is deleted at runtime |

Most parameters in this repo are `+` because proofs mention the same value many times. The erased form shows up in the laws as `for -bp: Nat`: `bp` matters to the statement but has no runtime existence. The error `x (consumed more than once)` means you forgot a `+`.

### Propositions are types, proofs are programs

This idea is the core of Bend, as of every dependently typed prover. A **proposition is a type**, and a **proof is a value of that type**. Checking a proof means type-checking a program.

| Logic | Bend |
|---|---|
| `a = b` | the type `{a == b : Nat}` |
| proof by computation | `{==}`, accepted when both sides evaluate to the same term |
| `A and B` | the pair type `A & B`; a proof is a pair `(pa, pb)` |
| `A or B` | `Or(A, B)`; a proof is `Inl{pa}` or `Inr{pb}` |
| `A implies B` | the function type `A -> B` |
| for all `x` | a function parameter `x` |
| false | `Empty`, a type with no values |
| true | `Unit`, whose one value is `Unit{}` |
| induction | recursion; the recursive call is the induction hypothesis |
| case analysis | `match` |

Because types can be computed, you can **define a proposition by recursion**. Here is how the vendored library defines `≤`:

```python
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
```

`Le(2n, 5n)` evaluates to `Unit`, so `Unit{}` proves it. `Le(5n, 2n)` evaluates to `Empty`, so nothing proves it. And `Le(1n+a, 1n+b)` *is* `Le(a, b)` by evaluation, with no lemma needed. Section 5 depends on that.

### Laws and proofs

A `law` is a named claim; a `def` with the same name is its proof:

```python
law add_zero:
  for x: Nat
  {Nat.add(x, 0n) == x : Nat}

def add_zero(x):
  match x:
    case 0n:
      {==}                                    # 0 + 0 evaluates to 0
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}
```

A project keeps its laws in `LAWS.bend` and their proofs in `PROOF.bend`, as `def Laws.<name>`. `bend PROOF.bend` prints `ALL PROOFS CHECK` and exits 0 only when every law has a complete proof. A law without a proof, a `?TODO` hole, or an `@unsafe` def anywhere in the imported code all make it print `SOME PROOFS FAIL` and exit 1.

**Bend has no tactics.** Lean users will miss `simp`, `ring`, `omega` and `linarith`: you write the proof term yourself. For arithmetic that means explicit chains of equalities, and you'll see plenty of them below.

---

## 2. The problem

You must split a total, in cents, across accounts in proportion to their weights. A dividend split over shareholdings, a trade fill over orders and a fee pool over investors are all this problem. The exact share `weight × total ÷ W` (where `W` is the sum of the weights) is rarely a whole number of cents, so something has to round.

The obvious approach rounds each account down independently. Each share is then within a cent of its exact amount, but the dropped fractions add up: $100.00 split three ways pays $33.33 × 3 = $99.99, and the missing cent belongs to nobody. Rounding to nearest has the opposite failure and can pay out more than the total. Real systems patch this with "give the leftover to the first account", which keeps the total right but can overpay one account by many cents.

We want three guarantees, for **every** input:

1. **Conservation.** The shares add up to exactly the total.
2. **Fairness.** Every share is less than one cent from its exact amount.
3. **Zero in, zero out.** A weight of zero gets nothing.

Tests can sample these. The point of the exercise is to prove them.

---

## 3. The program: `main.bend`

The method carries each account's rounding remainder into the next account. Starting from `carry = 0`, for each weight `w`:

```
x      = carry + w × total
share  = x div W
carry' = x mod W
```

For $100.00 over `[1, 1, 1]` (`W = 3`):

| account | x | share | carry' |
|---|---|---|---|
| 1 | 0 + 10000 = 10000 | 3333 | 1 |
| 2 | 1 + 10000 = 10001 | 3333 | 2 |
| 3 | 2 + 10000 = 10002 | 3334 | 0 |

No fraction is ever dropped; it just waits until it adds up to a whole cent. In Bend:

```python
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

def allocate(+total: Nat, +ws: List<&2, Nat>) -> List<&2, Nat>:
  split(total, ws, sum(ws))
```

Two choices here were made for the proofs:

- **The divisor is `1n+bp`, not `W`.** `split` matches the total weight, so `go` only ever runs with `W = 1 + bp`. That makes "we never divide by zero" a matter of how the value is written, rather than a side condition every lemma has to carry. Read `bp` as "W minus one".
- **`Nat.div` and `Nat.mod` are called separately**, not as one `Nat.divmod` whose pair is then destructured. Both versions run the same, but the separate calls give the proofs two named terms to talk about. [Section 5](#the-helper-pattern) explains why destructuring would have hurt.

`List<&2, Nat>` is a list of reusable `Nat`s; `h <> t` is cons.

---

## 4. The rules: `SPEC.bend` and `LAWS.bend`

### Turning "within one cent" into something provable

"Each share is within one cent of `w × total ÷ W`" involves a division, and division is awkward to reason about. Multiply through by `W` and it becomes two strict inequalities, with no division and no fractions:

```
s × W  <  w × total + W        (s is below the exact amount + 1)
w × total  <  s × W + W        (s is above the exact amount − 1)
```

`SPEC.bend` defines `<` from `≤`, and the fairness predicate over the two lists:

```python
def Lt(a: Nat, b: Nat) -> Kind(&2):
  N.Natural.Le(1n+a, b)

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
```

`Fair` is a proposition computed by recursion, just like `Le`. For lists of equal length it unfolds to one pair of inequalities per account. For lists of different lengths it reaches `Empty`, which can't be proven, so `Fair` also says "exactly one share per account" without a separate length law. `ZeroKept` follows the same pattern: per account, `{s == 0n}` when the weight is `0n`, and `Unit` otherwise.

### The laws

```python
law conserves:
  for +total: Nat
  for +ws: List<&2, Nat>
  for -bp: Nat
  for e: {Alloc.sum(ws) == 1n+bp : Nat}
  {Alloc.sum(Alloc.allocate(total, ws)) == total : Nat}
```

Read it as: for every total, for every list of weights, and for every `bp` such that the weights sum to `1 + bp`, the shares sum to the total. The `for e:` line is a hypothesis. A proof of the law is a function that receives evidence `e` of the precondition and must return evidence of the conclusion. "The weights sum to `1 + bp`" is how you say "the weights sum to something positive" without needing a `>` relation. `bp` is erased (`-`) because only the statement needs it.

`fair` has the same hypotheses, with conclusion `Spec.Fair(total, 1n+bp, ws, Alloc.allocate(total, ws))`. `zero_weight_gets_zero` has no precondition, because with no weight at all every share is zero anyway.

### Why `SPEC.bend` belongs to the reviewer

A law is only as good as its definitions. If someone redefined `Lt` as `Unit`, every fairness law would become trivially provable and mean nothing. That's why `SPEC.bend` gets the same protection as `LAWS.bend` (see `.github/CODEOWNERS`), and why it stays short enough to read.

---

## 5. The proofs: `PROOF.bend`

The whole argument rests on one equation per account. With `x = carry + w × total`, the code pays `q = x div W` and carries `r = x mod W`, and

```
q × W + r == carry + w × total,    with r ≤ bp   (that is, r < W)
```

Everything else is algebra on that equation. The proof is built in five layers.

### Layer 1: what does `Nat.div` actually do?

Base doesn't come with a theorem about division; it comes with a definition:

```python
def Nat.divmod.go(n: Nat, m: Nat, d: Nat, r: Nat) -> Nat & Nat:
  match n:
    case 0n:
      (d, r)
    case 1n+np:
      match m:
        case 0n:
          Nat.divmod.go(np, r, 1n+d, 0n)
        case 1n+mp:
          Nat.divmod.go(np, mp, d, 1n+r)

def Nat.divmod(a: Nat, b: Nat) -> Nat & Nat:
  match b:
    case 0n:
      (0n, a)
    case 1n+bp:
      Nat.divmod.go(a, bp, 0n, 0n)
```

It counts `n` down one at a time. `d` is the quotient so far, `r` the remainder so far, and `m` how far `r` is from rolling over into the next unit of `d`. So we first prove the textbook property of division, and the first job is to find the **loop invariant**: `m + r == bp` holds throughout.

The statement proven, `div.go`, says that after the loop finishes:

```
fst × (1 + bp) + snd == n + (r + d × (1 + bp))    and    snd ≤ bp
```

The right-hand side has `n` first on purpose. `Nat.add` recurses on its first argument, so when `n` steps from `1n+np` to `np` the checker can simplify the sum on its own, and each case of the induction needs one lemma (`add_successor`) instead of five. **Choosing the shape of a statement so that it evaluates is the most useful habit in Bend proving.** The top-level `div.spec(x, bp)` then specialises to `d = r = 0`, `m = bp`.

### Layer 2: the invariant across the whole list

For conservation we need a statement about the whole of `go`, not one step. We define `final(total, bp, ws, carry)`, the remainder left after the last account, and prove:

```
(sum of shares) × W + final  ==  carry + (sum of weights) × total,    and    final ≤ bp
```

This holds for any starting `carry ≤ bp`. The proof is induction on the list. In the step, the account's own equation (from layer 1) and the induction hypothesis for the rest of the list combine as:

```
(q + S') × W + rf  =  q×W + (S'×W + rf)          distributivity, associativity
                   =  q×W + (r + R×total)        the induction hypothesis
                   =  (q×W + r) + R×total
                   =  (carry + w×total) + R×total   this account's equation
                   =  carry + (w + R) × total     associativity, distributivity
```

Without tactics, each `=` is a term: `Equal.trans` to chain two equalities, `Equal.cong` to rewrite inside a context (`z => Nat.add(a, z)`), `Equal.sym` to flip one around, and a lemma from the vendored `Natural.bend` for associativity and the like. The general shape lives in `kept.alg`, which proves `((a + b) + c) == f + (g + e)` from `b + c == d + e` and `a + d == f + g`, so the step itself only has to say which terms are which.

<a id="the-helper-pattern"></a>**The helper pattern.** Bend won't `match` or destructure a computed value: `(e1, l1) = div.spec(x, bp)` is rejected. The fix used throughout is to pass the computed value to a helper that receives it as a parameter, and destructure it there:

```python
def kept.step(…, d: DivOk(…), ih: N.Natural.Le(…) -> Kept(…)) -> Kept(…):
  (e1, l1) = d
  kept.fin(total, bp, w, rest, carry, e1, ih(l1))

def kept(…):
  match ws:
    …
    case w <> rest:
      +x = Nat.add(carry, Nat.mul(w, total))
      kept.step(…, div.spec(x, bp), l => kept(total, bp, rest, Nat.mod(x, 1n+bp), l))
```

The induction hypothesis needs `l1` (the new carry is at most `bp`), which only exists after destructuring. So `kept` passes the recursive call down as a closure, `l => kept(…)`, and `kept.step` applies it. This avoids mutual recursion, which Bend forbids, and the termination checker still sees `rest` shrink. Helpers must be defined **above** the def that calls them.

### Layer 3: conservation

With `carry = 0`, layer 2 gives `S × W + rf == W × total`, with `rf ≤ bp`. To conclude `S == total`, squeeze it from both sides:

- `S × W ≤ S × W + rf = W × total`, so `S ≤ total`.
- `W × total = S × W + rf ≤ S × W + (W − 1)`, so `total ≤ S`.

The vendored lemma `le_of_scaled_le` performs exactly this cancellation: from `(1+s)·left ≤ (1+s)·right + slack` and `slack ≤ s`, it concludes `left ≤ right`. Antisymmetry (`le_antisymmetric`) then turns the two inequalities into an equality. That's all of `conserves.fin`.

One gap remains. The law is about `allocate(total, ws)`, which is `split(total, ws, sum(ws))`, and the checker can't simplify `split` until it knows whether `sum(ws)` is `0n` or `1n+_`. It can't match on `sum(ws)` either, because that's a computed value. The trick, in `conserves.split`, is to make the sum a **parameter**:

```python
def conserves.split(+total, +ws, +weight, -bp, e0: {Alloc.sum(ws) == weight : Nat}, e: …) -> …:
  match weight:
    case 0n:
      …   # impossible: e0 says the sum is 0, e says it is 1 + bp
    case 1n+wp:
      conserves.fin(total, wp, ws, e0, kept(total, wp, ws, 0n, N.Natural.zero_le(wp)))

def Laws.conserves(total, ws, bp, e):
  conserves.split(total, ws, Alloc.sum(ws), bp, {==}, e)
```

The law calls it with `weight := sum(ws)` and `e0 := {==}`. The `0n` case is impossible: `e0` and `e` together give `0 == 1 + bp`. To use that, a proof must produce `Empty` from it. `zero_ne_succ` does so by rewriting along a **motive**, `IsSucc`, which is `Empty` at `0n` and `Unit` at `1n+_`. Rewriting with `1+p == 0` turns the goal `Empty` (that is, `IsSucc(0n)`) into `IsSucc(1n+p)`, which is `Unit`, proven by `Unit{}`. This is the standard way to refute "0 equals a successor" in a type theory.

### Layer 4: fairness

Fairness needs no induction-wide invariant: each account's own equation is enough. From `q×W + r == carry + w×total`, with `carry ≤ bp` and `r ≤ bp`:

```
q×W  ≤  q×W + r  =  carry + w×total  ≤  bp + w×total
w×total  ≤  carry + w×total  =  q×W + r  ≤  q×W + bp
```

`fair.one` proves these two with `le_add_right`, `le_add_both_right`/`_left` and `le_transitive`. Then it turns them into the strict form `Fair` asks for. Here `Le(1+a, 1+b)` *is* `Le(a, b)` by evaluation, so `q×W ≤ bp + w×total` is already a proof of `q×W < (1+bp) + w×total` up to reordering a sum. The rest is the same list induction and helper pattern as layer 2.

There's one extra wrinkle. The law's `W` is `1 + bp`, but inside `split` the matched weight is `1 + wp`. They are the same number (both equal `sum(ws)`), but not the same *term*, so `fair.split` derives `1n+wp == 1n+bp` and rewrites the goal with `%same : …`.

### Layer 5: zero in, zero out

No new arithmetic is needed. With weight `0`, fairness's first inequality says `s × W < 0×total + W`, which evaluates to `Le(s×W, bp)`. If `s` were `1 + s'`, then `s×W` evaluates to `1 + (bp + s'×W)`, which is at least `1 + bp`, giving `1 + bp ≤ bp`. That is impossible (`not_successor_le_self`). So `s` must be `0n`, and `{==}` proves `0n == 0n`. With no weight at all, `split` returns `zeros(ws)`, and a short induction shows every element is `0n`.

### By the numbers

| | non-comment lines |
|---|---|
| `main.bend` (the code) | 28 |
| `LAWS.bend` + `SPEC.bend` (the rules) | 49 |
| `PROOF.bend` (the proofs) | 246 |
| `vendor/Natural.bend` (general arithmetic lemmas) | 1,093 |

Most of `PROOF.bend` spells out algebra that a human would wave through with "by distributivity". The vendored library is reusable and is re-checked on every run (put a `?TODO` in it and the gate fails), so it adds lines but no trust.

---

## 6. Working with the checker

Run `bend PROOF.bend` after every change; it takes well under a second. A failure tells you which def failed, what type was expected, what it observed, and the variables in scope. This is the one from writing the division proof:

```
- expected : {1n+Nat.add(Nat.add(bp, x), n) == Nat.add(x, Nat.add(bp, 1n+n)) : Nat}
- observed : {1n+Nat.add(Nat.add(bp, x), n) == Nat.add(x, 1n+Nat.add(bp, n)) : Nat}
```

The two differ only in where the `1n+` sits, so the fix is the lemma that moves it (`add_successor`), or restating things so that no move is needed.

Tools for exploring:

- **`?name` in place of a term prints the goal** at that point (together with the variables in scope) and fails. It is the closest Bend has to an interactive proof state.
- **`?TODO` leaves a hole**, so you can check the rest of the file and come back.
- **A `main` that returns a value is evaluated and printed by the checker.** Use this as a quick REPL:
  ```python
  def main() -> List<&2, Nat>:
    Alloc.allocate(1n, [3n, 2n])   # prints [0n, 1n]
  ```

Things that will trip you up, in rough order of frequency:

| Message or symptom | Cause | Fix |
|---|---|---|
| `x (consumed more than once)` | an affine variable used twice | mark it `+x` |
| `a match cannot scrutinize a computed value` | `match f(x)` or `(a, b) = f(x)` | pass `f(x)` to a helper and match its parameter |
| `can't be matched in this position` | a destructure after a `let` | destructure parameters first, then bind lets |
| `expected : a filled definition` | calling a def defined further down | move the helper above its caller |
| `expected : -bp / observed : bp` | an erased variable used at runtime | find a lemma that takes it erased, or write one |
| A rewrite fails mysteriously | `%e : P` turns `b` into `a`: the goal must match `P` with `_` replaced by the **right-hand** side of `e` | flip it with `Equal.sym`, or use `Equal.trans` chains |
| Nat literal error past `4294967295n` | literals stop at 2³² | build bigger numbers with `Nat.mul` |

---

## 7. The commit gate

The workflow Bend proposes is that a human writes `LAWS.bend`, an AI writes code and proofs, and `bend PROOF.bend` decides whether the result may be committed. `mistakes/` tests it with two edits an agent might plausibly make:

- **`naive-rounding.bend`** drops the carry. Each share is still fair, but $100.00 over three accounts sums to $99.99. `conserves` is false.
- **`leftover-to-first.bend`** rounds down and gives the leftover to account one. The total is right, but $99.99 over seven pays the first account $14.31 against an exact $14.2843. `fair` is false.

`./mistakes/try.sh mistakes/naive-rounding.bend` swaps one in and runs the gate.

The gate's message for either mistake is the same kind of error as section 6: the old proof no longer fits the new code. That alone doesn't say the code is wrong, since a correct refactor would also break the old proof, and the agent would then write a new one. What makes these mistakes different is that **no** proof can ever exist, because each mistake file's header gives a concrete input that violates the law. An agent can retry as often as it likes; the only way through is to change the code until the law is true.

An agent could also change the law, so two safeguards matter:

- **Protect the rules.** `LAWS.bend` and `SPEC.bend` are listed in `.github/CODEOWNERS`. With branch protection requiring code-owner review, an edit that weakens a law can't merge unreviewed.
- **Escape hatches are refused.** Bend reports `?TODO` holes, open laws and `@unsafe` defs as failures, so "prove it later" doesn't pass the gate.

---

## 8. What you are trusting

A proof moves trust from "the code is right" to a smaller set of things:

- **The laws say what you mean.** Nothing checks this but a reviewer, which is why the laws are short. For example, they say nothing about **order**: `allocate(1, [3, 2])` is `[0, 1]`, so a larger weight can receive less. That's allowed by `fair` (each share is within a cent of 0.6 and 0.4), but someone may still not want it. If that matters, it needs to be a law, and this method would then fail it (see the exercises).
- **Bend's checker.** `bend PROOF.bend --verdict` checks a second time with BendTT, a small kernel whose soundness is itself proven in Lean, so you need only trust that kernel. It needs Lean 4.34.0; CI runs it.
- **The compiler's arithmetic.** The proofs are about Peano `Nat`; the binary runs on 64-bit machine integers capped at 2⁴⁸ − 1. Past the cap the program stops; it doesn't wrap. So the guarantee holds whenever the program finishes, and the cap decides *whether* it finishes. Here the largest intermediate value is `weight × total`.
- **The toolchain version.** Bend 2 is weeks old, so CI pins the commit the proofs were checked against.

---

## 9. Exercises

Roughly in order of difficulty. Run `bend PROOF.bend` after each step.

1. **Break it yourself.** In `main.bend`, change `Nat.mod(x, 1n+bp)` to `0n`. Which def does the checker point at, and why that one?
2. **A zero total pays nothing.** Add a law: for any weights, every share of `allocate(0n, ws)` is `0n`. Hint: with a positive total weight, `fair.one`'s first inequality already forces it, as in layer 5.
3. **One share per account, always.** `Fair` implies equal lengths only when the weights sum to something positive. State and prove `List.length(Alloc.allocate(total, ws)) == List.length(ws)` for all inputs, using the `weight`-as-a-parameter trick from layer 3.
4. **Try to prove monotonicity**, "a larger weight never gets less", and find out why you can't. Then write it as a law and confirm that `bend PROOF.bend` refuses to let you fill it. What would you change in the algorithm? (The largest-remainder method satisfies it, at the cost of sorting, and a much harder permutation proof; `demos/proof_insertion_sort` in Bend's repo is a starting point.)
5. **Port it.** Do the same example in Lean, Dafny or SPARK, and compare the proof effort. That's the next folder in this repo.

## Further reading

- `bend guide`: the official language guide (`guide/GUIDE.md` in Bend's repository).
- `demos/proof_insertion_sort` in Bend's repository: a small, complete law-and-proof project, shaped like this one.
- [`chelokot/bend-math`](https://github.com/chelokot/bend-math): the source of `vendor/Natural.bend`, with integers, rationals and more.
- `paper/BendTT.pdf` in Bend's repository: the type theory, and why `--verdict` is trustworthy.
