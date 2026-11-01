# Payment allocation, proven in Bend

This allocator splits an amount of money across accounts in proportion to their weights. Typical uses are a dividend over holdings, a trade fill over orders, or a fee pool over investors.

It is written in [Bend 2](https://github.com/bendlang/bend), whose compiler won't accept a change to the code unless it comes with a mathematical proof that the rules below still hold. The question this proof of concept asks is whether that proof requirement is a workable commit gate for code that an AI agent edits.

New to Bend? [`TUTORIAL.md`](TUTORIAL.md) explains the language and walks through every proof.

## The rules

The rules live in [`LAWS.bend`](LAWS.bend). It is about 20 lines, written for a reviewer to read, and the AI never edits it:

| Law | In plain English |
|---|---|
| `conserves` | The shares add up to exactly the total. Rounding loses no cent and invents none. |
| `fair` | There is one share per account, and each share is **less than one cent** from its exact pro-rata amount `weight × total ÷ W`. |
| `zero_weight_gets_zero` | An account with weight zero receives nothing, whatever the other weights. |

`conserves` and `fair` assume the weights add up to a positive `W`; with no weight at all there is nothing to split by. Amounts are whole minor units (cents, or shares for a fill). The total and the weights can be any size, subject to the native limit described under [What is and isn't proven](#what-is-and-isnt-proven).

`bend PROOF.bend` prints `ALL PROOFS CHECK` only when every law is proven for **every** input, not just for a sample of test cases. It takes about 0.3s.

## What it does

From `bend demo.bend`. The "naive" row rounds each account down on its own:

```
1. Split a $100.00 payment three ways
  total    $100.00   weights [1, 1, 1]
  allocate [$33.33, $33.33, $33.34]   sum $100.00
  naive    [$33.33, $33.33, $33.33]   sum $99.99   <-- $0.01 lost

2. Dividend of $1,234,567.89 over holdings of 5,000 / 12,500 / 82,500 shares
  total    $1234567.89   weights [5000, 12500, 82500]
  allocate [$61728.39, $154320.99, $1018518.51]   sum $1234567.89
  naive    [$61728.39, $154320.98, $1018518.50]   sum $1234567.87   <-- $0.02 lost

4. A $99.99 fee pool over seven equal investors
  total    $99.99   weights [1, 1, 1, 1, 1, 1, 1]
  allocate [$14.28, $14.28, $14.29, $14.28, $14.29, $14.28, $14.29]   sum $99.99
  naive    [$14.28, $14.28, $14.28, $14.28, $14.28, $14.28, $14.28]   sum $99.96   <-- $0.03 lost
```

The full output, all five scenarios, is in [`tests/demo.expected`](tests/demo.expected).

## The demo: a commit gate for AI edits

[`mistakes/`](mistakes) holds two edits to `main.bend` that an agent could plausibly make when asked to "simplify" the code:

| Mistake | What it looks like | Law it breaks |
|---|---|---|
| [`naive-rounding.bend`](mistakes/naive-rounding.bend) | "Just compute each share directly." Every share is within a cent, but the rounded-away cents go nowhere: $100.00 three ways pays $99.99. | `conserves` |
| [`leftover-to-first.bend`](mistakes/leftover-to-first.bend) | "Round down, give the leftover to the first account." A common real-world shortcut. The total is right, but the first account can get up to n − 1 extra cents: $99.99 over seven pays the first $14.31 against an exact $14.28. | `fair` |

```bash
./mistakes/try.sh mistakes/naive-rounding.bend
```

This swaps the mistake into a scratch copy, runs the gate (which prints `SOME PROOFS FAIL` and exits 1), then shows what the change would have paid.

The gate can't tell an agent *why* its proof fails, only that it does. In both cases above, though, no proof can exist, because the code really breaks a law; each mistake file's header gives the counterexample. An agent that keeps trying can only get through by fixing the code. It cannot get through by weakening the check, as long as `LAWS.bend` and `SPEC.bend` are protected; see [`.github/CODEOWNERS`](../.github/CODEOWNERS).

## Running it

Install Bend (`curl -fsSL https://bend-lang.com/install.sh | sh`), then, from this folder:

```bash
bend PROOF.bend                 # the gate: ALL PROOFS CHECK
bend demo.bend                  # the scenarios above
./mistakes/try.sh mistakes/leftover-to-first.bend
./check.sh                      # everything CI runs
```

The checks were developed against Bend at commit `faeb02e` (31 Oct 2026); CI pins that commit. To use a checkout instead of the installer, set `BEND="bun /path/to/bend/bend2/main.ts"` for the scripts. Bend's own README notes that the installed `bend` ignores a project's `bunfig.toml` and `.env`, so prefer it for code you don't trust.

### Native and JavaScript builds

```bash
bend demo.bend -o demo && ./demo            # native, via clang
bend main.bend -o build/allocate.mjs        # an ES module of main.bend
node node/example.mjs                       # calls it from Node
```

[`node/example.mjs`](node/example.mjs) shows the TypeScript/Node integration path: the proven code, compiled as-is, called with plain numbers.

## How it works

The allocator ([`main.bend`](main.bend), 28 lines of code) carries the rounding remainder from each account to the next. Starting from `carry = 0`:

```
share  = (carry + weight × total) div W
carry' = (carry + weight × total) mod W
```

Every step is one exact equation: `share × W + carry' = carry + weight × total`, with both carries below `W`. That equation is what makes the proofs tractable:

- **Conservation.** Summed over the accounts, the equation telescopes to `(Σ shares) × W + last carry = W × total`. Since `last carry < W`, it follows that `Σ shares = total`.
- **Fairness.** On its own, the equation puts `share × W` within `W` of `weight × total`.
- **Zero weight.** Fairness with `weight = 0` forces `share × W < W`, so the share is 0.

[`PROOF.bend`](PROOF.bend) spells this out in about 250 lines. Bend has no tactics, so every rewrite is an explicit term.

## What is and isn't proven

- **The laws are about Bend's own definitions.** The proofs reason about `Nat` as Bend defines it in its Base library, where numbers are unbounded. The native and JavaScript builds swap in machine arithmetic, so you trust Bend's compiler to do that faithfully.
- **Native numbers stop at 2⁴⁸ − 1, about 2.8 × 10¹⁴.** The intermediate value is `weight × total`, so, for example, $1bn in cents with weights up to 1,000 fits, while $10bn does not. Past the limit, the program halts with `a Nat past the largest immediate 2^48-1` (exit 1, or an exception in JavaScript). It never returns a wrong figure. There is no 64-bit integer type, which is the main thing to resolve before production use.
- **Nothing about order.** Which account gets the extra cent depends on the order of the accounts, so this is not the "largest remainder" method. The method doesn't guarantee that a larger weight gets at least as much as a smaller one, and the laws don't claim it.
- **The proofs pass the strict check.** `bend PROOF.bend --verdict` re-checks them with BendTT, a small kernel whose soundness is proven in Lean, so the trusted base is that kernel rather than Bend's full checker. It needs Lean 4.34.0, so CI runs it as its own job, and it passes. You can run it locally once Lean is installed.
- **Bend is young.** Bend 2 was released in September 2026, and Bend 1 code does not carry over.

## The cost of the proofs

| | Lines (non-comment) |
|---|---|
| Code: `main.bend` | 28 |
| Rules: `LAWS.bend` + `SPEC.bend` | 49 |
| Proof: `PROOF.bend` | 246 |
| Arithmetic lemmas: `vendor/Natural.bend` | 1,093 (vendored, MIT) |

That is roughly 9 lines of proof per line of code, on top of an existing lemma library. Claude wrote the proofs in one session, with about a dozen round trips to the checker. The error messages were precise enough to fix each failure directly. For a fair comparison, a property-based test suite would take a fraction of the effort, but it covers only the inputs it samples.

## Files

| File | Owner | Role |
|---|---|---|
| `TUTORIAL.md` | anyone | How Bend works, and how each proof is built |
| `LAWS.bend`, `SPEC.bend` | human | The rules, and the definitions they are written in |
| `main.bend` | anyone | The allocator |
| `PROOF.bend` | whoever edits `main.bend` | The proofs; must check before commit |
| `vendor/Natural.bend` | upstream | Arithmetic lemmas from [bend-math](https://github.com/chelokot/bend-math), unmodified |
| `demo.bend`, `node/` | anyone | Running the allocator |
| `mistakes/` | anyone | Edits the gate must block |
| `check.sh`, `tests/` | anyone | What CI runs |
