# Formal verification examples

Small, runnable proofs of concept of formal verification applied to real business logic, one language or tool per folder. Each example states its rules in a form a reviewer can read, proves that the code obeys them, and runs those checks in CI.

| Example | Language | What is proven |
|---|---|---|
| [`bend-payment-allocation`](bend-payment-allocation) | [Bend 2](https://github.com/bendlang/bend) | A pro-rata money split never loses or invents a cent, and keeps every share within a cent of exact. Edits that break either rule are blocked at commit. Includes a [tutorial](bend-payment-allocation/TUTORIAL.md) on Bend and the proofs. |

## Adding an example

Each example lives in its own folder and is self-contained:

- a `README.md` covering what is proven, how to run it, and what is *not* proven;
- a `check.sh` that runs everything CI runs, and exits non-zero on any failure;
- a workflow in `.github/workflows/<folder>.yml`, limited by `paths:` to its own folder;
- pinned toolchain versions, so a green run means the same thing next year.

## Licence

MIT; see [`LICENSE`](LICENSE). Vendored third-party files carry their own licence alongside them.
