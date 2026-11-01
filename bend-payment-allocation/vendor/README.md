# vendor

`Natural.bend` is copied unmodified from
[chelokot/bend-math](https://github.com/chelokot/bend-math) at commit
`9d1fb38299ceae7cd4bb5b8097c33a07df966484`, under the MIT licence in
[`LICENSE`](LICENSE). It supplies the arithmetic lemmas the proofs lean on:
commutativity, associativity and distributivity of `Nat.add`/`Nat.mul`, and
the `Le` order with its transitivity, antisymmetry and cancellation rules.

Bend checks this file like any other: `bend PROOF.bend` re-proves every lemma
in it, so vendoring it adds no trust.
