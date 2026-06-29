# LatticeSurgery

> Reserved placeholder for a full lattice-surgery / adapter language; **no `.lean` modules live here yet**.

This folder is an intentional, empty-of-code placeholder in the LogicQ stack. In the
longer target pipeline (`ChainQ -> PPR -> PPM -> surgery/adapter -> QStab -> QClifford`)
this layer would own the merge/split/bridge/adapter and product-/batched-surgery nodes
that sit between the logical Pauli-product languages (PPM, MagicQ) and the physical
stabilizer-measurement target (QStab). **It is not implemented here.** The actually-built
surgery work currently lives in `Compiler/LS` (the lattice-surgery IR, "LSIR"),
`Compiler/LS2QStab` (lowering skeleton), and cross-block PPM capability checks in
`TypeChecker/Judgment/PPM`.

## What's here

This folder contains **only this README** — there are no `.lean` files and no child
directories. The table below is intentionally empty of modules to avoid implying code
that does not exist.

| Module | Role |
| --- | --- |
| _(none)_ | This is a reserved/stub folder; no Lean modules are present. |

## Key definitions

There are no Lean definitions in this folder. The intended responsibilities (verbatim
from this folder's prior README) are:

> A surgery node should check the merged CSS matrices, measured logical Pauli,
> preserved logicals, gauge handling, detector determinism, and explicit
> distance/fault-distance/decoder obligations.

For real, currently-defined surgery types and theorems, see the [Compiler.LS](../Compiler/LS/README.md)
layer — e.g. its `Program` AST, the `check`/lowering passes, and the load-bearing
`lower_dataflow` preservation theorem.

## Example

There is no code to quote from this folder. The full intent recorded in the prior
placeholder README is:

```text
This layer should own merge, split, bridge, adapter, product-surgery, and
batched-surgery nodes.
```

(Source: this folder's own `README.md`.) A concrete, real lattice-surgery value — a
well-formed sparse-Pauli measurement — lives instead in the implemented LSIR layer,
[Compiler/LS/README.md](../Compiler/LS/README.md) (the actual `SPauli` value from
[Compiler/LS/Syntax.lean:64](../Compiler/LS/Syntax.lean#L64)):

```lean
[(0, .Z), (1, .Z)]      -- OK: a well-formed 2-body ZZ readout (densifies on 3 qubits to "ZZI")
```

## Status & scope

**Stub / planned (M in the [Compiler/CONTRACT.md](../Compiler/CONTRACT.md) tiering: missing/planned).**

- The full lattice-surgery / adapter IR described above is **not implemented** in this
  folder. Nothing here is proved, decided, or wired — there is no code to make any claim about.
- The current, honestly-bounded surgery implementation is the LSIR in
  [Compiler/LS](../Compiler/LS/README.md): a sparse-Pauli surgery-schedule / certificate
  IR with `by decide` well-formedness tests, a `propext`-only (not "axiom-free")
  `lower_dataflow` preservation theorem, and a large set of **explicitly deferred**
  obligations (stabilizer-flow semantic soundness, code/fault distance, decoder
  threshold, downstream extractability, full cultivation / 15-to-1 chunks). None of
  those deferred items are upgraded by this placeholder.
- Cross-block / cross-code PPM legality checks live in
  [TypeChecker/Judgment/PPM](../TypeChecker/Judgment/PPM/README.md); an early
  surgery-side type-checker placeholder also exists at
  [TypeChecker/LatticeSurgery](../TypeChecker/LatticeSurgery/README.md).

## See also

- [../README.md](../README.md) — the LogicQ repository root and the target stack diagram.
- [../Compiler/LS/README.md](../Compiler/LS/README.md) — the implemented lattice-surgery IR (LSIR).
- [../Compiler/LS2QStab/README.md](../Compiler/LS2QStab/README.md) — the LS-to-QStab lowering skeleton.
- [../Compiler/CONTRACT.md](../Compiler/CONTRACT.md) — the proved / `by decide` / assumed / missing tiering contract.
- [../TypeChecker/Judgment/PPM/README.md](../TypeChecker/Judgment/PPM/README.md) — cross-block PPM capability checks.
- [../TypeChecker/LatticeSurgery/README.md](../TypeChecker/LatticeSurgery/README.md) — the surgery-side type-checker placeholder.
