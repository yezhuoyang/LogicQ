# Compiler/ChainQ2PPR

> Reserved compiler pass: typed ChainQ logical programs -> Pauli-product rotations (PPR). **Not implemented.**

This folder is a placeholder for the `ChainQ -> PPR` edge of the intended linear
pipeline `ChainQ → PPR → PPM → LS → QStab → QClifford`. It sits at the very front of
that pipeline: it would consume typed/legal logical programs (front-end ChainQ code
families, validated by the `TypeChecker`) and elaborate them into Pauli-product
rotations expressed in the standalone [`PPR`](../../PPR/README.md) language spec.
Per [`Compiler/CONTRACT.md`](../CONTRACT.md), this pass is currently **empty** — the
`ChainQ -> PPR` missing-pass note still applies, and the main wired path goes through
the Mixed IR instead (see [`Compiler/ChainQ2Mixed`](../ChainQ2Mixed)).

## What's here

This folder contains **no `.lean` modules** and **no child directories** — only this
`README.md`. There is nothing to import or build here yet.

| Module | Role |
| ------ | ---- |
| _(none)_ | Reserved for the future `ChainQ -> PPR` elaboration pass. |

## Key definitions

None in this folder. The target language already exists as a verified standalone spec
in the top-level [`PPR/`](../../PPR/README.md) directory (`PPR/Syntax.lean`,
`PPR/Semantics.lean`, `PPR/Basic.lean`) — a future pass here would produce
`PPR.RotProg` values and prove a theorem connecting source logical semantics to
`PPR.RotProg.denote`.

## Example

There is no Lean code in this folder. The entire contents of the directory is this
README; the previous version stated the intent verbatim:

```text
Reserved for the ChainQ-to-PPR pass.

No implementation lives here yet.  The future pass should elaborate typed
logical programs into Pauli-product rotations, with a theorem connecting source
logical semantics to `PPR.RotProg.denote`.
```

_Source: this file (`README.md`), prior revision._

As a pass-bridge layer, the two endpoints already have real syntax even though the
edge between them is empty. For illustration only — nothing here wires them — the
**source** side is a ChainQ code-family declaration (parses today via the
`code … as BivariateBicycle { … }` macro in `ChainQ/SurfaceSyntax.lean`):

```lean
-- ChainQ source: a real BivariateBicycle [[18, 2, 3]] code family.
code bb as BivariateBicycle {
  l = 3;
  m = 3;
  A = x^2*y + x^2*y^2;
  B = 1 + x*y^2;
  params = (18, 2, 3);
}
```

and the **target** side is a PPR program — a sequence of logical Pauli-product
rotations `± Angle · (q[i] ↦ P)*` (parses today via `PPR/Parse.lean`, `by decide`):

```text
+π/8 · q[0]↦Z              -- a logical T on q[0]   (π/8 = non-Clifford)
+π/4 · q[0]↦Z              -- a logical S on q[0]   (π/4 = Clifford)
+π/8 · q[0]↦Z q[1]↦Z       -- a two-qubit ZZ rotation over {q[0], q[1]}
```

The future pass would consume the former (after the `TypeChecker` validates it) and
emit a `PPR.RotProg` value of the latter shape, proving a theorem connecting source
logical semantics to `PPR.RotProg.denote`.

## Status & scope

- **M (missing / planned):** The `ChainQ -> PPR` pass is unimplemented. There is no
  elaboration function, no semantics-preservation theorem, and no `.lean` file here.
- The downstream **target** language [`PPR`](../../PPR/README.md) is a real, verified
  standalone spec (syntax + semantics + laws), but **nothing in this folder wires
  ChainQ to it**. Do not treat this edge as compiled or proved.
- The actually-wired front-end path is `Source/ChainQ -> Mixed IR` (see the parent
  [`Compiler/README.md`](../README.md) and [`Compiler/CONTRACT.md`](../CONTRACT.md)),
  not `ChainQ -> PPR -> PPM -> LS -> ...`, which remains the intended/future plan.

## See also

- [Compiler/README.md](../README.md) — parent compiler overview and the intended pipeline.
- [Compiler/CONTRACT.md](../CONTRACT.md) — proof tiers (P/D/A/M) and the missing-pass notes covering this edge.
- [PPR/README.md](../../PPR/README.md) — the standalone Pauli-product-rotation language this pass would target.
- [Compiler/PPR2PPM/README.md](../PPR2PPM/README.md) — the next intended edge (`PPR -> PPM`).
- [Compiler/ChainQ2Mixed](../ChainQ2Mixed) — the front-end edge that is actually wired today.
