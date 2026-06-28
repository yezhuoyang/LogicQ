# Compiler/PPM2LS

> Reserved (empty) directory for the planned PPM-layer → lattice-surgery (LS) IR lowering pass.

This folder is a **placeholder** for a future compiler edge that would translate legal PPM
(Pauli-product-measurement) layers into the lattice-surgery IR. In the LogicQ stack the
intended linear pipeline is `ChainQ → PPR → PPM → LS → QStab → QClifford`; this directory
owns the `PPM → LS` step. As of now it is **not implemented** — the only end-to-end wired
path is `Source LogicalOp → Mixed IR` (via `compile?`), plus the `Mixed/PPM → QStab →
QClifford` extraction edges. The downstream LS IR that this pass would eventually emit into
already exists as a standalone language under [`../LS/`](../LS/Basic.lean).

## What's here

This directory currently contains **no `.lean` modules** and **no subdirectories** — only this
README. There is nothing to lower yet.

| Module | Role |
| ------ | ---- |
| _(none)_ | No Lean source files exist in this folder. |

## Key definitions

None in this folder. The intended pass would select native surgery, product surgery, bridge,
adapter, or code-switch implementations for legal PPM layers and emit checked surgery
certificates, targeting the existing LS IR (e.g. [`../LS/Syntax.lean`](../LS/Syntax.lean),
[`../LS/Cert.lean`](../LS/Cert.lean), [`../LS/Check.lean`](../LS/Check.lean)). No such
definitions live here.

## Example

There is no example to quote: this is a header-only placeholder directory. The complete content
of [README.md](README.md) (prior to this rewrite) was simply a one-paragraph reservation note
describing the future pass. The verbatim design intent recorded for it is:

```text
Reserved for the PPM-to-surgery/adapter pass.

The future pass should select native surgery, product surgery, bridge, adapter,
or code switch implementations for legal PPM layers, then emit checked surgery
certificates.
```

## Status & scope

- **Tier: M (missing / planned).** Per [CONTRACT.md](../CONTRACT.md), `Compiler/{ChainQ2PPR,
  PPM2LS, QStab2QClifford}` were originally all empty; `PPM2LS` remains empty (no code wired).
  The `PPM → LS` edge is listed among the **missing-pass notes** that still apply, and
  `ChainQ/DESIGN_NOTE.md` explicitly records that the `PPM2LS/` folder "stays empty (no code)".
- **Nothing proved here.** There are no theorems, no `by decide` tests, and no documented
  assumptions in this folder, because there is no code. Any channel-correctness, fault-tolerance,
  distance, or operational-equivalence claims for `PPM → LS` are therefore **deferred** — not
  asserted by this directory.
- The LS IR that this pass is meant to target is implemented separately and should not be
  conflated with this placeholder; see [`../LS/`](../LS/Basic.lean).

## See also

- Parent: [Compiler/README.md](../README.md) — lists `PPM2LS` among the planned passes.
- Contract / scope matrix: [Compiler/CONTRACT.md](../CONTRACT.md).
- The downstream lattice-surgery IR this pass would emit into: [Compiler/LS](../LS/Basic.lean).
- Sibling planned pass: [Compiler/ChainQ2PPR](../ChainQ2PPR/README.md).
