# TypeChecker/ChainQ

> Reserved namespace for ChainQ-specific checker adapters — currently a documentation stub.

This folder is a placeholder in the LogicQ stack's legality layer. It is meant to
hold checker-side adapters that connect front-end ChainQ code families to the
`TypeChecker` static legality judgments (front-end ChainQ codes -> TypeChecker
legality -> Compiler Mixed IR -> ... -> QStab/QClifford physical target). **No
implementation lives here yet.** The actual ChainQ -> TypeChecker elaboration
path currently resides one level up, in
[`TypeChecker/Core/Elaborate.lean`](../Core/Elaborate.lean).

## What's here

| Module | Role |
|--------|------|
| (none) | This folder contains only this `README.md`; there are no `.lean` modules here yet. |

The elaboration that this namespace is reserved to host lives, for now, in the
sibling `Core` folder.

## Key definitions

These live in [`../Core/Elaborate.lean`](../Core/Elaborate.lean) (the current home
of the ChainQ -> TypeChecker path), not in this folder:

```lean
/-- **The normal ChainQ → TypeChecker path**: elaborate and validate, packaging
    the `Block.valid` proof.  Errors (`malformedBlock`) only if the symplectic
    block fails to validate. -/
def toTypedBlock? (cc : CheckedCSSCode) (clb : CheckedLogicalBasis) : Except TypeError TypedBlock :=
  validateBlock? 0 (elaborateBlock cc clb)
```

```lean
/-- Elaborate a checked CSS code + checked logical basis into a raw symplectic
    `Block` (stabilizers via `cssToStab`, logicals embedded; owned & live). -/
def elaborateBlock (cc : CheckedCSSCode) (clb : CheckedLogicalBasis) : Block
```

## Example

The folder has only this header/stub `README.md` — there is no `.lean` code to
quote from it. The representative code for what this namespace is reserved to do
lives in [`../Core/Elaborate.lean`](../Core/Elaborate.lean):

```lean
/-- Elaborate a checked CSS code + checked logical basis into a raw symplectic
    `Block` (stabilizers via `cssToStab`, logicals embedded; owned & live). -/
def elaborateBlock (cc : CheckedCSSCode) (clb : CheckedLogicalBasis) : Block :=
  { n    := cc.code.n,
    stab := cssToStab cc.code,
    lx   := embedX cc.code.n clb.basis.lx,
    lz   := embedZ cc.code.n clb.basis.lz,
    live := true, own := .owned }
```

This turns a validity-carrying ChainQ `CheckedCSSCode` plus its
`CheckedLogicalBasis` into the symplectic `Block` that the TypeChecker judgments
consume.

## Status & scope

- **Stub / planned (M).** This folder is reserved for ChainQ-specific checker
  adapters and currently holds no Lean implementation.
- The ChainQ -> TypeChecker elaboration that would otherwise belong here is
  implemented (and runtime-VALIDATED via `validateBlock?`) in
  [`../Core/Elaborate.lean`](../Core/Elaborate.lean). Per that file's own header,
  the `∀`-proof that CSS-validity implies `Block.valid` is **deferred** (it needs
  a rank identity and a span-embedding lemma); only runtime validation packages
  the `Block.valid` proof for now.
- Nothing in this folder is proved or wired, because there is nothing here yet —
  do not treat this namespace as carrying any guarantees.

## See also

- [../README.md](../README.md) — parent `TypeChecker` layer (legality checks over typed QEC blocks).
- [../Core/Elaborate.lean](../Core/Elaborate.lean) — the current ChainQ -> TypeChecker elaboration path.
- [../../README.md](../../README.md) — repository root.
