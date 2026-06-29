# Logical

> Shared logical-level addressing vocabulary: which logical qubit of which logical block.

This is the smallest shared layer in the LogicQ stack. The front end (ChainQ) declares
logical *blocks* — code patches such as the surface code, whose machine-form AST is
`CodeDecl.surface 3` (surface/toric have no surface macro; ChainQ/Syntax.lean) — and the
logical IRs (PPR, PPM) compute on the logical *qubits* of those blocks. This module fixes
the single `LQubit`
address type so every logical level (ChainQ source, PPR/PPM, TypeChecker, Compiler source)
refers to the same addressing scheme. There are no physical qubits here; those appear only
after lowering to QStab / QClifford.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Defines `Logical.BlockId` and the `Logical.LQubit` address structure. Mathlib-free pure `Nat` data. |

## Key definitions

From [Basic.lean](Basic.lean):

```lean
abbrev BlockId := Nat
```

```lean
structure LQubit where
  blk : BlockId
  idx : Nat
  deriving DecidableEq, Repr, Inhabited
```

`BlockId` indexes a declared logical block (the front end maps block names `q`, `a`, `t`
to numeric ids in first-occurrence order). `LQubit` is the `idx`-th logical qubit of block
`blk` (intended `0 ≤ idx < k_blk`). In the logical-IR surface syntaxes a logical qubit is
written *block name* + *index* in square brackets, e.g. `q[0]` (the first block, id `0`);
its `LQubit` machine form is `⟨0, 0⟩`.

## Example

```lean
structure LQubit where
  blk : BlockId
  idx : Nat
  deriving DecidableEq, Repr, Inhabited
```

The full data definition from [Basic.lean](Basic.lean). The `deriving DecidableEq` is what lets
later layers compare logical qubits by `decide`; `Repr` enables `#eval`-style printing and
`Inhabited` provides a default. The original README's illustrative addresses were

```lean
def q0 : Logical.LQubit := { blk := 0, idx := 0 }
def q1 : Logical.LQubit := { blk := 0, idx := 1 }
```

(these `def`s are not present in [Basic.lean](Basic.lean) itself — the file defines only the
two declarations above).

## Status & scope

This folder is **pure data, no theorems**. It declares an addressing type and nothing more:

- `BlockId` / `LQubit` are concrete `Nat`-backed definitions (Mathlib-free). There are no
  proof obligations, `by decide` tests, or soundness theorems in this folder, so the
  CONTRACT tiers (P / D / A / M) do not apply to anything here.
- **Not enforced here:** bounds (`idx < k_blk`), liveness, and ownership are *not* checked by
  this module. Those constraints are imposed later by `TypeChecker.TypedEnv` and the
  compiler source checks. `LQubit` only names an address; legality lives downstream.

## See also

- [../README.md](../README.md) — repository root: the full ChainQ → TypeChecker → Compiler
  Mixed IR → QStab/QClifford pipeline this addressing feeds into.
- [../TypeChecker/README.md](../TypeChecker/README.md) — where `LQubit` bounds / ownership are
  actually checked.
- [../PPM/README.md](../PPM/README.md), [../PPR/README.md](../PPR/README.md) — logical IRs that
  compute on these `LQubit` addresses.
