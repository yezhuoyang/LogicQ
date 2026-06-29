# TypeChecker/Core

> The trusted core of the legality type checker: the binary-symplectic kernel, the typing environment Γ, and the elaboration path from ChainQ codes into validity-carrying typed blocks.

This is the foundation layer of the LogicQ TypeChecker. It sits between the **front-end ChainQ code families** (`CSSCode`/`StabilizerCode`/logical bases) and the higher **judgments** (PPM, transversal, code-switch). Everything here is **PL-minimal**: there is no new Pauli or code type — a Pauli on `n` qubits is a `GF2.BoolVec` of width `2n` (X-block ++ Z-block), a code is a symplectic stabilizer `GF2.BoolMat`, and all operations reuse `ChainQ.GF2`. The core's job is to turn a raw, untrusted `Block` into a `TypedBlock` that *carries a proof* of `Block.valid`, so downstream judgments may trust every invariant.

## What's here

| Module | Role |
| --- | --- |
| [Symplectic.lean](Symplectic.lean) | Binary symplectic kernel: symplectic form, orthogonality, Clifford-as-`2n×2n`-matrix, and elaboration of `CSSCode`/`StabilizerCode`/`PauliString` into width-`2n` stabilizer matrices. |
| [Block.lean](Block.lean) | The typing environment Γ: `Block`, `Block.valid` (well-formed + complete), `TypedBlock`/`SubBlock`, `Env` → `TypedEnv` validation at the boundary. |
| [Elaborate.lean](Elaborate.lean) | The normal path: a `CheckedCSSCode` + `CheckedLogicalBasis` (from ChainQ) elaborate and runtime-validate into a `TypedBlock`. |
| [Distance.lean](Distance.lean) | Explicit, machine-checkable distance-bound obligations (`DistanceObligation`, `checkBlockDistance`) for FT paths that assume `d ≥ required`. |
| [Error.lean](Error.lean) | The `TypeError` vocabulary and `ok?`/`res?` helpers; judgments return `Except TypeError <evidence>`. |

## Key definitions

```lean
structure Block where
  n    : Nat
  stab : BoolMat            -- symplectic stabilizer generator rows
  lx   : BoolMat := []      -- declared logical X̄ rows  (LogicalBasis, declared-first)
  lz   : BoolMat := []      -- declared logical Z̄ rows
  dist : Option ChainQ.CSSDistanceBounds := none
  live : Bool := true
  own  : Owned := .owned
  deriving Repr
```

```lean
def Block.valid (b : Block) : Bool :=
  b.validPartial &&
  decide (b.lx.length = b.n - rank b.stab)        -- COMPLETENESS: k = n − rank(stab)
```

```lean
structure TypedBlock where
  block : Block
  valid : block.valid = true
```

```lean
def sympForm (n : Nat) (u v : BoolVec) : Bool := dotBit u (swapHalves n v)
```

```lean
def cssToStab (c : CSSCode) : BoolMat := c.symplecticStabilizers
```

```lean
def toTypedBlock? (cc : CheckedCSSCode) (clb : CheckedLogicalBasis) : Except TypeError TypedBlock :=
  validateBlock? 0 (elaborateBlock cc clb)
```

## Example

```lean
-- a bare logical qubit (X̄ = [1 0], Z̄ = [0 1]), no stabilizers — k = 1 − rank [] = 1:
{ n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] }
-- OK: well-formed AND complete

-- XX written twice ⇒ rank 1, k = 1 (redundant generators tolerated):
{ n := 2, stab := [[true, true, false, false], [true, true, false, false]],
  lx := [[true, false, false, false]], lz := [[false, false, true, true]] }
-- OK: rank, not row count

-- n = 2, no stabilizers ⇒ k must be 2, but only one logical pair is exposed:
{ n := 2, stab := [], lx := [[true, false, false, false]],
  lz := [[false, false, true, false]] }
-- rejected: INCOMPLETE (k = n − rank stab not met — though this IS a legitimate `SubBlock`)
```

These `Block` values pin down the meaning of `Block.valid`: a bare qubit is valid, redundant generators are tolerated (rank, not row count), and an incomplete logical basis is rejected (though it is a legitimate `SubBlock`). Source: [Block.lean](Block.lean) (lines 116–126).

## Status & scope

- **Tier D (`by decide` tests):** `Block.valid` / `Block.validPartial`, `TypedEnv.ofEnv?`, the symplectic predicates (`sympForm`, `preservesSymp`, `sympOrthogonal`), `checkBlockDistance`, and the full ChainQ → `TypedBlock` elaboration pipeline are all exercised by executable `example … := by decide` checks in their respective modules.
- **Validity is runtime-validated, not yet proved end-to-end.** Elaboration (`elaborateBlock` / `toTypedBlock?`) packages the `Block.valid` proof via `validateBlock?` at runtime. The `∀`-level theorem that *CSS-validity ⇒ `Block.valid`* (needing `rank (cssToStab c) = rank hx + rank hz` plus a span-embedding lemma) is **explicitly deferred** — see the DESIGN_NOTE in [Elaborate.lean](Elaborate.lean).
- **Distance bounds are obligations, not certificates.** [Distance.lean](Distance.lean) only checks that a block *carries* a `CSSDistanceBounds` profile meeting `required`; it does not itself prove any distance lower bound. The underlying bound is a documented assumption (Tier A) supplied by the front-end profile.
- **Trusted boundary:** a `TypedBlock` makes malformed blocks *unrepresentable* downstream, so judgments never re-check `Block.valid` — but this trust rests on the runtime validation above, not a closed proof.

## See also

- [../README.md](../README.md) — the TypeChecker overview (judgments built on this core).
- [../../README.md](../../README.md) — the LogicQ repository root.
- [../../Compiler/CONTRACT.md](../../Compiler/CONTRACT.md) — the P/D/A/M proof-status tiering referenced above.
