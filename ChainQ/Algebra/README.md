# ChainQ/Algebra

> The Mathlib-free GF(2) linear-algebra kernel that ChainQ and the typechecker are built on.

This is the lowest layer of the LogicQ front-end: pure `Bool`/`List`/`Nat` GF(2) primitives (no Mathlib), used to express CSS codes and chain complexes before any legality checking happens. It is deliberately name-compatible with `FormalRV.Framework.LDPC` (`BoolVec`/`BoolMat`/`dotBit`/`transpose`/`orthogonal`) so the spec can later be reconciled with the vendored FormalRV `CSSCode` pivot. On top of the bare arithmetic it adds explicit shape predicates, Gaussian elimination (rank / span membership / witnesses), right-kernel and quotient bases for *deriving* logical operators, and a circulant group-ring `F₂[x]/(xˡ−1)` for the lifted-product / bivariate-bicycle code families. Everything above (ChainQ code families → TypeChecker legality → Compiler Mixed IR → … → QStab/QClifford) consumes these `BoolMat` operations.

## What's here

| Module | Role |
| --- | --- |
| [GF2.lean](GF2.lean) | Core GF(2) primitives: `BoolVec`/`BoolMat`, `dotBit`, `transpose`, `gemmT`, `matMul`, `orthogonal`, plus the `zero_gemmT_iff_orthogonal` bridge theorem. |
| [Shape.lean](Shape.lean) | Explicit shape predicates (`matrixWellShaped`, `hasShape`, `square`, `compatibleMul`, `sameWidth`), safe accessors (`row?`), and builders (`identMat`, `zeroMat`, `kron`, checked `hcat?`/`vcat?`). |
| [GF2Rank.lean](GF2Rank.lean) | GF(2) Gaussian elimination: `vecXor`, `rowReduce`, `rank`, `inSpan`, and witness-carrying `solveInSpan?`. |
| [Kernel.lean](Kernel.lean) | Right-kernel basis (`kernelBasis`), quotient bases, and matrix inverse — shape-checked wrappers (`kernelBasis?`, `quotientBasis?`, `gf2Inv?`) over an `Unsafe` namespace. |
| [Ring.lean](Ring.lean) | The circulant group-ring `F₂[x]/(xˡ−1)`: `circNorm`, `circulant`, `circMul`, `circDagger`, ring matrices, and the binary `liftMat`. |

## Key definitions

```lean
abbrev BoolVec := List Bool
abbrev BoolMat := List BoolVec
```

```lean
/-- GF(2) inner product: `true` iff the number of positions where both are
    `1` is odd (`Σ aᵢ·bᵢ mod 2`).  `dotBit a b = false` ⇔ `a ⟂ b`. -/
def dotBit (a b : BoolVec) : Bool :=
  decide (((a.zip b).countP (fun p => p.1 && p.2)) % 2 = 1)
```

```lean
/-- The CSS commutation / orthogonality test `A · Bᵀ = 0`: every row of `a`
    is GF(2)-orthogonal to every row of `b`. -/
def orthogonal (a b : BoolMat) : Bool :=
  a.all (fun ra => b.all (fun rb => ! dotBit ra rb))
```

```lean
/-- Whether `v` lies in the row span of `m` (the central membership test). -/
def inSpan (m : BoolMat) (v : BoolVec) : Bool :=
  isZeroVec (reduceInto (rowReduce m) v)
```

```lean
/-- A basis of the right kernel `{x ∈ F₂ⁿ : ∀ row r of H, dotBit r x = 0}` — the
    orthogonal complement of the row span of `H`. -/
def kernelBasis (H : BoolMat) (n : Nat) : BoolMat
```

```lean
/-- Ring multiplication in `F₂[x]/(xˡ−1)`: convolution of supports mod `ℓ`,
    keeping odd-multiplicity exponents (mod-2 sum). -/
def circMul (l : Nat) (p q : Circ) : Circ
```

## Example

```lean
/-- **Bridge:** "the GF(2) product `A·Bᵀ` is zero" is exactly the
    orthogonality predicate — the two ways the CSS condition gets written. -/
theorem zero_gemmT_iff_orthogonal (a b : BoolMat) :
    isZeroMat (gemmT a b) = orthogonal a b := by
  unfold isZeroMat gemmT orthogonal
  induction a with
  | nil => rfl
  | cons ra ta ih =>
    simp only [List.map_cons, List.all_cons, all_not_map_dotBit, ih]
```

This is the single real theorem proved in the layer: it identifies the matrix form of the CSS condition (`A·Bᵀ = 0`) with the row-wise orthogonality predicate, so the two ways the type system writes the commutation check are provably the same. Source: [GF2.lean](GF2.lean).

## Status & scope

- **P (proved theorems).** [GF2.lean](GF2.lean) proves `all_not_map_dotBit` and `zero_gemmT_iff_orthogonal`, the bridge between the `gemmT` matrix product and the `orthogonal` predicate. These are the only `theorem`s in the folder.
- **D (`by decide` tests).** Every module ends with a block of `example … := by decide` smoke checks exercising `dotBit`/`transpose`/`orthogonal` ([GF2.lean](GF2.lean)), `rank`/`inSpan`/`solveInSpan?` ([GF2Rank.lean](GF2Rank.lean)), `identMat`/`kron`/shape predicates ([Shape.lean](Shape.lean)), `kernelBasis`/`gf2Inv` ([Kernel.lean](Kernel.lean)), and the circulant ring laws and GF(2) canonicalization regressions ([Ring.lean](Ring.lean)). These are concrete executable checks, not general theorems.
- **A (assumptions).** The core arithmetic (`dotBit`, `transpose`, `matMul`, `vecXor`, the `Unsafe.*` algebra, `liftMat`) relies on `List.zip`/`getD`, which silently truncate or pad on a width mismatch; callers must supply equal-width inputs. The shape predicates in [Shape.lean](Shape.lean) and the `?`-suffixed wrappers in [Kernel.lean](Kernel.lean) (`kernelBasis?`, `quotientBasis?`, `gf2Inv?`) exist precisely to make that obligation checkable, returning `none` rather than a silently wrong result — language/typechecker code should use those, not the `Unsafe.*` variants.
- **M (planned / not here).** No general correctness theorems for `rank`, `inSpan`, `kernelBasis`, `solveInSpan?`, or the ring operations are proved — their behaviour is validated only by `by decide` examples. There are no fault-tolerance, distance, decoder, or channel-correctness claims in this layer; those live (and are deferred) elsewhere in the stack.

## See also

- [../README.md](../README.md) — the ChainQ front-end (chain-complex code families) that consumes this kernel.
- [../../README.md](../../README.md) — the LogicQ repository root and overall verified-compiler pipeline.
- [../../Compiler/CONTRACT.md](../../Compiler/CONTRACT.md) — the P/D/A/M proof-tier contract referenced above.
