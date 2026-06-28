# ChainQ/Core

> The code-type layer of the ChainQ front end: the declarable code kinds, their decidable well-typedness, and theorem-backed parameter/logical/distance metadata.

This is the static, Mathlib-free heart of the ChainQ front end. A QEC code is declared either directly (as a `CSSCode` check-matrix pair or a `StabilizerCode` Pauli-generator list) or homologically (as a `ChainComplex` over Z2), and well-typedness is a `decide`-able Boolean judgement. It sits at the source end of the LogicQ stack — these checked code objects feed the TypeChecker legality layer and downstream Compiler Mixed IR before everything lowers to the QStab/QClifford physical target.

## What's here

| Module | Role |
| --- | --- |
| [Code.lean](Code.lean) | The two code kinds: `CSSCode` (GF(2) `hx`/`hz`) and `StabilizerCode` (explicit Paulis), with decidable `valid`. |
| [ChainComplex.lean](ChainComplex.lean) | Two-step chain complex over Z2; the `chainComplex_css` soundness theorem; elaboration `toCSS`. |
| [Params.lean](Params.lean) | Rank-computed `k`, homological logical reps, `CSSLogicalBasis` validity, and `deriveLogicalBasis?` (+ soundness). |
| [LogicalIndex.lean](LogicalIndex.lean) | User-declared logical-qubit indexing: named Z/X representatives, diagnostics, proof-carrying basis wrappers. |
| [Distance.lean](Distance.lean) | Theorem-backed distance-bound profiles (no search): family/systolic/expansion/cleaning/paper-table sources. |
| [Error.lean](Error.lean) | The `ChainQError` error vocabulary for checked constructors. |

## Key definitions

```lean
structure CSSCode where
  n  : Nat
  hx : BoolMat
  hz : BoolMat

def CSSCode.valid (c : CSSCode) : Bool := c.wellShaped && c.cssCondition

structure ChainComplex where
  nFaces : Nat
  nEdges : Nat
  nVerts : Nat
  d2 : BoolMat
  d1 : BoolMat

def ChainComplex.toCSS (cc : ChainComplex) : CSSCode :=
  { n := cc.nEdges, hx := transpose cc.d1 cc.nVerts, hz := cc.d2 }
```

```lean
theorem chainComplex_css (cc : ChainComplex) :
    cc.chainLaw = cc.toCSS.cssCondition := by
  rfl
```

```lean
def CSSCode.k (c : CSSCode) : Nat := c.n - rank c.hx - rank c.hz

theorem deriveLogicalBasis?_sound {c : CSSCode} {b : CSSLogicalBasis}
    (h : deriveLogicalBasis? c = some b) : CSSLogicalBasis.valid c b = true
```

## Example

```lean
/-- **Type-system soundness.**  The chain-complex law `∂₁∘∂₂ = 0` holds iff the
    elaborated CSS code satisfies the CSS commutation condition `H_X·H_Zᵀ = 0`.
    Equivalently: every well-typed chain complex elaborates to a genuine,
    pairwise-commuting CSS code. -/
theorem chainComplex_css (cc : ChainComplex) :
    cc.chainLaw = cc.toCSS.cssCondition := by
  rfl
```

This headline theorem is the distinguishing feature of the front end: declaring a code as a chain complex whose well-typedness is `∂₁∘∂₂ = 0` is *exactly* declaring a code that elaborates to a commuting CSS code. It is exercised concretely on worked surface patches, e.g. `example : triangle.chainLaw = true := by decide` and `example : square.toCSS.cssCondition = true := by decide`. Source: [ChainComplex.lean](ChainComplex.lean).

## Status & scope

Using the [Compiler/CONTRACT.md](../../Compiler/CONTRACT.md) tiers (P proved theorem, D `by decide` test, A documented assumption, M missing/planned):

- **P — proved theorems.** `chainComplex_css` and `chainComplex_toCSS_cssCondition` (type-system soundness, `rfl`); `ChainComplex.fromBoundaryMaps?_sound`; `deriveLogicalBasis?_sound`; `CSSCode.logicalZ_iff` / `logicalX_iff`; `independentModulo_iff_rank`; `CheckedLogicalPauliBasis.valid_css`; `completeCheckedLogicalPauliBasis?_sound`. These are about the *static* judgements (shape, commutation, logical-class membership, basis validity), not about channels or operational equivalence.
- **D — `by decide` tests.** Extensive: worked `triangle`/`square`/`asymCC` chain complexes, the `fiveQubit` stabilizer code, `bareQubit`/`xCheck2`, derived bases for `surface`/`toric`, and the `toyLPCSS` lifted-product logical-index examples with their negative (rejection) cases.
- **A — documented assumptions.** Distance information is NOT searched, enumerated, or solved for in Lean. Per [Distance.lean](Distance.lean), a distance bound enters only as a named, externally-audited theorem/profile certificate (`familyTheorem`, `productSystolic`, `graphExpansion`, `cleaningUpperBound`, `paperTableTheorem`, `externalFormalTheorem`); the executable Lean work is only arithmetic and consistency checking on supplied bounds.
- **M — out of scope here.** `k` is computed from GF(2) rank but no fault-tolerance, decoder, channel-correctness, or operational-equivalence claim is made at this layer; `deriveLogicalBasis?` / `completeLogicalIndex?` guarantee a *checked* logical basis but explicitly do NOT optimize weight, sparsity, geometry, or qLDPC locality.

Soundness theorems here are the usual `propext`-clean kind (not "axiom-free"). No claim is upgraded beyond what the code proves.

## See also

- Parent: [ChainQ/README.md](../README.md) — the front-end code type system and its subfolders.
- Repo root: [README.md](../../README.md).
- Sibling layer used here: [ChainQ/Algebra](../Algebra/README.md) — the GF(2) matrix/kernel routines.
- (`LogicalIndex.lean` builds on `ChainQ.Checked`; see [ChainQ/Checked](../Checked/README.md).)
