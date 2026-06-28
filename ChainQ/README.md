# ChainQ

> The front-end code type system: declaring CSS/stabilizer code families and type-checking them into proof-carrying code objects.

ChainQ is the entry layer (`L_FE`) of the LogicQ stack. A user declares a QEC code family (surface, toric, HGP, bivariate-bicycle, lifted-product, or a raw CSS matrix pair); ChainQ elaborates and *type-checks* it into a `CheckedCSSCode` that carries its own validity proof. Downstream, the TypeChecker checks protocol legality and the Compiler lowers to the Mixed IR and ultimately to the QStab/QClifford physical target.

This top-level folder is the **umbrella + source-language boundary**: it re-exports the algebra, core types, code-family constructors, and materialization API (which live in subfolders), and adds the source-declaration syntax (`CodeDecl`, `NamedCodeDecl`) and a readable surface syntax.

## What's here

Most root `.lean` files are thin shims or aggregators after the strict-folder-ownership refactor; the real implementations live in the subfolders. The genuinely source-bearing modules at this level are [Syntax.lean](Syntax.lean) and [SurfaceSyntax.lean](SurfaceSyntax.lean).

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Public umbrella; `import ChainQ.Basic` pulls in the whole ChainQ layer. |
| [Syntax.lean](Syntax.lean) | Source declarations `CodeDecl` / `NamedCodeDecl` and the checked elaboration `check?` / `checkLogicalIndex?`. |
| [SurfaceSyntax.lean](SurfaceSyntax.lean) | Readable paper-facing commands + BB/circulant polynomial sugar (`BBPoly`, `XVar`/`YVar`). |
| [Families.lean](Families.lean) | Aggregator re-exporting the per-family constructors. |
| [Checked.lean](Checked.lean) | Aggregator re-exporting `CheckedCSSCode`, `mkCSS`, `mkSurface`, `mkToric`, `mkHGP`, `mkBB`, `mkLiftedProduct`. |
| [Code.lean](Code.lean) | Shim re-exporting `ChainQ.Core.Code` (`CSSCode`, `StabilizerCode`). |
| [ChainComplex.lean](ChainComplex.lean) | Shim re-exporting `ChainQ.Core.ChainComplex`. |
| [GF2.lean](GF2.lean) · [GF2Rank.lean](GF2Rank.lean) · [Shape.lean](Shape.lean) · [Kernel.lean](Kernel.lean) · [Ring.lean](Ring.lean) | Shims re-exporting `ChainQ.Algebra.*`. |
| [Params.lean](Params.lean) · [Error.lean](Error.lean) · [Distance.lean](Distance.lean) · [LogicalIndex.lean](LogicalIndex.lean) | Shims re-exporting `ChainQ.Core.*`. |

## Key definitions

```lean
-- ChainQ/Syntax.lean
inductive CodeDecl where
  | css (code : CSSCode)
  | surface (d : Nat)
  | toric (d : Nat)
  | hgp (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat)
  | bb (l m : Nat) (a b : List (Prod Nat Nat))
  | liftedProduct (l : Nat) (A : List (List Circ)) (rA nA : Nat)
  deriving Repr
```

```lean
-- ChainQ/Syntax.lean
def CodeDecl.check? : CodeDecl -> Except ChainQError CheckedCSSCode
```

```lean
-- ChainQ/Checked/Basic.lean — the invariant is carried in the type
structure CheckedCSSCode where
  code  : CSSCode
  valid : code.valid = true

def mkCSS (c : CSSCode) : Except ChainQError CheckedCSSCode
```

```lean
-- ChainQ/Checked/Basic.lean — a genuine ∀-theorem about the constructor
theorem mkCSS_sound {c : CSSCode} {cc : CheckedCSSCode} (h : mkCSS c = .ok cc) :
    cc.code = c
```

```lean
-- ChainQ/Core/ChainComplex.lean — chain law ⇔ CSS commutation, by rfl (re-exported here)
theorem chainComplex_css (cc : ChainComplex) :
    cc.chainLaw = cc.toCSS.cssCondition := by
  rfl
```

## Example

```lean
example : isOk ((CodeDecl.surface 3).check?) = true := by decide
example : isOk ((CodeDecl.toric 2).check?) = true := by decide
example : isOk ((CodeDecl.bb 3 3 [(0, 0), (1, 0), (0, 2)] [(0, 0), (2, 0), (0, 1)]).check?) = true := by decide
example : isOk ((CodeDecl.liftedProduct 3 [[[0], [1]]] 1 2).check?) = true := by decide
```

These `by decide` smoke tests in [Syntax.lean](Syntax.lean) show source-level code-family declarations elaborating and type-checking through `check?` into a `CheckedCSSCode`. Companion negative tests in the same file (e.g. `badNClaimSurface3`, `badDClaimSurface3`, `missingDistanceClaimSurface3`) confirm that a wrong declared `[[n,k,d]]` or a missing exact-distance profile is *rejected*.

## Status & scope

- **P — proved.** The `CheckedCSSCode` invariant is carried in the type (no checked code with an invalid `code` exists, via `CheckedCSSCode.code_valid`). `mkCSS_sound` / `mkLogicalBasis_sound` ([Checked/Basic.lean](Checked/Basic.lean)) and the headline `chainComplex_css` / `chainComplex_toCSS_cssCondition` ([Core/ChainComplex.lean](Core/ChainComplex.lean), by `rfl`) establish static type-system soundness — shape, CSS commutation `H_X·H_Zᵀ = 0`, and logical-class membership. Soundness theorems here are typically `propext`-clean, **not** "axiom-free".
- **D — `by decide` tests.** The `check?` / `checkLogicalIndex?` smoke and negative tests in [Syntax.lean](Syntax.lean) and the rejection test in [Checked/Basic.lean](Checked/Basic.lean).
- **A — assumptions / external.** A declared distance `d` is **not** proved here: `CodeParamClaim.checkAgainst` only accepts `d` when a *theorem-backed exact distance profile* (`CSSDistanceBounds.provesExactDistance`) is supplied, and known-paper-table profiles (e.g. `paperTableExact`) are documented external/paper citations, not in-Lean distance proofs.
- **M / deferred.** Channel correctness, fault-tolerance, decoder behaviour, and operational equivalence are out of scope for this static front-end and are deferred (see [Compiler/CONTRACT.md](../Compiler/CONTRACT.md)). These judgements are about the *static* code object, not about quantum channels.

## See also

- Parent: [../README.md](../README.md)
- Subfolders (each with its own README): [Algebra](Algebra/README.md) (GF(2) / circulant-ring kernel), [Core](Core/README.md) (code types, chain complexes, params, errors, distance, logical index), [Materialize](Materialize/README.md) (concrete check / stabilizer export), [Checked](Checked/README.md) (validity-carrying constructors).
- Code families: [HGPCode](HGPCode/README.md), [Surface](Surface/README.md), [Toric](Toric/README.md), [BBCode](BBCode/README.md), [LiftedProduct](LiftedProduct/README.md), [ColorCode](ColorCode/README.md).
