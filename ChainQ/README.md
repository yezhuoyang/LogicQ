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

ChainQ has a real surface syntax for the lifted-product and bivariate-bicycle families:
the `code <name> as LiftedProduct { … }` and `code <name> as BivariateBicycle { … }`
macros (parse today — [SurfaceSyntax.lean](SurfaceSyntax.lean)) elaborate to `NamedCodeDecl`,
and `check?` remains the checked boundary into `CheckedCSSCode`:

```lean
-- parses today — ChainQ/SurfaceSyntax.lean (bivariate-bicycle macro)
code bbCode as BivariateBicycle {
  l = 3;
  m = 3;
  A = x^2*y + x^2*y^2;
  B = 1 + x*y^2;
  params = (18, 2, 3);
}

-- parses today — ChainQ/SurfaceSyntax.lean (lifted-product macro)
-- protograph is a rows×cols matrix of circulant polynomials in `x` (see CircPoly sugar);
-- entries are written as 1 / x / x^k / sums, e.g. `1 + x^2`.
code lpCode as LiftedProduct {
  ell = 8;
  rows = 3;
  cols = 4;
  protograph = [[1, x, x^2, x^3], [x, x^2, x^3, 1], [x^2, x^3, 1, x]];
  params = (200, 20, 10);
}
```

The `surface` and `toric` families have **no** surface macro — they are written directly as
the `CodeDecl` AST (machine form). Each declaration below elaborates and type-checks through
`check?` into a `CheckedCSSCode`:

```lean
-- machine form (no surface macro) — ChainQ/Syntax.lean : inductive CodeDecl
CodeDecl.surface 3   -- OK: the d=3 surface code
CodeDecl.toric 2     -- OK: the d=2 toric code
```

A `NamedCodeDecl` additionally carries a claimed `[[n,k,d]]` and a distance profile; the matcher
in [Syntax.lean](Syntax.lean) accepts the claim only when `n`/`k` recompute and a theorem-backed
exact-distance profile is supplied. The surface-3 declaration with the correct claim is accepted;
companion declarations with a wrong `n`, a wrong `d`, or no distance profile are *rejected*:

```lean
-- OK: n/k recompute and a surface-3 exact-distance profile is supplied
{ name := "surface3", decl := .surface 3,
  claimedParams   := some { n := 13, k := 1, d := 3 },
  distanceProfile := surfaceDistanceBounds? 3 }

-- rejected: declared n=12, but the compiled surface-3 code has n=13      (badNClaimSurface3)
{ name := "surface3", decl := .surface 3,
  claimedParams   := some { n := 12, k := 1, d := 3 },
  distanceProfile := surfaceDistanceBounds? 3 }

-- rejected: declared d=4, but the profile only proves exact d=3          (badDClaimSurface3)
{ name := "surface3", decl := .surface 3,
  claimedParams   := some { n := 13, k := 1, d := 4 },
  distanceProfile := surfaceDistanceBounds? 3 }

-- rejected: declared d=3, but no theorem-backed exact-distance profile    (missingDistanceClaimSurface3)
{ name := "surface3", decl := .surface 3,
  claimedParams   := some { n := 13, k := 1, d := 3 },
  distanceProfile := none }
```

## Status & scope

- **P — proved.** The `CheckedCSSCode` invariant is carried in the type (no checked code with an invalid `code` exists, via `CheckedCSSCode.code_valid`). `mkCSS_sound` / `mkLogicalBasis_sound` ([Checked/Basic.lean](Checked/Basic.lean)) and the headline `chainComplex_css` / `chainComplex_toCSS_cssCondition` ([Core/ChainComplex.lean](Core/ChainComplex.lean), by `rfl`) establish static type-system soundness — shape, CSS commutation `H_X·H_Zᵀ = 0`, and logical-class membership. Soundness theorems here are typically `propext`-clean, **not** "axiom-free".
- **D — `by decide` tests.** The `check?` / `checkLogicalIndex?` smoke and negative tests in [Syntax.lean](Syntax.lean) and the rejection test in [Checked/Basic.lean](Checked/Basic.lean).
- **A — assumptions / external.** A declared distance `d` is **not** proved here: `CodeParamClaim.checkAgainst` only accepts `d` when a *theorem-backed exact distance profile* (`CSSDistanceBounds.provesExactDistance`) is supplied, and known-paper-table profiles (e.g. `paperTableExact`) are documented external/paper citations, not in-Lean distance proofs.
- **M / deferred.** Channel correctness, fault-tolerance, decoder behaviour, and operational equivalence are out of scope for this static front-end and are deferred (see [Compiler/CONTRACT.md](../Compiler/CONTRACT.md)). These judgements are about the *static* code object, not about quantum channels.

## See also

- Parent: [../README.md](../README.md)
- Subfolders (each with its own README): [Algebra](Algebra/README.md) (GF(2) / circulant-ring kernel), [Core](Core/README.md) (code types, chain complexes, params, errors, distance, logical index), [Materialize](Materialize/README.md) (concrete check / stabilizer export), [Checked](Checked/README.md) (validity-carrying constructors).
- Code families: [HGPCode](HGPCode/README.md), [Surface](Surface/README.md), [Toric](Toric/README.md), [BBCode](BBCode/README.md), [LiftedProduct](LiftedProduct/README.md), [ColorCode](ColorCode/README.md).
