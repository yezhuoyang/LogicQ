# ChainQ / LiftedProduct

> Lifted-product CSS code constructor over the circulant ring `F₂[x]/(xˡ−1)`.

This folder is one of the ChainQ front-end code families. It turns a ring matrix `A`
(a matrix of circulant-polynomial exponent lists) into a concrete `CSSCode` via the
lifted-product construction (Panteleev–Kalachev, [arXiv 2012.04068](https://arxiv.org/abs/2012.04068)).
It sits at the very front of the LogicQ stack: families like this materialize concrete
GF(2) `hx`/`hz` matrices that downstream layers (TypeChecker legality → Compiler Mixed IR
→ QStab/QClifford physical target) consume.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Raw (shape-unchecked) `Internal.liftedProduct`, plus the `Option`-returning `liftedProduct?` checked variant; dimension / CSS-condition `by decide` tests. |
| [Checked.lean](Checked.lean) | `mkLiftedProduct`, the `Except ChainQError CheckedCSSCode` constructor that reports shape errors, plus its `isOk` accept test. |

## Key definitions

```lean
def liftedProduct (l : Nat) (A : List (List Circ)) (rA nA : Nat) : CSSCode :=
  let Ad := pDagger l A
  let pHx := pHcat (pKron l A (pIdent nA)) (pKron l (pIdent rA) Ad)
  let pHz := pHcat (pKron l (pIdent nA) A) (pKron l Ad (pIdent rA))
  { n  := (rA * rA + nA * nA) * l,
    hx := liftMat l pHx,
    hz := liftMat l pHz }
```

```lean
def liftedProduct? (l : Nat) (A : List (List Circ)) (rA nA : Nat) : Option CSSCode
```

```lean
def mkLiftedProduct (l : Nat) (A : List (List Circ)) (rA nA : Nat) :
    Except ChainQError CheckedCSSCode
```

`Internal.liftedProduct` is the raw builder: `hx = lift[A⊗I | I⊗A*]`, `hz = lift[I⊗A | A*⊗I]`,
with `n = (rA²+nA²)·ℓ`. `liftedProduct?` returns `none` unless `ℓ ≥ 1` and `A` actually has the
declared `rA × nA` shape; `mkLiftedProduct` reports the specific failure as `degenerateParam`
or `badDimension`.

## Example

The raw constructor input — a `1×2` ring matrix `A = [1, x]` at `ℓ = 3` (each circulant
is an exponent list: `[0]` = `1`, `[1]` = `x`):

```lean
-- Lifted product tiny: ℓ=3, A = [1, x] (1×2 ring matrix).
Internal.liftedProduct 3 [[[0], [1]]] 1 2
-- ⇒ a CSSCode with  n = (1²+2²)·3 = 15  and  cssCondition = true  (hx·hzᵀ = 0)
```

The checked `?`-variant gates the same input on its declared `rA × nA` shape:

```lean
liftedProduct? 3 [[[0], [1]]] 1 2   -- OK: declared 1×2 = actual ⇒ some (… 15-qubit code …)
liftedProduct? 3 [[[0], [1]]] 2 2   -- rejected: declared rA=2 ≠ actual 1 ⇒ none
mkLiftedProduct 3 [[[0], [1]]] 1 2  -- OK: .ok ⟨…⟩  (CheckedCSSCode)
```

A `1×2` ring matrix `A = [1, x]` at `ℓ = 3` yields a 15-qubit CSS code whose
`hx · hzᵀ = 0` (the CSS condition) holds. Source:
[Basic.lean](Basic.lean) (lines 31–33, 43–44), [Checked.lean](Checked.lean) (line 27).

## Status & scope

- The `by decide` lines (`.n = 15`, `.cssCondition = true`, `liftedProduct?`/`mkLiftedProduct`
  accept/reject) are D-tier executable tests in the CONTRACT sense — they confirm the
  construction computes the declared dimensions and satisfies the CSS condition on the cited
  example inputs only. They are concrete checks, not general theorems over all `A`, `ℓ`.
- The doc-comment claim that `hx·hzᵀ = 0` "because `transpose (lift A*) = lift A`" is stated as
  the construction's design rationale; no general parametric proof of `cssCondition = true` for
  arbitrary lifted-product inputs is provided in this folder.
- Shape checking is real and executable: `liftedProduct?` / `mkLiftedProduct` reject `ℓ = 0` and
  any `A` not matching the declared `rA × nA` shape.
- Out of scope here (consistent with the rest of LogicQ): code distance, decoder correctness,
  fault-tolerance, and operational/channel claims. These are not asserted or proved in this folder.

## See also

- [../README.md](../README.md) — ChainQ front-end code type system and sibling families.
- [../Checked/README.md](../Checked/README.md) — the `CheckedCSSCode` / `ChainQError` machinery
  that `mkLiftedProduct` returns into.
- [../../README.md](../../README.md) — LogicQ repository root.
