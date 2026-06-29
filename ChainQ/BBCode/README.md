# ChainQ/BBCode

> Bivariate-bicycle (BB) qLDPC code constructor for the ChainQ front-end.

This folder is one of the parametric code families in `ChainQ`, the front-end
code type system of the LogicQ verified compiler stack. It builds concrete
`CSSCode` values from bivariate monomial data over `F₂[x,y]/(xˡ−1, yᵐ−1)`, with
the CSS condition (`Hx·Hzᵀ = 0`) verified per-instance by `decide`. These
`CSSCode` values feed the rest of the stack (TypeChecker legality → Compiler
Mixed IR → … → QStab/QClifford physical target).

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Raw internal `bb` constructor + the `Option`-valued `bb?` checked variant, with dimension/shape/CSS `decide` tests. |
| [Checked.lean](Checked.lean) | The `Except ChainQError`-valued `mkBB` constructor with accept/reject `decide` tests. |

## Key definitions

```lean
-- ChainQ/BBCode/Basic.lean
def bb (l m : Nat) (a b : List (Nat × Nat)) : CSSCode :=
  let A := biCirculant l m a
  let B := biCirculant l m b
  { n  := 2 * l * m,
    hx := hcat A B,
    hz := hcat (transpose B (l * m)) (transpose A (l * m)) }
```

```lean
-- ChainQ/BBCode/Basic.lean
def bb? (l m : Nat) (a b : List (Nat × Nat)) : Option CSSCode :=
  if decide (1 ≤ l) && decide (1 ≤ m) && !a.isEmpty && !b.isEmpty
  then some (Internal.bb l m a b) else none
```

```lean
-- ChainQ/BBCode/Checked.lean
def mkBB (l m : Nat) (a b : List (Nat × Nat)) : Except ChainQError CheckedCSSCode :=
  if ! (decide (1 ≤ l) && decide (1 ≤ m)) then
    .error (.degenerateParam "BB: ℓ and m must be ≥ 1")
  else if a.isEmpty || b.isEmpty then
    .error (.degenerateParam "BB: A and B must be nonempty")
  else mkCSS (Internal.bb l m a b)
```

`bb` is the raw (`⚠ INTERNAL`, shape-unchecked) constructor; `bb?` and `mkBB`
are the checked wrappers that reject `ℓ = 0`, `m = 0`, or empty `A`/`B`.

## Example

A concrete BB code value — the bivariate-bicycle instance with `ℓ = m = 3`,
`A = 1 + x + y²` (exponents `[(0,0),(1,0),(0,2)]`), `B = 1 + x² + y` (exponents
`[(0,0),(2,0),(0,1)]`):

```lean
-- The BB program/value (raw constructor): n = 18, CSS ✓, hx is a 9×18 matrix.
Internal.bb 3 3 [(0,0),(1,0),(0,2)] [(0,0),(2,0),(0,1)]
--   .n            = 18          -- n = 2·ℓ·m
--   .cssCondition = true        -- Hx·Hzᵀ = A·B + B·A = 0
--   .hx           : 9 × 18      -- hasShape … 9 18
```

The same parameters through the checked wrappers (`bb?`, `mkBB`):

```lean
bb? 3 3 [(0,0),(1,0),(0,2)] [(0,0),(2,0),(0,1)]   -- OK: some (the n = 18 instance)
bb? 0 3 [(0,0)] [(0,0)]                            -- rejected: ℓ = 0 ⇒ none

mkBB 3 3 [(0,0),(1,0),(0,2)] [(0,0),(2,0),(0,1)]  -- OK: a CheckedCSSCode
mkBB 0 3 [(0,0)] [(0,0)]                           -- rejected: degenerateParam "BB: ℓ and m must be ≥ 1"
```

Source: [Basic.lean](Basic.lean) (§4 Tests), [Checked.lean](Checked.lean) (§4 Tests).

## Status & scope

- **D (`by decide`)** — Correctness here is per-instance, not universal. The
  CSS condition, dimensions, and check-matrix shapes are validated by `decide`
  on fixed parameters (`Basic.lean` §4, §5; `Checked.lean` §4), including the
  accept/reject behavior of the checked constructors.
- **A (assumption / grounding note)** — Per the header in
  [Basic.lean](Basic.lean), the BB family originates with Bravyi et al. 2024
  (not vendored in `Library/`); this constructor follows the BB-style codes as
  used in the universal-adapters paper arXiv:2410.03628. The `hx·hzᵀ = A·B +
  B·A = 0` rationale (circulants commute) is stated in the doc comment as
  motivation, not proved as a `∀`-theorem.
- **M (planned / not here)** — No distance, decoder, fault-tolerance, or
  channel-correctness claims are made in this folder. There is no universal
  theorem that `bb l m a b` always satisfies the CSS condition for arbitrary
  inputs; legality is checked per-instance downstream.

## See also

- [../README.md](../README.md) — ChainQ front-end code type system overview and
  sibling code families.
- Parent `ChainQ` definitions this folder uses: `biCirculant`/`hcat`/`transpose`
  (Algebra), `CSSCode`/`ChainQError` (Core), `mkCSS`/`isOk` (Checked).
