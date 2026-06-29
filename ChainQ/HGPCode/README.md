# ChainQ/HGPCode

> Tillich–Zémor hypergraph-product (HGP) CSS code family and its classical repetition-code inputs.

This folder is part of the **ChainQ** front-end code-family layer of the LogicQ stack: it constructs CSS quantum codes from a pair of classical parity-check matrices via the hypergraph product (arXiv 0903.0566). Downstream these `CSSCode` / `CheckedCSSCode` values feed the TypeChecker legality layer, the Compiler Mixed IR, and ultimately the QStab/QClifford physical target. The HGP of two repetition codes is the surface code, which is defined separately in [`ChainQ/Surface`](../Surface/README.md).

## What's here

| Module | Role |
| --- | --- |
| [Repetition.lean](Repetition.lean) | Classical open-boundary (`repOpen`) and cyclic (`repCyc`) repetition parity-check matrices used as HGP inputs |
| [Basic.lean](Basic.lean) | Raw shape-unchecked HGP constructor `Internal.hgp` and the `Option`-valued checked variant `hgp?` |
| [Checked.lean](Checked.lean) | `Except`-valued constructor `mkHGP` returning a `CheckedCSSCode` (or a typed `ChainQError`) |

## Key definitions

```lean
/-- Open-boundary distance-`d` repetition code: `(d−1)×d`, row `i` has `1`s at
    columns `i` and `i+1`. -/
def repOpen (d : Nat) : BoolMat
```

```lean
/-- HGP of classical `h1` (`m1×n1`) and `h2` (`m2×n2`):
    `hx = [h1⊗I_{n2} | I_{m1}⊗h2ᵀ]`, `hz = [I_{n1}⊗h2 | h1ᵀ⊗I_{m2}]`,
    `n = n1·n2 + m1·m2`.  Satisfies `hx·hzᵀ = h1⊗h2ᵀ + h1⊗h2ᵀ = 0`. -/
def hgp (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : CSSCode
```

```lean
/-- Checked HGP: `none` unless the declared shapes match the actual matrices and
    every dimension is ≥ 1. -/
def hgp? (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : Option CSSCode
```

```lean
/-- Hypergraph product; rejects declared-vs-actual shape disagreement and any
    zero dimension. -/
def mkHGP (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat) : Except ChainQError CheckedCSSCode
```

## Example

The classical input is `repOpen 3`, the distance-3 open-boundary repetition code — a
`2×3` `BoolMat` (row `i` has `1`s at columns `i`, `i+1`):

```lean
-- repOpen 3 : BoolMat   (2 rows × 3 cols, so its true shape is m = 2, n = 3)
[[true, true, false],
 [false, true, true]]
```

Feeding two copies to the checked HGP constructor:

```lean
-- mkHGP (repOpen 3) (repOpen 3) 2 3 2 3
--   OK: declared shapes (m1=2,n1=3,m2=2,n2=3) match the actual 2×3 matrices.
--       ⇒ .ok (CheckedCSSCode with n = n1·n2 + m1·m2 = 3·3 + 2·2 = 13)

-- mkHGP (repOpen 3) (repOpen 3) 5 3 2 3
--   rejected: declared m1 = 5 disagrees with the actual matrix shape (2 rows).
--       ⇒ .error (.badDimension "HGP: a declared dimension disagrees with the actual matrix shape")
```

These two values show `mkHGP` accepting a well-shaped HGP of two distance-3 repetition
codes, and rejecting a declared `m1 = 5` that disagrees with the actual matrix shape `2` —
returning the specific `.badDimension` error. Source: [Checked.lean](Checked.lean).

## Status & scope

- **D (`by decide` executable tests):** The accept/reject behaviour of `hgp?` and `mkHGP` is exercised by the `by decide` examples in [Basic.lean](Basic.lean) and [Checked.lean](Checked.lean) (declared-vs-actual shape match, wrong-dimension rejection with the right error constructor).
- **A (documented construction):** The CSS-validity identity `hx·hzᵀ = 0` is stated in the `Internal.hgp` docstring as the design rationale; the packaged `CheckedCSSCode` from `mkHGP` carries whatever proof `mkCSS` (in [`ChainQ/Checked`](../Checked/README.md)) provides.
- **M / deferred:** No code **distance**, decoder, fault-tolerance, or channel-correctness claims are made here. Distance bounds (e.g. for the derived surface code) live elsewhere (`ChainQ/Core/Distance.lean`) and are out of scope for this folder. `repOpen`/`repCyc` are plain parity-check builders with no proved minimum-distance guarantee in this folder.

Bodies in this folder were split out verbatim from `ChainQ.Families` / `ChainQ.Checked` per the module headers; this README does not upgrade any of those into stronger claims.

## See also

- Parent layer: [../README.md](../README.md)
- Checked-code wrapper used by `mkHGP`: [../Checked/README.md](../Checked/README.md)
- Surface code = HGP of two repetition codes: [../Surface/README.md](../Surface/README.md)
- Repo root: [../../README.md](../../README.md)
