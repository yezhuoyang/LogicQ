# ChainQ/Toric

> The toric-code family: the hypergraph product (HGP) of two cyclic repetition codes, with its validity-carrying checked constructor.

This folder sits in the **ChainQ front-end** of the LogicQ stack, where parametric quantum-code families construct concrete `CSSCode` values that later layers (TypeChecker legality -> Compiler Mixed IR -> QStab/QClifford physical target) consume. `toric d` is defined as `HGP(repCyc d, repCyc d)`, yielding the `[[2d², 2, d]]` family, and `mkToric` wraps it in an `Except`-based constructor with a proved soundness theorem.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Defines `toric` (raw `CSSCode`) and `toric?` (`Option`-checked variant); `decide` tests for dimensions, validity, and parameter rejection. |
| [Checked.lean](Checked.lean) | Defines `mkToric` (`Except ChainQError CheckedCSSCode`), proves `mkToric_sound`, and an executable accept test. |

## Key definitions

```lean
def toric (d : Nat) : CSSCode := Internal.hgp (repCyc d) (repCyc d) d d d d
```

```lean
def toric? (d : Nat) : Option CSSCode := if 2 ≤ d then some (toric d) else none
```

```lean
def mkToric (d : Nat) : Except ChainQError CheckedCSSCode :=
  if d < 2 then .error (.degenerateParam "toric code needs d ≥ 2")
  else mkCSS (toric d)
```

```lean
theorem mkToric_sound {d : Nat} {cc : CheckedCSSCode} (h : mkToric d = .ok cc) :
    cc.code = toric d ∧ cc.code.valid = true
```

## Example

The toric family is built from cyclic repetition codes. `repCyc d` is the `d×d`
parity-check matrix with `1`s at columns `i` and `(i+1) mod d` in row `i`
([Repetition.lean:22](../HGPCode/Repetition.lean#L22)):

```lean
-- repCyc 2  (the input code for toric 2)
[ [1, 1]
, [1, 1] ]

-- repCyc 3  (the input code for toric 3)
[ [1, 1, 0]
, [0, 1, 1]
, [1, 0, 1] ]
```

`toric d = HGP(repCyc d, repCyc d)`, so `toric 2` is the `[[8, 2, 2]]` code and
`toric 3` is the `[[18, 2, 3]]` code. The concrete materialized values
([Basic.lean:22](Basic.lean#L22), [Checked.lean:33](Checked.lean#L33)):

```lean
toric 3 . n      = 18      -- OK: n = 2·3²
toric 3 . valid  = true    -- OK: Hx · Hzᵀ = 0
toric 2 . valid  = true    -- OK: Hx · Hzᵀ = 0

toric? 2 . isSome = true    -- OK: d ≥ 2 accepted ⇒ some (toric 2)
toric? 0          = none    -- rejected: d < 2

mkToric 2  -- OK: .ok ⟨toric 2, valid⟩
mkToric 1  -- rejected: .error (.degenerateParam "toric code needs d ≥ 2")
```

The soundness theorem (stated above): whenever `mkToric d` returns `.ok cc`, the
underlying code is exactly `toric d` and it satisfies the CSS validity check
(`Hx * Hzᵀ = 0`). Source: [Checked.lean](Checked.lean).

## Status & scope

- **P (proved theorem):** `mkToric_sound` is a `∀`-quantified soundness theorem — a successful checked construction yields exactly `toric d` and a valid CSS code.
- **D (`by decide` test):** Concrete-parameter facts in [Basic.lean](Basic.lean) — `(toric 3).n = 18`, `(toric 3).valid = true`, `(toric 2).valid = true`, `(toric? 2).isSome = true`, `(toric? 0) = none`, and `isOk (mkToric 2) = true` in [Checked.lean](Checked.lean).
- **Scope of validity:** `valid = true` here means the materialized CSS checks commute (`Hx * Hzᵀ = 0`), and `mkToric`/`toric?` reject degenerate parameters (`d < 2`). This is a structural/algebraic guarantee only.
- **Deferred:** the `[[2d², 2, d]]` claim records the intended `n`, `k`, and code **distance** `d`; the distance/`k` values are documented parameters, NOT proved here. No channel-correctness, fault-tolerance, decoder, or operational-equivalence claim is made in this folder. Soundness is `propext`-style clean, not "axiom-free."

## See also

- [../README.md](../README.md) — the ChainQ front-end overview (code views, validity rules, family constructors).
- [../HGPCode/README.md](../HGPCode/README.md) — the hypergraph-product machinery (`Internal.hgp`, `repCyc`) that `toric` is built on.
- [../Checked/README.md](../Checked/README.md) — the validity-carrying `CheckedCSSCode` / `mkCSS` constructors used by `mkToric`.
