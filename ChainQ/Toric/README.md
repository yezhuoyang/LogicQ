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

```lean
/-- A successful `mkToric` yields exactly `toric d`, and it is valid. -/
theorem mkToric_sound {d : Nat} {cc : CheckedCSSCode} (h : mkToric d = .ok cc) :
    cc.code = toric d ∧ cc.code.valid = true := by
  unfold mkToric at h
  split at h
  · contradiction
  · exact ⟨mkCSS_sound h, cc.valid⟩
```

The soundness theorem: whenever `mkToric d` returns `.ok cc`, the underlying code is exactly `toric d` and it satisfies the CSS validity check (`Hx * Hzᵀ = 0`). Source: [Checked.lean](Checked.lean).

## Status & scope

- **P (proved theorem):** `mkToric_sound` is a `∀`-quantified soundness theorem — a successful checked construction yields exactly `toric d` and a valid CSS code.
- **D (`by decide` test):** Concrete-parameter facts in [Basic.lean](Basic.lean) — `(toric 3).n = 18`, `(toric 3).valid = true`, `(toric 2).valid = true`, `(toric? 2).isSome = true`, `(toric? 0) = none`, and `isOk (mkToric 2) = true` in [Checked.lean](Checked.lean).
- **Scope of validity:** `valid = true` here means the materialized CSS checks commute (`Hx * Hzᵀ = 0`), and `mkToric`/`toric?` reject degenerate parameters (`d < 2`). This is a structural/algebraic guarantee only.
- **Deferred:** the `[[2d², 2, d]]` claim records the intended `n`, `k`, and code **distance** `d`; the distance/`k` values are documented parameters, NOT proved here. No channel-correctness, fault-tolerance, decoder, or operational-equivalence claim is made in this folder. Soundness is `propext`-style clean, not "axiom-free."

## See also

- [../README.md](../README.md) — the ChainQ front-end overview (code views, validity rules, family constructors).
- [../HGPCode/README.md](../HGPCode/README.md) — the hypergraph-product machinery (`Internal.hgp`, `repCyc`) that `toric` is built on.
- [../Checked/README.md](../Checked/README.md) — the validity-carrying `CheckedCSSCode` / `mkCSS` constructors used by `mkToric`.
