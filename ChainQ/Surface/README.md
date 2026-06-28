# ChainQ/Surface

> The (unrotated) surface-code family, built as a hypergraph product of two open repetition codes.

This folder is one of the parametric code families in the **ChainQ** front-end, the layer where concrete `CSSCode` values are constructed before legality is checked by the TypeChecker and lowered through the Compiler's Mixed IR toward the QStab/QClifford physical target. `surface d` is not a symbolic placeholder: for a fixed distance `d` it computes the concrete GF(2) check matrices `hx`/`hz` of the `[[d²+(d−1)², 1, d]]` code via the HGP construction. The folder also provides checked constructors (`surface?`, `mkSurface`) that reject the degenerate `d < 2` and carry a validity proof.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Defines `surface d` as `Internal.hgp (repOpen d) (repOpen d) …`; the checked `surface?`; and `decide` tests for dimensions, shapes, and the CSS condition. |
| [Checked.lean](Checked.lean) | The `Except`-returning `mkSurface` constructor, its soundness theorem `mkSurface_sound`, and executable tests for the full checked pipeline. |

## Key definitions

```lean
def surface (d : Nat) : CSSCode := Internal.hgp (repOpen d) (repOpen d) (d - 1) d (d - 1) d
```

```lean
def surface? (d : Nat) : Option CSSCode := if 2 ≤ d then some (surface d) else none
```

```lean
def mkSurface (d : Nat) : Except ChainQError CheckedCSSCode :=
  if d < 2 then .error (.degenerateParam "surface code needs d ≥ 2")
  else mkCSS (surface d)
```

```lean
theorem mkSurface_sound {d : Nat} {cc : CheckedCSSCode} (h : mkSurface d = .ok cc) :
    cc.code = surface d ∧ cc.code.valid = true
```

## Example

```lean
-- Surface code: n = d² + (d−1)².
example : (surface 2).n = 5 := by decide
example : (surface 3).n = 13 := by decide
example : (surface 2).valid = true := by decide
example : (surface 3).valid = true := by decide
example : hasShape (surface 3).hx 6 13 = true := by decide   -- 6 X-checks on 13 qubits
example : hasShape (surface 3).hz 6 13 = true := by decide
```

These `by decide` checks (from [Basic.lean](Basic.lean)) confirm that `surface 3` materializes to a `[[13, …]]` code with the expected `6 × 13` X- and Z-check matrices and a satisfied CSS condition (`Hx * Hzᵀ = 0`).

## Status & scope

- **P (proved theorem)** — `mkSurface_sound` is a `∀`-theorem: a successful `mkSurface d` yields exactly `surface d` together with `cc.code.valid = true`. It is established by `unfold`/`split` plus `mkCSS_sound` and the validity field of `CheckedCSSCode`.
- **D (`by decide` tests)** — concrete dimensions (`n = 5`, `n = 13`), shapes (`hasShape … 6 13`), CSS validity, the `d < 2` rejection (with the right `degenerateParam` reason), and the checked pipeline reaching `mkLogicalBasis` are verified by `decide` for the small fixed cases shown.
- **Scope of validity** — `valid = true` here means the CSS commutation condition `Hx · Hzᵀ = 0` holds (the usual condition inherited from the HGP construction); it does **not** by itself assert the code distance is `d`, nor any fault-tolerance, decoder, or channel-correctness property. Those remain **deferred** to downstream layers per the repository contract.
- No `Step`/operational-semantics or physical-channel claims are made at this layer.

## See also

- [../README.md](../README.md) — the ChainQ front-end overview (code views, validity rules, family list).
- [../HGPCode/README.md](../HGPCode/README.md) — the hypergraph-product and repetition-code constructors that `surface` is built on.
- [../Checked/README.md](../Checked/README.md) — `CheckedCSSCode`, `mkCSS`, and `mkLogicalBasis` used by `mkSurface`.
- [../../README.md](../../README.md) — the LogicQ repository root.
