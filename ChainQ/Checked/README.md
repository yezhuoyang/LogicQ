# ChainQ/Checked

> Validity-carrying public constructors: a code object that carries its own well-formedness proof.

This is the sound boundary between the raw `ChainQ` code-family data (`CSSCode`, `CSSLogicalBasis`) and everything downstream. A value of `CheckedCSSCode`/`CheckedLogicalBasis` literally bundles a proof that the code (or basis) validates, so a malformed code can never be smuggled into the TypeChecker legality layer, the Compiler Mixed IR, or the QStab/QClifford physical target. It sits at the front-end ChainQ layer of the LogicQ stack, immediately above the raw parameter/error definitions in `ChainQ`.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | The shared base of the typed ChainQ front-end core: the `Checked*` structures, the `Except`-returning constructors `mkCSS`/`mkLogicalBasis`, their soundness theorems, and an executable rejection test. |

## Key definitions

```lean
structure CheckedCSSCode where
  code  : CSSCode
  valid : code.valid = true
```

```lean
structure CheckedLogicalBasis where
  code  : CSSCode
  basis : CSSLogicalBasis
  valid : CSSLogicalBasis.valid code basis = true
```

```lean
def mkCSS (c : CSSCode) : Except ChainQError CheckedCSSCode
def mkLogicalBasis (cc : CheckedCSSCode) : Except ChainQError CheckedLogicalBasis
```

```lean
theorem mkCSS_sound {c : CSSCode} {cc : CheckedCSSCode} (h : mkCSS c = .ok cc) :
    cc.code = c
theorem mkLogicalBasis_sound {cc : CheckedCSSCode} {clb : CheckedLogicalBasis}
    (h : mkLogicalBasis cc = .ok clb) :
    clb.code = cc.code ∧ deriveLogicalBasis? cc.code = some clb.basis
```

## Example

```lean
-- rejects, with the RIGHT reason:
example : (match mkCSS { n := 2, hx := [[true, false]], hz := [[true, false]] } with
           | .error (.invalidCSS _) => true | _ => false) = true := by decide
```

`mkCSS` rejects a code whose X- and Z-checks anticommute (`Hx·Hzᵀ ≠ 0`) and reports it as an `.invalidCSS` error, verified by `decide`. Source: [Basic.lean](Basic.lean).

## Status & scope

- **P (proved theorem):** `CheckedCSSCode.code_valid`, `mkCSS_sound`, and `mkLogicalBasis_sound` are genuine `∀`-theorems about the constructors. The structures carry their validity proof in the type, so soundness-by-construction (no `CheckedCSSCode` exists with an invalid `code`) holds definitionally.
- **D (`by decide` test):** the single rejection `example` in [Basic.lean](Basic.lean) is an executable check, not a universal claim.
- **A (assumption / external):** `mkLogicalBasis` delegates basis derivation/validation to `deriveLogicalBasis?` and its soundness lemma `deriveLogicalBasis?_sound`, which live outside this folder (in `ChainQ`); their correctness is assumed here.
- **Out of scope / deferred:** nothing in this folder makes any channel-correctness, fault-tolerance, distance, decoder, or operational-equivalence claim. This layer only certifies *static well-formedness* of CSS codes and logical bases; all physical/operational guarantees are established (or deferred) elsewhere in the stack.

## See also

- Parent: [../README.md](../README.md)
- Repo root: [../../README.md](../../README.md)
