# PPR — Pauli-Product Rotations

> The logical Pauli-product-rotation IR (level `L_PPR`): a program is a sequence of `exp(i φ P)` rotations over logical qubits.

A PPR program is a sequence of **logical** Pauli-product rotations `exp(i φ P)`, with the phase `φ` a signed dyadic fraction of π in Litinski's set `±{π, π/2, π/4, π/8}` and `P` a logical Pauli string. In the LogicQ stack PPR sits above [PPM](../PPM): it is the high-level "logical gates as rotations" view, and the `π/8` count (`RotProg.tCount`) is exactly the T-count the lowering to PPM must preserve. Everything here is at the logical level — there are no physical qubits in the syntax — and the denotational semantics fixes each rotation as a concrete monomial complex matrix under a qubit layout.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Umbrella module; re-exports `Syntax` and `Semantics` |
| [Syntax.lean](Syntax.lean) | Pure data: `Pauli`, `PauliString`, `Angle`, `Phase`, `Rot`, `RotProg`, well-formedness and T-count, worked-example gates (`rotT`/`rotS`/`rotZZ`) |
| [Parse.lean](Parse.lean) | Total text parser `parsePPR : String → Except ParseError RotProg` for the surface syntax; round-trip tests are `by decide` |
| [Semantics.lean](Semantics.lean) | Mathlib denotation: dense-Pauli monomial matrices, `rotOf`/`Rot.denote`/`RotProg.denote`, and the composition law `denote_append` |

## Key definitions

```lean
/-- A single-qubit Pauli (`I` is represented by the ABSENCE of a factor). -/
inductive Pauli
  | X | Y | Z
  deriving DecidableEq, Repr, Inhabited
```

```lean
/-- A **Pauli-product rotation** `exp(i φ P)` — the PPR primitive: a phase `φ`
    together with the logical Pauli string `P` it rotates about. -/
structure Rot where
  phase : Phase
  pauli : PauliString
  deriving Repr, Inhabited, DecidableEq
```

```lean
/-- The **T-count** of a PPR program: the number of `π/8` rotations.  This is
    the resource invariant the lowering to PPM must preserve. -/
def RotProg.tCount (p : RotProg) : Nat := (p.filter Rot.isT).length
```

```lean
/-- `rotOf φ M = cos φ · 1 + (i · sin φ) · M` — the rotation `exp(i φ P)` for an
    involutive `M = axisMat P`. -/
noncomputable def rotOf {n : Nat} (φ : ℝ) (M : Matrix (BitStr n) (BitStr n) ℂ) :
    Matrix (BitStr n) (BitStr n) ℂ :=
  (↑(Real.cos φ) : ℂ) • (1 : Matrix (BitStr n) (BitStr n) ℂ)
    + (Complex.I * ↑(Real.sin φ)) • M
```

```lean
/-- **Composition law.**  The unitary of a concatenated program is the product
    of the parts, in reverse order (later rotations act on the left). -/
theorem denote_append (n : Nat) (lay : LQubit → Fin n) (p q : RotProg) :
    RotProg.denote n lay (p ++ q)
      = RotProg.denote n lay q * RotProg.denote n lay p
```

## Example

```lean
/-- A logical **T** on `q`: the `+π/8` Z-rotation `exp(i π/8 Z)`. -/
def rotT (q : LQubit) : Rot := ⟨⟨false, .piEighth⟩, [(q, .Z)]⟩
/-- A logical **S** on `q`: the `+π/4` Z-rotation. -/
def rotS (q : LQubit) : Rot := ⟨⟨false, .piQuarter⟩, [(q, .Z)]⟩
/-- A two-qubit logical `π/8` rotation about `Z⊗Z` over the set `{q₁, q₂}`. -/
def rotZZ (q₁ q₂ : LQubit) : Rot := ⟨⟨false, .piEighth⟩, [(q₁, .Z), (q₂, .Z)]⟩

-- A 3-rotation PPR program over logical block 0 (LQubit ⟨blk, idx⟩):
--   exp(i·+π/8 · Z₀)         -- T   on q0   (π/8 ⇒ T-type)
--   exp(i·+π/4 · Z₀)         -- S   on q0   (π/4 ⇒ Clifford)
--   exp(i·+π/8 · Z₀⊗Z₁)      -- ZZ  on {q0,q1} (π/8 ⇒ T-type)
[ rotT ⟨0, 0⟩            -- ⟨⟨false, .piEighth⟩,  [(⟨0,0⟩, .Z)]⟩
, rotS ⟨0, 0⟩            -- ⟨⟨false, .piQuarter⟩, [(⟨0,0⟩, .Z)]⟩
, rotZZ ⟨0, 0⟩ ⟨0, 1⟩ ] -- ⟨⟨false, .piEighth⟩,  [(⟨0,0⟩, .Z), (⟨0,1⟩, .Z)]⟩
-- tCount = 2   -- the two π/8 rotations (T and ZZ); the π/4 S does not count
-- OK: wf = true   -- every axis names each logical qubit at most once
```

Logical T/S/`ZZ` gates built as concrete `Rot` values; the program above is the literal `RotProg` whose T-count is exactly the two `π/8` rotations and which is well-formed (each axis names a logical qubit at most once). Source: [Syntax.lean](Syntax.lean) (lines 104–117).

The same program has a surface syntax that **parses today** ([Parse.lean](Parse.lean), tests by `decide`). A `Phase` is a sign `+`/`-` and an `Angle` in `π | π/2 | π/4 | π/8`; a `Rot` is `Phase · PauliString`, where a `PauliString` is space-separated `q[i] ↦ P` factors (`P ∈ {X, Y, Z}`); rotations are separated by newlines or `;`. Block names (`q`, `a`, …) are interned to `Logical.BlockId`s in first-occurrence order.

```text
+π/8 · q[0]↦Z              // T   on q[0]      (π/8 ⇒ T-type)
+π/4 · q[0]↦Z              // S   on q[0]      (π/4 ⇒ Clifford)
+π/8 · q[0]↦Z q[1]↦Z      // ZZ  on {q[0],q[1]} (π/8 ⇒ T-type)
```

This text parses (via `PPR.Parse.parsePPR`) to exactly `[rotT ⟨0,0⟩, rotS ⟨0,0⟩, rotZZ ⟨0,0⟩ ⟨0,1⟩]`, with `tCount = 2` — the same `RotProg` shown in Lean above ([Parse.lean](Parse.lean), lines 93–98).

## Status & scope

- **Proved (P).** The semantic laws in [Semantics.lean](Semantics.lean) are real Mathlib theorems: `rotOf_zero`, `denote_nil`, `denote_singleton`, the monoid helper `foldl_mul_one`, and the composition law `denote_append` (running `p` then `q` denotes `denote q * denote p`).
- **Decided (D).** The worked-example facts in [Syntax.lean](Syntax.lean) (`isT`, `support`, `wf`, `tCount`) are `by decide` tests on concrete programs.
- **Assumed / modeled (A).** The denotation is an ideal-channel, noiseless unitary model: `rotOf` uses the involutive closed form `cos φ · 1 + i sin φ · M`, and `axisMat` is a layout-parameterized monomial matrix (no tensor/Kronecker machinery). The logical→physical layout `lay : LQubit → Fin n` is a free parameter; it is **not** verified that `axisMat (denseOf …)` is involutive, nor that `rotOf` equals a true matrix exponential — these are taken as the operational meaning of a rotation.
- **Missing / planned (M).** No lowering from PPR into PPM is defined in this folder, so the stated T-count preservation invariant is **documented intent, not a proved theorem** here. No fault-tolerance, distance, decoder, or operational-equivalence claims are made.

This module is `Mathlib`-pinned (same Mathlib as FormalRV) in `Semantics.lean`; `Syntax.lean` is Mathlib-free pure data.

## See also

- [Repository README](../README.md) — the full LogicQ verified-compiler stack
- [PPM](../PPM) — the Pauli-product-measurement layer that PPR lowers into
