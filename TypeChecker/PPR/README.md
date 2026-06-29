# TypeChecker/PPR

> Reserved slot for a future PPR (Pauli-Product-Rotation) typing / optimization pass.

This directory is a **placeholder** inside the TypeChecker legality layer
(front-end ChainQ code families → **TypeChecker** legality → Compiler Mixed IR →
… → QStab/QClifford physical target). It is intended to host static checks over
the PPR IR — the rotation level `L_PPR` whose `π/8` count is the program's
T-count. Today that IR exists and has denotational semantics, but **no
typechecker pass is wired here yet**: this folder contains only this README.

## What's here

This folder owns **no `.lean` modules** and **no subdirectories** — it is a
documented stub. The PPR IR it is reserved to check lives in the top-level
[`PPR/`](../../PPR/) package:

| Module | Role |
| --- | --- |
| [`PPR/Basic.lean`](../../PPR/Basic.lean) | Umbrella; re-exports the syntax and semantics of `L_PPR`. |
| [`PPR/Syntax.lean`](../../PPR/Syntax.lean) | Mathlib-free data: `Pauli`, `PauliString`, `Angle`, `Phase`, `Rot`, `RotProg`, plus `wf`/`tCount`. |
| [`PPR/Semantics.lean`](../../PPR/Semantics.lean) | Denotational semantics: a rotation `exp(i φ P)` as a monomial complex matrix. |

## Key definitions

The IR this slot is reserved to type-check (from `PPR/Syntax.lean` and
`PPR/Semantics.lean`):

```lean
structure Rot where
  phase : Phase
  pauli : PauliString
```

```lean
/-- The **T-count** of a PPR program: the number of `π/8` rotations.  This is
    the resource invariant the lowering to PPM must preserve. -/
def RotProg.tCount (p : RotProg) : Nat := (p.filter Rot.isT).length
```

```lean
noncomputable def RotProg.denote (n : Nat) (lay : LQubit → Fin n) (p : RotProg) :
    Matrix (BitStr n) (BitStr n) ℂ :=
  p.foldl (fun acc r => Rot.denote n lay r * acc) 1
```

## Example

There is no checker code in this folder to quote. The concrete artifacts are
the PPR **programs** the IR represents — sequences of logical Pauli-product
rotations. Each logical gate is one rotation `exp(i φ P)`; these are the actual
worked values from [`PPR/Syntax.lean`](../../PPR/Syntax.lean#L104):

```lean
-- A logical T on q: the +π/8 Z-rotation exp(i π/8 Z)  (T-type, π/8)
def rotT (q : LQubit) : Rot := ⟨⟨false, .piEighth⟩, [(q, .Z)]⟩
-- A logical S on q: the +π/4 Z-rotation             (Clifford, π/4)
def rotS (q : LQubit) : Rot := ⟨⟨false, .piQuarter⟩, [(q, .Z)]⟩
-- A two-qubit π/8 rotation about Z⊗Z over {q₁,q₂}     (T-type, π/8)
def rotZZ (q₁ q₂ : LQubit) : Rot := ⟨⟨false, .piEighth⟩, [(q₁, .Z), (q₂, .Z)]⟩
```

A `RotProg` is just a list of these rotations applied left to right. The
T-count is the number of `π/8` rotations, and the program is well-formed when
every axis lists at most one factor per logical qubit
([`PPR/Syntax.lean`](../../PPR/Syntax.lean#L116)):

```lean
-- A 3-rotation PPR program over logical qubits ⟨0,0⟩ and ⟨0,1⟩:
[ rotT ⟨0, 0⟩                  -- +π/8 · (⟨0,0⟩↦Z)
, rotS ⟨0, 0⟩                  -- +π/4 · (⟨0,0⟩↦Z)
, rotZZ ⟨0, 0⟩ ⟨0, 1⟩ ]        -- +π/8 · (⟨0,0⟩↦Z, ⟨0,1⟩↦Z)
-- tCount = 2   (the two π/8 rotations: rotT and rotZZ; rotS is Clifford)
-- wf     = true (every axis is duplicate-qubit-free)

(rotZZ ⟨0, 0⟩ ⟨0, 1⟩).support = [⟨0, 0⟩, ⟨0, 1⟩]   -- OK: the rotation acts on {⟨0,0⟩, ⟨0,1⟩}

-- A malformed axis (two factors on the same logical qubit):
[(⟨0, 0⟩, .Z), (⟨0, 0⟩, .X)]   -- rejected: PauliString.wf = false (duplicate logical qubit)
```

The closest concrete *proved* artifact is the rotation-layer **composition law**
in [`PPR/Semantics.lean`](../../PPR/Semantics.lean), the law a future PPR pass
would build on:

```lean
/-- **Composition law.**  The unitary of a concatenated program is the product
    of the parts, in reverse order (later rotations act on the left): running
    `p` then `q` is `denote q * denote p`.  This is the form the end-to-end
    correctness threads through the rotation layer. -/
theorem denote_append (n : Nat) (lay : LQubit → Fin n) (p q : RotProg) :
    RotProg.denote n lay (p ++ q)
      = RotProg.denote n lay q * RotProg.denote n lay p := by
  simp only [RotProg.denote, List.foldl_append]
  exact foldl_mul_one (Rot.denote n lay) q
    (List.foldl (fun acc r => Rot.denote n lay r * acc) 1 p)
```

This `theorem` is **proved** in the IR package, not in this folder; see
[`PPR/Semantics.lean`](../../PPR/Semantics.lean).

## Status & scope

- **(M) Missing / planned.** This `TypeChecker/PPR/` folder contains **no Lean
  code** — no syntax, no judgment, no soundness theorem. It is a reserved slot
  for a future PPR typing / optimization checker, and nothing here is wired into
  the TypeChecker pipeline.
- The PPR **IR itself** (under top-level [`PPR/`](../../PPR/)) does exist:
  `RotProg.wf` / `RotProg.tCount` are total `Bool`/`Nat` functions exercised by
  `by decide` examples **(D)**, and the denotational laws `rotOf_zero`,
  `denote_nil`, `denote_singleton`, `foldl_mul_one`, `denote_append` are
  **proved (P)** in `PPR/Semantics.lean`.
- **Deferred / not claimed here:** there is no PPR legality judgment,
  no `Except TypeError` rule, no soundness theorem, and no lowering-correctness
  obligation connecting PPR to PPM/QStab in this folder. Do not read this slot
  as providing any verified PPR check today. The lowering and any
  optimization-preservation results remain future work.

## See also

- [`../README.md`](../README.md) — the parent TypeChecker legality layer.
- [`../../PPR/Basic.lean`](../../PPR/Basic.lean) — the PPR IR umbrella module this slot is reserved to type-check.
- [`../../README.md`](../../README.md) — repository root overview.
