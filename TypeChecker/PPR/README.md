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

There is no checker code in this folder to quote. The closest concrete artifact
is the rotation-layer **composition law** in [`PPR/Semantics.lean`](../../PPR/Semantics.lean),
the proved law a future PPR pass would build on:

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
