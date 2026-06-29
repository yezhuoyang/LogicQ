/-
  PPR.Syntax — the Pauli-Product-Rotation IR (level L_PPR).

  A PPR program is a sequence of LOGICAL Pauli-product rotations.  The single,
  obvious primitive is

        Rot  =  a logical Pauli string `P`   +   a phase `φ`        (i.e. `exp(i φ P)`)

  acting on the SET of logical qubits in the support of `P`.  Following Litinski,
  the phase is a signed dyadic fraction of π:

        φ ∈ ± { π , π/2 , π/4 , π/8 }
        π/2 ↦ a Pauli       π/4 ↦ Clifford (S-type)       π/8 ↦ non-Clifford (T-type)

  so the `π/8` count is exactly the T-count (`RotProg.tCount`).

  LOGICAL LEVEL: every factor is over a `Logical.LQubit`; there are no physical
  qubits here.  This file is pure data (Mathlib-free); the denotational
  semantics lives in `PPR/Semantics.lean`.

  Standard-PL BNF:

    Pauli       ::= 'X' | 'Y' | 'Z'                       -- a single-qubit Pauli (I = absent)
    PauliString ::= (LQubit '↦' Pauli)*                   -- a logical Pauli product P
    Angle       ::= 'π' | 'π/2' | 'π/4' | 'π/8'
    Phase       ::= ('+' | '-') Angle                     -- φ = ± Angle
    Rot         ::= Phase '·' PauliString                 -- exp(i φ P)
    RotProg     ::= Rot*                                  -- applied left to right
-/
import Logical.Basic

namespace PPR
open Logical

/-- A single-qubit Pauli (`I` is represented by the ABSENCE of a factor). -/
inductive Pauli
  | X | Y | Z
  deriving DecidableEq, Repr, Inhabited

/-- A **logical Pauli string** `P`: the rotation axis, given by its
    non-identity factors over a set of logical qubits.  Logical qubits not
    listed carry `I`. -/
abbrev PauliString := List (LQubit × Pauli)

/-- The SET of logical qubits a Pauli string acts on (its support). -/
def PauliString.support (P : PauliString) : List LQubit := P.map Prod.fst

/-- A Pauli string is **well-formed** when it has at most one factor per
    logical qubit (a canonical sparse representation). -/
def PauliString.wf (P : PauliString) : Bool := P.support.Nodup

/-- The rotation **angle** magnitude: a dyadic fraction of π (the Litinski set).
    `π/2` realizes a Pauli, `π/4` a Clifford (S-type), `π/8` the non-Clifford
    (T-type) rotation. -/
inductive Angle
  | pi | piHalf | piQuarter | piEighth
  deriving DecidableEq, Repr, Inhabited

/-- A rotation **phase** `φ = ± angle`: a signed dyadic multiple of π
    (`neg = false ↦ +φ`, `neg = true ↦ -φ`). -/
structure Phase where
  neg   : Bool
  angle : Angle
  deriving DecidableEq, Repr, Inhabited

/-- A **Pauli-product rotation** `exp(i φ P)` — the PPR primitive: a phase `φ`
    together with the logical Pauli string `P` it rotates about. -/
structure Rot where
  phase : Phase
  pauli : PauliString
  deriving Repr, Inhabited, DecidableEq

/-- A **PPR program**: a sequence of Pauli-product rotations, applied in order
    (left to right). -/
abbrev RotProg := List Rot

/-! ## Classification and resources. -/

/-- A `π/8` angle is the non-Clifford (T-type) one. -/
def Angle.isT : Angle → Bool
  | .piEighth => true
  | _         => false

/-- A `π/4` angle is the Clifford (S-type) one. -/
def Angle.isClifford : Angle → Bool
  | .piEighth => false
  | _         => true

/-- Whether a rotation is a non-Clifford (`π/8`, T-type) rotation. -/
def Rot.isT (r : Rot) : Bool := r.phase.angle.isT

/-- The set of logical qubits a rotation acts on. -/
def Rot.support (r : Rot) : List LQubit := r.pauli.support

/-- A program is **well-formed** when every rotation's axis is well-formed. -/
def RotProg.wf (p : RotProg) : Bool := p.all (fun r => r.pauli.wf)

/-- The **T-count** of a PPR program: the number of `π/8` rotations.  This is
    the resource invariant the lowering to PPM must preserve. -/
def RotProg.tCount (p : RotProg) : Nat := (p.filter Rot.isT).length

/-! ## Worked examples (logical gates as Pauli rotations). -/

/-- A logical **T** on `q`: the `+π/8` Z-rotation `exp(i π/8 Z)`. -/
def rotT (q : LQubit) : Rot := ⟨⟨false, .piEighth⟩, [(q, .Z)]⟩
/-- A logical **S** on `q`: the `+π/4` Z-rotation. -/
def rotS (q : LQubit) : Rot := ⟨⟨false, .piQuarter⟩, [(q, .Z)]⟩
/-- A two-qubit logical `π/8` rotation about `Z⊗Z` over the set `{q₁, q₂}`. -/
def rotZZ (q₁ q₂ : LQubit) : Rot := ⟨⟨false, .piEighth⟩, [(q₁, .Z), (q₂, .Z)]⟩

example : (rotT ⟨0, 0⟩).isT = true := by decide
example : (rotS ⟨0, 0⟩).isT = false := by decide
example : (rotZZ ⟨0, 0⟩ ⟨0, 1⟩).pauli.wf = true := by decide
example : (rotZZ ⟨0, 0⟩ ⟨0, 1⟩).support = [⟨0, 0⟩, ⟨0, 1⟩] := by decide
-- The π/8 rotations are exactly the T-count: two of the three below.
example : RotProg.tCount [rotT ⟨0, 0⟩, rotS ⟨0, 0⟩, rotZZ ⟨0, 0⟩ ⟨0, 1⟩] = 2 := by decide
example : RotProg.wf [rotT ⟨0, 0⟩, rotS ⟨0, 0⟩, rotZZ ⟨0, 0⟩ ⟨0, 1⟩] = true := by decide

end PPR
