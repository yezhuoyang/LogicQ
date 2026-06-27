/-
  QClifford.Semantics — the operational semantics of the target circuit.

  A QClifford circuit runs against a PHYSICAL state with a classical store of
  measured bits.  As with `PPM.Semantics`, the state is PARAMETRIC: a `Host St`
  supplies the Clifford gate actions and a `Z`-basis measurement
  (`measureZ : PQubit → St → Bool × St`).  Instantiate `St` with a stabilizer
  tableau (Mathlib-free) or a density matrix later; the control-flow law
  `run_append` below holds for any host.

  `run` threads `(state, store)`: gates transform the state, `meas` records its
  outcome bit, and `ifPauli` applies a feed-forward Pauli conditioned on a bit.
-/
import QClifford.Syntax

namespace QClifford
open Physical

/-- The classical store of measured bits. -/
abbrev Store := CBit → Bool
/-- The empty store. -/
def Store.empty : Store := fun _ => false
/-- Set bit `r` to `b`. -/
def Store.set (σ : Store) (r : CBit) (b : Bool) : Store :=
  fun x => if x = r then b else σ x

/-- A physical execution host: the Clifford gate actions and a `Z`-measurement. -/
structure Host (St : Type) where
  applyH    : PQubit → St → St
  applyS    : PQubit → St → St
  applyX    : PQubit → St → St
  applyZ    : PQubit → St → St
  applyCNOT : PQubit → PQubit → St → St
  applyCZ   : PQubit → PQubit → St → St
  measureZ  : PQubit → St → Bool × St

/-- Apply a Pauli (feed-forward correction) via the host (`Y = Z·X` mod phase). -/
def applyPauli {St : Type} (Ho : Host St) : Pauli → PQubit → St → St
  | .I, _, st => st
  | .X, q, st => Ho.applyX q st
  | .Z, q, st => Ho.applyZ q st
  | .Y, q, st => Ho.applyZ q (Ho.applyX q st)

/-- Run a circuit, threading the physical state and the classical store. -/
def run {St : Type} (Ho : Host St) : Circuit → St → Store → St × Store
  | [],                  st, σ => (st, σ)
  | .H q :: t,           st, σ => run Ho t (Ho.applyH q st) σ
  | .S q :: t,           st, σ => run Ho t (Ho.applyS q st) σ
  | .X q :: t,           st, σ => run Ho t (Ho.applyX q st) σ
  | .Z q :: t,           st, σ => run Ho t (Ho.applyZ q st) σ
  | .CNOT c d :: t,      st, σ => run Ho t (Ho.applyCNOT c d st) σ
  | .CZ a b :: t,        st, σ => run Ho t (Ho.applyCZ a b st) σ
  | .meas q r :: t,      st, σ =>
      run Ho t (Ho.measureZ q st).2 (σ.set r (Ho.measureZ q st).1)
  | .ifPauli r p q :: t, st, σ =>
      run Ho t (if σ r then applyPauli Ho p q st else st) σ

/-- **Sequential composition.**  Running `c₁ ++ c₂` is running `c₂` from the
    state/store produced by `c₁` — the composition law the end-to-end
    correctness proof threads through the target. -/
theorem run_append {St : Type} (Ho : Host St) (c₁ c₂ : Circuit) (st : St) (σ : Store) :
    run Ho (c₁ ++ c₂) st σ
      = run Ho c₂ (run Ho c₁ st σ).1 (run Ho c₁ st σ).2 := by
  induction c₁ generalizing st σ with
  | nil => rfl
  | cons g t ih => cases g <;> simp [run, ih]

end QClifford
