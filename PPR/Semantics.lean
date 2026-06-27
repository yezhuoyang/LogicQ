/-
  PPR.Semantics — the denotational semantics of the Pauli-Product-Rotation IR.

  A rotation `exp(i φ P)` is a UNITARY operator.  Using `P² = I`, it has the
  closed form

        rotOf φ P  =  cos φ · 1  +  (i · sin φ) · P                    (Euler form)

  so the semantics is fixed once we give the operator `P` of a logical Pauli
  string.  We denote `P` as a MONOMIAL complex matrix indexed by computational
  basis bitstrings `x : Fin n → Bool` (no tensor/Kronecker machinery): a Pauli
  string sends `|x⟩ ↦ coeff·|act x⟩`, where `X`/`Y` flip a bit and `Z`/`Y`
  contribute a sign/phase.  A PPR program denotes the product of its rotations.

  This is the first module that uses Mathlib (`ℂ`, `Matrix`, `Real.cos/sin`);
  it is pinned to the same Mathlib as FormalRV.  The logical→physical qubit
  layout is a parameter `lay : LQubit → Fin n`.
-/
import PPR.Syntax
import Mathlib

open Logical

namespace PPR

/-- The computational basis on `n` qubits is indexed by `n`-bit strings. -/
abbrev BitStr (n : Nat) := Fin n → Bool

/-- A DENSE Pauli over `n` qubits: a single-qubit Pauli or `I` (`none`) per
    position. -/
abbrev DensePauli (n : Nat) := Fin n → Option Pauli

/-- Lower a sparse logical Pauli string to a dense Pauli over `Fin n`, via a
    qubit layout `lay`.  Logical qubits not listed are `I`. -/
def denseOf (n : Nat) (lay : LQubit → Fin n) (P : PauliString) : DensePauli n :=
  fun i => (P.find? (fun f => decide (lay f.1 = i))).map Prod.snd

/-- The basis bitstring that a dense Pauli maps `x` to: `X` and `Y` flip the
    bit, `I` and `Z` leave it. -/
def act {n : Nat} (d : DensePauli n) (x : BitStr n) : BitStr n :=
  fun i => match d i with
    | some .X => !(x i)
    | some .Y => !(x i)
    | _       => x i

/-- The (single) nonzero matrix entry `⟨act d x | P | x⟩`: `Z`/`Y` contribute a
    sign on set bits, `Y` an extra factor of `i`. -/
def coeff {n : Nat} (d : DensePauli n) (x : BitStr n) : ℂ :=
  Finset.univ.prod (fun i : Fin n =>
    (match d i with
     | some .Z => (if x i then -1 else 1)
     | some .Y => (if x i then -Complex.I else Complex.I)
     | _       => 1 : ℂ))

/-- The monomial matrix of a dense Pauli string. -/
def axisMat {n : Nat} (d : DensePauli n) : Matrix (BitStr n) (BitStr n) ℂ :=
  fun y x => if y = act d x then coeff d x else 0

/-- `rotOf φ M = cos φ · 1 + (i · sin φ) · M` — the rotation `exp(i φ P)` for an
    involutive `M = axisMat P`. -/
noncomputable def rotOf {n : Nat} (φ : ℝ) (M : Matrix (BitStr n) (BitStr n) ℂ) :
    Matrix (BitStr n) (BitStr n) ℂ :=
  (↑(Real.cos φ) : ℂ) • (1 : Matrix (BitStr n) (BitStr n) ℂ)
    + (Complex.I * ↑(Real.sin φ)) • M

/-- The real angle of a phase `φ = ± π / 2ᵏ`. -/
noncomputable def Phase.toReal (p : Phase) : ℝ :=
  (if p.neg then -1 else 1) *
    (match p.angle with
     | .pi        => Real.pi
     | .piHalf    => Real.pi / 2
     | .piQuarter => Real.pi / 4
     | .piEighth  => Real.pi / 8)

/-- The unitary denoted by a single rotation on `n` qubits laid out by `lay`. -/
noncomputable def Rot.denote (n : Nat) (lay : LQubit → Fin n) (r : Rot) :
    Matrix (BitStr n) (BitStr n) ℂ :=
  rotOf r.phase.toReal (axisMat (denseOf n lay r.pauli))

/-- The unitary denoted by a PPR program: rotations applied in order (the first
    rotation is rightmost in the operator product). -/
noncomputable def RotProg.denote (n : Nat) (lay : LQubit → Fin n) (p : RotProg) :
    Matrix (BitStr n) (BitStr n) ℂ :=
  p.foldl (fun acc r => Rot.denote n lay r * acc) 1

/-! ## Basic laws. -/

/-- A zero-angle rotation is the identity. -/
@[simp] theorem rotOf_zero {n : Nat} (M : Matrix (BitStr n) (BitStr n) ℂ) :
    rotOf 0 M = 1 := by
  simp [rotOf, Real.cos_zero, Real.sin_zero]

/-- The empty program denotes the identity. -/
@[simp] theorem denote_nil (n : Nat) (lay : LQubit → Fin n) :
    RotProg.denote n lay [] = 1 := rfl

/-- A one-rotation program denotes that rotation. -/
theorem denote_singleton (n : Nat) (lay : LQubit → Fin n) (r : Rot) :
    RotProg.denote n lay [r] = Rot.denote n lay r := by
  simp [RotProg.denote]

/-- Factoring a left-multiplying fold through its initial value (monoid law). -/
theorem foldl_mul_one {M β : Type*} [Monoid M] (g : β → M) (l : List β) (init : M) :
    l.foldl (fun acc a => g a * acc) init
      = l.foldl (fun acc a => g a * acc) 1 * init := by
  induction l generalizing init with
  | nil => simp
  | cons a t ih =>
    simp only [List.foldl_cons]
    rw [ih (g a * init), ih (g a * 1), mul_one, mul_assoc]

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

end PPR
