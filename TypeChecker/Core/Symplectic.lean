/-
  TypeChecker.Core.Symplectic — the binary symplectic layer.

  PL-MINIMAL CORE: there is NO new Pauli or code type.  A Pauli on `n` qubits
  is a `GF2.BoolVec` of width `2n` (X-block ++ Z-block); a code is its symplectic
  stabilizer `GF2.BoolMat` (rows = generators, width `2n`).  The existing
  `ChainQ.CSSCode`/`StabilizerCode` ELABORATE into this representation, and all
  symplectic operations REUSE `ChainQ.GF2` (`dotBit`/`transpose`/`matMul`/
  `orthogonal`/`inSpan`) plus a single half-swap.  Mathlib-free.

  Convention: a Clifford gate's logical action is a `2n×2n` symplectic `BoolMat`
  acting on Pauli row-vectors by `v ↦ v · M` (so named gates are just `def`s).
-/
import ChainQ.Basic
import Logical.Basic

namespace TypeChecker
open ChainQ ChainQ.GF2

/-! ## Plain matrices. -/

/-- The `m×m` identity over GF(2). -/
def idMat (m : Nat) : BoolMat :=
  (List.range m).map (fun i => (List.range m).map (fun j => decide (i = j)))

/-- The `r×c` zero matrix. -/
def zeroMat (r c : Nat) : BoolMat := (List.range r).map (fun _ => List.replicate c false)

/-! ## The symplectic form (reuses GF2 + one half-swap). -/

/-- Swap the X-block and Z-block of a width-`2n` Pauli vector. -/
def swapHalves (n : Nat) (v : BoolVec) : BoolVec := v.drop n ++ v.take n

/-- The symplectic inner product `a·d ⊕ b·c` of two Pauli vectors: `false`
    iff they COMMUTE.  `= dotBit u (swapHalves v)`. -/
def sympForm (n : Nat) (u v : BoolVec) : Bool := dotBit u (swapHalves n v)

/-- Every row of `A` symplectically commutes with every row of `B`
    (reuses `GF2.orthogonal`). -/
def sympOrthogonal (n : Nat) (A B : BoolMat) : Bool := orthogonal A (B.map (swapHalves n))

/-- The symplectic form matrix `J = [[0,I],[I,0]]` (`2n×2n`): row `i` has a `1`
    at column `(i+n) mod 2n`. -/
def J (n : Nat) : BoolMat :=
  (List.range (2 * n)).map (fun i =>
    (List.range (2 * n)).map (fun j => decide (j = (i + n) % (2 * n))))

/-- Apply a symplectic map `M` (`2n×2n`) to a set of Pauli rows, `v ↦ v · M`
    (reuses `GF2.matMul`). -/
def applyMap (n : Nat) (M rows : BoolMat) : BoolMat := matMul rows M (2 * n)

/-- Whether `M` preserves the symplectic form: `M · J · Mᵀ = J` (the condition
    that `M` is a genuine Clifford/symplectic transformation). -/
def preservesSymp (n : Nat) (M : BoolMat) : Bool :=
  decide (matMul (matMul M (J n) (2 * n)) (transpose M (2 * n)) (2 * n) = J n)

/-! ## Elaboration: existing code types ⇒ symplectic stabilizer matrix. -/

/-- A single-qubit Pauli's `(x, z)` symplectic bits. -/
def pauliXZ : Pauli → Bool × Bool
  | .I => (false, false)
  | .X => (true,  false)
  | .Z => (false, true)
  | .Y => (true,  true)

/-- A dense `PauliString` (length `n`) as a width-`2n` symplectic vector. -/
def stringToSym (p : PauliString) : BoolVec :=
  (p.map (fun c => (pauliXZ c).1)) ++ (p.map (fun c => (pauliXZ c).2))

/-- A `CSSCode` as a symplectic stabilizer matrix: X-checks become `(hx | 0)`,
    Z-checks become `(0 | hz)`.  M20: the CSS→stabilizer materialization is now owned
    by the FRONT-END (`ChainQ.CSSCode.symplecticStabilizers`); this is a thin alias
    that preserves the `cssToStab` name (byte-identical result). -/
def cssToStab (c : CSSCode) : BoolMat := c.symplecticStabilizers

/-- A `StabilizerCode` (Pauli generators) as a symplectic stabilizer matrix. -/
def stabCodeToStab (c : StabilizerCode) : BoolMat := c.gens.map stringToSym

/-! ## Smoke checks. -/

example : sympForm 1 [true, false] [false, true] = true  := by decide   -- X̄, Z̄ anticommute
example : sympForm 1 [true, false] [true, false] = false := by decide   -- X, X commute
example : preservesSymp 1 (idMat 2) = true := by decide
example : preservesSymp 1 (J 1) = true := by decide                     -- transversal H is symplectic
-- the square CSS code's symplectic stabilizers all commute (= its css_condition)
example : sympOrthogonal 4 (cssToStab square.toCSS) (cssToStab square.toCSS) = true := by decide

end TypeChecker
