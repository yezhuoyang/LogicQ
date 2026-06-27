/-
  TypeChecker.Judgment.Transversal.Examples — worked, decidable examples for
  `checkLogicalAutomorphism` and `checkTransversal` over a TYPED environment.
-/
import TypeChecker.Judgment.Transversal.Check

namespace TypeChecker
open ChainQ ChainQ.GF2

/-! ## Worked examples (all decidable) — over a TYPED environment.

    Fixtures must be `Block.valid` (complete) to enter a `TypedEnv`; the proofs
    are discharged `by decide`.  (The old incomplete fragments `tiny`/`sq` are no
    longer representable — they would be `SubBlock`s; the non-self-dual rejection
    is shown instead on the COMPLETE repetition code `rep3`.) -/

/-- A single logical qubit, no stabilizers: `X̄ = X`, `Z̄ = Z`. -/
def oneQ : Block := { n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] }

/-- The self-dual `[[2,0,2]]` code (Bell stabilizer `XX`, `ZZ`; `k = 0`). -/
def bell2 : Block :=
  { n := 2, stab := [[true, true, false, false], [false, false, true, true]] }

/-- The complete `[[3,1,1]]` repetition code (`Z₀Z₁`, `Z₁Z₂`; `X̄ = XXX`, `Z̄ = Z₀`). -/
def rep3 : Block :=
  { n := 3,
    stab := [[false, false, false, true,  true,  false],
             [false, false, false, false, true,  true ]],
    lx := [[true,  true,  true,  false, false, false]],
    lz := [[false, false, false, true,  false, false]] }

/-- The single-qubit Hadamard as a `2×2` symplectic (`X↔Z`). -/
def hGate : BoolMat := [[false, true], [true, false]]

def toneQ  : TypedEnv := ⟨[⟨oneQ,  by decide⟩]⟩
def tbell2 : TypedEnv := ⟨[⟨bell2, by decide⟩]⟩
def trep3  : TypedEnv := ⟨[⟨rep3,  by decide⟩]⟩

/-! ### `checkLogicalAutomorphism` (arbitrary symplectic action `M`). -/

-- The automorphism `J 1` (= Hadamard) on a single qubit is legal and induces X̄↦Z̄, Z̄↦X̄:
example : ok? (checkLogicalAutomorphism toneQ 0 (J 1)) = true := by decide
example : (res? (checkLogicalAutomorphism toneQ 0 (J 1))).map (·.inducedLX) = some [[false, true]] := by decide
example : (res? (checkLogicalAutomorphism toneQ 0 (J 1))).map (·.inducedLZ) = some [[true, false]] := by decide
-- identity is always legal; H is a legal automorphism on the self-dual Bell code:
example : ok? (checkLogicalAutomorphism tbell2 0 (idMat 4)) = true := by decide
example : ok? (checkLogicalAutomorphism tbell2 0 (J 2)) = true := by decide
-- REJECTIONS: H not preserved on the non-self-dual repetition code; non-symplectic; unknown block.
example : ok? (checkLogicalAutomorphism trep3 0 (J 3)) = false := by decide
example : ok? (checkLogicalAutomorphism tbell2 0 (zeroMat 4 4)) = false := by decide
example : ok? (checkLogicalAutomorphism tbell2 5 (J 2)) = false := by decide

/-! ### `checkTransversal` (genuine LOCAL single-qubit gate `g`; tensor power). -/

-- transversal H on one qubit builds `J 1` and induces X̄ ↦ Z̄:
example : Internal.transversalMap 1 hGate = J 1 := by decide
example : ok? (checkTransversal toneQ 0 hGate) = true := by decide
example : (res? (checkTransversal toneQ 0 hGate)).map (·.inducedLX) = some [[false, true]] := by decide
-- transversal H on two qubits builds `J 2`, legal on the self-dual Bell code:
example : Internal.transversalMap 2 hGate = J 2 := by decide
example : ok? (checkTransversal tbell2 0 hGate) = true := by decide
-- REJECTIONS: transversal H is NOT legal on the non-self-dual repetition code;
example : ok? (checkTransversal trep3 0 hGate) = false := by decide
-- a non-symplectic single-qubit gate is rejected;
example : ok? (checkTransversal toneQ 0 [[true, false], [false, false]]) = false := by decide
-- a wrong-size gate (not 2×2) is rejected; an unknown block id is rejected.
example : ok? (checkTransversal toneQ 0 (idMat 4)) = false := by decide
example : ok? (checkTransversal toneQ 5 hGate) = false := by decide

end TypeChecker
