/-
  TypeChecker.Judgment.Switch.Examples — worked examples for `checkSwitch`:
  encode an unprotected qubit into the [[3,1,1]] repetition code.
-/
import TypeChecker.Judgment.Switch.Check

namespace TypeChecker
open ChainQ ChainQ.GF2

/-! ## Worked example: encode an unprotected qubit into the [[3,1,1]] repetition code.

    A transparent switch C → D where C is one bare qubit (`X̄ = X`, `Z̄ = Z`) and
    D is the bit-flip repetition code (`Z₀Z₁`, `Z₁Z₂` stabilizers; `X̄ = XXX`,
    `Z̄ = Z₀`).  The map `f` sends `X̄ ↦ XXX`, `Z̄ ↦ Z₀`. -/

/-- One bare logical qubit. -/
def unenc1 : Block := { n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] }

/-- The `[[3,1,1]]` bit-flip repetition code (symplectic form, width 6). -/
def repCode3 : Block :=
  { n := 3,
    stab := [[false, false, false, true,  true,  false],    -- Z₀Z₁
             [false, false, false, false, true,  true ]],    -- Z₁Z₂
    lx := [[true,  true,  true,  false, false, false]],       -- X̄ = XXX
    lz := [[false, false, false, true,  false, false]] }      -- Z̄ = Z₀

/-- The encoding map `X̄ ↦ XXX`, `Z̄ ↦ Z₀` (2 rows × 6). -/
def encF : BoolMat := [[true, true, true, false, false, false],
                       [false, false, false, true, false, false]]

def tsrc  : TypedEnv   := ⟨[⟨unenc1, by decide⟩]⟩
def tdst  : TypedBlock := ⟨repCode3, by decide⟩

-- The encode-into-repetition switch is legal:
example : ok? (checkSwitch tsrc 0 tdst { kind := .gaugeFix, f := encF }) = true := by decide
-- …and it preserves the logical operators (induced X̄ = XXX, Z̄ = Z₀):
example : (res? (checkSwitch tsrc 0 tdst { kind := .gaugeFix, f := encF })).map (·.2.inducedLX)
            = some [[true, true, true, false, false, false]] := by decide

-- REJECTIONS:
-- a degenerate map (everything ↦ 0) does not preserve the logical operators;
example : ok? (checkSwitch tsrc 0 tdst { kind := .gaugeFix, f := zeroMat 2 6 }) = false := by decide
-- a borrowed block cannot be switched (switching consumes);
example : ok? (checkSwitch ⟨[⟨{ unenc1 with own := .borrowed }, by decide⟩]⟩ 0 tdst { kind := .gaugeFix, f := encF }) = false := by decide
-- an unknown block id is rejected.
example : ok? (checkSwitch tsrc 3 tdst { kind := .gaugeFix, f := encF }) = false := by decide
-- CERTIFICATE SHAPE: f must be exactly 2·n_C × 2·n_D (here 2×6); a 1×1 f is rejected.
example : ok? (checkSwitch tsrc 0 tdst { kind := .gaugeFix, f := [[true]] }) = false := by decide

/-! ### Raw entry point + typed-target safety.

    A malformed TARGET code is now UNREPRESENTABLE as a `TypedBlock`; the raw
    wrapper `checkSwitchFromEnv` rejects it as `malformedTarget` (NOT a source id),
    and a malformed SOURCE as `malformedBlock`. -/

-- a target with mismatched Z̄ arity (k_D = 0) is rejected as a malformed TARGET:
example : (match checkSwitchFromEnv { blocks := [unenc1] } 0 { repCode3 with lz := [] } { kind := .gaugeFix, f := encF } with
           | .error .malformedTarget => true | _ => false) = true := by decide
-- a target Z̄ of the wrong width (1×2) is likewise a malformed TARGET (no zip/vecXor truncation):
example : (match checkSwitchFromEnv { blocks := [unenc1] } 0 { repCode3 with lz := [[true, false]] } { kind := .gaugeFix, f := encF } with
           | .error .malformedTarget => true | _ => false) = true := by decide
-- a malformed SOURCE block (zero-width logical) is rejected as `malformedBlock 0` (the source id):
example : (match checkSwitchFromEnv { blocks := [{ unenc1 with lx := [[]] }] } 0 repCode3 { kind := .gaugeFix, f := encF } with
           | .error (.malformedBlock i) => i == 0 | _ => false) = true := by decide
-- the raw wrapper accepts the good case too:
example : ok? (checkSwitchFromEnv { blocks := [unenc1] } 0 repCode3 { kind := .gaugeFix, f := encF }) = true := by decide

-- TYPED CERT: `encF` is a well-formed 2·1 × 2·3 certificate; a 1×1 map is rejected.
example : ok? (mkSwitchCert? { kind := .gaugeFix, f := encF } 1 3) = true := by decide
example : ok? (mkSwitchCert? { kind := .gaugeFix, f := [[true]] } 1 3) = false := by decide

end TypeChecker
