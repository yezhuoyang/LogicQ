/-
  Compiler.Demo.Contract — the M22 contract examples: the THREE required end-to-end
  fragments at their EXPLICIT correctness boundaries, plus the `SupportedSourceProgram`
  and `opBoundary` contract facts.  Every claim is `by decide`; nothing is overclaimed.

      1. EXACT direct fragment        — run operationally, matches the ideal simulator.
      2. PPM-gadget fragment          — TYPECHECKED + lowered under the EXPLICIT
                                        ideal-gadget assumption (channel NOT run).
      3. Library-inspired code switch — typechecks with its PROVED symplectic
                                        certificate (`checkSwitch`).
-/
import Compiler.Demo.Common
import Compiler.Demo.Entangling
import TypeChecker.Basic

namespace Compiler.Demo
open Compiler Compiler.Sim TypeChecker ChainQ

/-! ## §1. EXACT direct fragment (boundary = `GadgetBoundary.exact`).

    `H ; S` on a single-logical block lowers to direct transversals; running the
    EMITTED program operationally (`execMixed`) yields the SAME state as the ideal
    source circuit. -/

def hsSrc : List LogicalOp := [.hGate ⟨0, 0⟩, .sGate ⟨0, 0⟩]

example : (match compile? .executable demoCfg tenvQ hsSrc with
           | .ok c => decide (execMixed (Layout.flat 4) 1 c.prog (init 1)
                              = some (runGates 1 (sourceGates (Layout.flat 4) hsSrc) (init 1)))
           | .error _ => false) = true := by decide
example : hsSrc.all (fun op => opBoundary op == GadgetBoundary.exact) = true := by decide

/-! ## §2. PPM-gadget fragment under the EXPLICIT ideal-gadget assumption
    (boundary = `GadgetBoundary.idealChannel`).

    The Bell-prep CNOT genuinely LOWERS and TYPE-CHECKS through `compile?` given an
    adapter capability — but its gadget CHANNEL is NOT run (`execMixed` is `none`/stuck
    on the multi-statement PPM gadget); the carrier channel is ASSUMED ideal, not
    proven.  (`opBoundary (.cnotGate …) = .idealChannel`.) -/

example : ok? (compile? .executable typecheckedCNOTCfg bellEnv typecheckedCNOTLowering) = true := by decide
example : (match compile? .executable typecheckedCNOTCfg bellEnv typecheckedCNOTLowering with
           | .ok c => ok? (checkLogicalExec typecheckedCNOTCfg.caps bellEnv c.prog) | _ => false) = true := by decide
-- the gadget channel is NOT executed — execMixed gets STUCK (ideal-channel boundary):
example : (match compile? .executable typecheckedCNOTCfg bellEnv typecheckedCNOTLowering with
           | .ok c => execMixed (Layout.flat 4) 4 c.prog (init 4) = none | _ => false) = true := by decide
example : opBoundary (.cnotGate ⟨0, 0⟩ ⟨1, 0⟩) = GadgetBoundary.idealChannel := by decide

/-! ## §3. Library-inspired CODE SWITCH that typechecks with its PROVED certificate.

    `MixedInstr.switch 0 repCode3 {kind := .gaugeFix, f := encF}` encodes a bare logical
    qubit (`tsrc`) into the `[[3,1,1]]` repetition CSS code (`repCode3`) via the
    symplectic map `encF` (X̄ ↦ XXX, Z̄ ↦ Z₀).  The mixed checker runs the SYMPLECTIC
    `checkSwitch`, which DECIDES over GF(2): cert shape, logical arity, stabilizer
    preservation, AND logical-operator preservation mod stabilizers — this is a PROVED
    structural certificate (NOT merely a shape check, and NOT a fault-tolerance claim:
    distance/decoder remain deferred obligations). -/

def switchRepInstr : MixedInstr := .switch 0 repCode3 { kind := .gaugeFix, f := encF }

example : ok? (checkLogicalExec [] tsrc [switchRepInstr]) = true := by decide
example : ok? (checkLogicalExecAux [] tsrc PPMState.init [switchRepInstr]) = true := by decide
-- a BAD-shape certificate (1×1 instead of the required 2·n_C × 2·n_D) is REJECTED:
example : ok? (checkLogicalExec [] tsrc
    [.switch 0 repCode3 { kind := .gaugeFix, f := [[true]] }]) = false := by decide

/-! ## §4. The `SupportedSourceProgram` contract (Task 2). -/

-- A supported program: compiles end-to-end (operands well-formed, every op lowers,
-- caps present, magic policy holds; resources IDEAL-ASSUMED).
example : SupportedSourceProgram .executable demoCfg tenvQ hsSrc := by decide
-- NOT supported: a CNOT to a non-existent block is not even well-formed.
example : ¬ SupportedSourceProgram .executable demoCfg tenvQ [.cnotGate ⟨0, 0⟩ ⟨1, 0⟩] := by decide

/-! ## §5. The per-op correctness BOUNDARY (`opBoundary`, Task 3·4) as Lean-checked facts. -/

example : opBoundary (.hGate ⟨0, 0⟩) = GadgetBoundary.exact := by decide
example : opBoundary (.xGate ⟨0, 0⟩) = GadgetBoundary.exact := by decide
example : opBoundary (.zGate ⟨0, 0⟩) = GadgetBoundary.exact := by decide
example : opBoundary (.blockTransversal 0 hGate2x2) = GadgetBoundary.exact := by decide
example : opBoundary (.czGate ⟨0, 0⟩ ⟨1, 0⟩) = GadgetBoundary.idealChannel := by decide   -- experimental placeholder gadget
example : opBoundary (.measure 0 [(⟨0, 0⟩, PPM.PLetter.Z)]) = GadgetBoundary.idealChannel := by decide
example : opBoundary (.tGate ⟨0, 0⟩) = GadgetBoundary.typecheckedOnly := by decide

end Compiler.Demo
