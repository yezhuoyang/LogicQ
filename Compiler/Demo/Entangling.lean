/-
  Compiler.Demo.Entangling — the typechecked CNOT lowering (§7): a real PPM-gadget
  compiler path, NOT a claim of channel correctness.
-/
import Compiler.Demo.Common

namespace Compiler.Demo
open Compiler Compiler.Sim TypeChecker ChainQ

/-! ## §7. TYPECHECKED CNOT LOWERING — NOT semantic CNOT correctness (M18 task 5).

    A cross-block `CNOT` lowers to the `progCNOTAt` PPM gadget, whose two joint
    measurements (`Z⊗Z`, `X⊗X`) require ADAPTER capabilities.  Given them, the
    program `H q0 ; CNOT q0 q1` genuinely LOWERS and TYPE-CHECKS through `compile?`.

    THIS IS NOT A CLAIM OF CHANNEL CORRECTNESS.  The gadget channel is the deferred
    ideal-gadget ASSUMPTION; `execMixed` does NOT run it (it is `none`/stuck on the
    gadget — see below), and `CNOT` is OUTSIDE the exact-operational fragment
    (`exactSupportedOp (.cnotGate …) = false`).  What is real here is the COMPILER
    PATH: source-typed, lowered to nontrivial PPM measurements, and re-checked.

    The ancilla block (block 2) carries TWO logical qubits because the ancilla-address
    seed advances once per op, so the leading `hGate` shifts the gadget ancilla to
    `⟨2,1⟩` — which must be a valid index. -/

/-- A 2-logical-qubit bare block (the CNOT-gadget ancilla block). -/
def q2 : Block :=
  { n := 2, stab := [],
    lx := [[true, false, false, false], [false, true, false, false]],
    lz := [[false, false, true, false], [false, false, false, true]] }

/-- Env: data blocks 0,1 (bare qubits) + ancilla block 2 (two qubits). -/
def bellEnv : TypedEnv := ⟨[⟨q0, by decide⟩, ⟨q0, by decide⟩, ⟨q2, by decide⟩]⟩

/-- Adapter capability for the gadget's `Z⊗Z` on blocks (0,2). -/
def zzCap02 : Capability := { kind := .adapterPPM, blocks := [0, 2], ancN := 0, connStab := [[false, false, false, true, false, true]] }
/-- Adapter capability for the gadget's `X⊗X` on blocks (2,1). -/
def xxCap21 : Capability := { kind := .adapterPPM, blocks := [2, 1], ancN := 0, connStab := [[false, true, true, false, false, false]] }

/-- Count the `.meas` statements in a PPM fragment (for the nontrivial-gadget check). -/
def stmtMeasCount : PPM.Stmt → Nat
  | .meas _ _   => 1
  | .ite _ a b  => stmtMeasCount a + stmtMeasCount b
  | .seq a b    => stmtMeasCount a + stmtMeasCount b
  | _           => 0

def typecheckedCNOTCfg : CompileConfig := { caps := [zzCap02, xxCap21], anc := ⟨2, 0⟩ }
/-- `H q0 ; CNOT q0 q1` — used ONLY to exhibit a typechecked CNOT LOWERING. -/
def typecheckedCNOTLowering : List LogicalOp := [.hGate ⟨0, 0⟩, .cnotGate ⟨0, 0⟩ ⟨1, 0⟩]

example : sourceWellFormed typecheckedCNOTCfg.caps bellEnv PPMState.init typecheckedCNOTLowering = true := by decide
example : sourceCompilable .executable typecheckedCNOTCfg bellEnv typecheckedCNOTLowering = true := by decide
example : ok? (compile? .executable typecheckedCNOTCfg bellEnv typecheckedCNOTLowering) = true := by decide
-- the EMITTED Mixed IR type-checks (under the same caps):
example : (match compile? .executable typecheckedCNOTCfg bellEnv typecheckedCNOTLowering with
           | .ok c => ok? (checkLogicalExec typecheckedCNOTCfg.caps bellEnv c.prog) | _ => false) = true := by decide
-- the emitted CNOT lowering contains NONTRIVIAL PPM measurements (≥ 3 `.meas`): it is a
-- real gadget, not a no-op — but its CHANNEL is assumed ideal, not run:
example : (match compile? .executable typecheckedCNOTCfg bellEnv typecheckedCNOTLowering with
           | .ok c => 3 ≤ (c.prog.map (fun i => match i with | .ppm s => stmtMeasCount s | _ => 0)).sum
           | _ => false) = true := by decide
-- `execMixed` does NOT run the gadget (the channel is deferred): it gets STUCK (`none`),
-- so NO operational CNOT-correctness is claimed:
example : (match compile? .executable typecheckedCNOTCfg bellEnv typecheckedCNOTLowering with
           | .ok c => execMixed (Layout.flat 4) 4 c.prog (init 4) = none
           | _ => false) = true := by decide
-- WITHOUT the adapter capabilities the same program is well-formed but NOT compilable:
example : sourceWellFormed [] bellEnv PPMState.init typecheckedCNOTLowering = true := by decide
example : sourceCompilable .executable { caps := [], anc := ⟨2, 0⟩ } bellEnv typecheckedCNOTLowering = false := by decide

end Compiler.Demo
