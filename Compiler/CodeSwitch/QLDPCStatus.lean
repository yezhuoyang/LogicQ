/-
  Compiler.CodeSwitch.QLDPCStatus — the FORMAL qLDPC-protocol status layer (Concern 3).

  This module answers, AS CHECKED CODE (not prose), the question:
    "Which qLDPC paper methods are supported in MixIR syntax + semantics, and which are
     external checked artifacts?"

  Each method is assigned a `MixIRStatus`:
    * `lowersToMixIR` — it has a ChainQ source op AND elaborates to a checked `MixPrim` via the
      existing `checkPrim?` (so it carries a `CheckedPrimitive` / MixIR `WellTyped` claim).
    * `externalOnly` — it has a proof-carrying checker that recomputes its GF(2) algebra, but it
      is DELIBERATELY NOT a `CheckedPrimitive`, has NO `MixPrim` constructor, and there is NO
      `compileChainQToMixIR?` elaboration path for it.

  The `externalOnly` verdict is honest, not a downgrade: adding `MixPrim` arms for these methods
  would re-introduce the operational-channel / induced-action obligations the DR5 soundness fix
  removed.  The registry below is the SINGLE SOURCE OF TRUTH for the headline claim, and the
  `not_all_lower_to_mixIR` theorem is the formal "NO" answer.
-/
import Compiler.CodeSwitch.ProductSurgery

namespace Compiler.CodeSwitch
open TypeChecker

/-! ## §S.1. The status vocabulary. -/

/-- The qLDPC paper methods the compiler knows about. -/
inductive QLDPCMethod
  | highWeightPPM | productSurgery | qgpu | gppm | dimensionJump | batchedCodeSwitch | homomorphicCNOT
  deriving DecidableEq, Repr

/-- A method's relationship to MixIR. -/
inductive MixIRStatus
  /-- ChainQ source op + checked `MixPrim` via `checkPrim?` (carries a `CheckedPrimitive`). -/
  | lowersToMixIR
  /-- Proof-carrying checker, but NO `CheckedPrimitive` / NO `MixPrim` / NO elaboration path. -/
  | externalOnly
  deriving DecidableEq, Repr

/-- One row of the status registry: the method, its MixIR status, the proof-carrying RESULT
    type its checker returns, and a one-line note (for `externalOnly`, the named obligation /
    why it produces no `CheckedPrimitive`). -/
structure QLDPCMethodSpec where
  method       : QLDPCMethod
  status       : MixIRStatus
  artifactType : String
  note         : String
  deriving Repr

/-! ## §S.2. The registry — the single source of truth for the headline claim. -/

/-- Each method's status, recorded HONESTLY.  Only high-weight capability PPM lowers to MixIR
    (a `measure` source op → `MixPrim.ppm`, admitted via a `CapabilityWitness` whose merged-code
    certificate `checkPPM` recomputes); every other method is an external checked artifact. -/
def qldpcRegistry : List QLDPCMethodSpec :=
  [ { method := .highWeightPPM, status := .lowersToMixIR,
      artifactType := "MixPrim.ppm / CheckedPrimitive",
      note := "measure source op; high-weight admitted via CapabilityWitness + checkPPM merged cert" },
    { method := .productSurgery, status := .externalOnly,
      artifactType := "CheckedProductSurgery",
      note := "no MixPrim; provenance enters PPM only via CapabilityWitness.productSurgery; block-identity binding (CheckedProductSurgeryFor) NOT built" },
    { method := .qgpu, status := .externalOnly,
      artifactType := "CheckedQGPURoundIn",
      note := "no MixPrim; ChainQ-name-bound via checkQGPURoundIn?; physical FT of the d-round schedule deferred" },
    { method := .gppm, status := .externalOnly,
      artifactType := "GPPMArtifact",
      note := "explicitly NOT a CheckedPrimitive; operational measurement-outcome rule + ancilla state prep deferred" },
    { method := .dimensionJump, status := .externalOnly,
      artifactType := "DimensionJumpChecked",
      note := "no MixPrim; one-bit teleport init/measure/feedback + homology-quotient injectivity deferred" },
    { method := .batchedCodeSwitch, status := .externalOnly,
      artifactType := "BatchedCodeSwitchFor",
      note := "no MixPrim; envOut/locOut wiring into compile? deferred" },
    { method := .homomorphicCNOT, status := .externalOnly,
      artifactType := "BridgedHomCNOT / ExternalClaim",
      note := "induced action verified (homCNOTBridge_sound) but produces TypedTransversalCNOTBatch, not MixIR" } ]

/-! ## §S.3. The checked facts. -/

/-- The registry covers every method exactly once (no method silently omitted). -/
theorem qldpcRegistry_complete :
    qldpcRegistry.map (·.method)
      = [.highWeightPPM, .productSurgery, .qgpu, .gppm, .dimensionJump, .batchedCodeSwitch, .homomorphicCNOT] := by
  decide

/-- **The honest headline, as a CHECKED fact.**  NOT all qLDPC methods lower to MixIR — so we
    CANNOT claim "all qLDPC primitives are supported in MixIR syntax and semantics". -/
theorem not_all_lower_to_mixIR :
    qldpcRegistry.all (fun s => s.status == .lowersToMixIR) = false := by decide

/-- Exactly ONE method lowers to MixIR: high-weight capability PPM. -/
theorem only_ppm_lowers :
    (qldpcRegistry.filter (fun s => s.status == .lowersToMixIR)).map (·.method) = [.highWeightPPM] := by decide

/-- The six external-only methods are all recorded `externalOnly` (none counted as MixIR support). -/
theorem externalOnly_methods :
    (qldpcRegistry.filter (fun s => s.status == .externalOnly)).map (·.method)
      = [.productSurgery, .qgpu, .gppm, .dimensionJump, .batchedCodeSwitch, .homomorphicCNOT] := by decide

/-- **`lowersToMixIR` anchor (NOT a bare flag).**  The one `lowersToMixIR` method is real: a
    high-weight (3-body) PPM is genuinely ADMITTED as MixIR legality through a `CapabilityWitness`
    — `checkPPMWitnessed` recomputes the merged-code certificate (`checkPPM`) and accepts.  (The
    full ChainQ→MixIR path `measure` source op → `MixPrim.ppm` is exercised in
    `Compiler/ChainQ2Mixed/Compile.lean` §C.12c.) -/
theorem highWeightPPM_lowers_anchor :
    ok? (checkPPMWitnessed bare3Env [.generic psMergeCap (by decide)] hw3) = true := by decide

end Compiler.CodeSwitch
