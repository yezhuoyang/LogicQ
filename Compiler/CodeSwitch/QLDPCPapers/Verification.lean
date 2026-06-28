/-
  Compiler.CodeSwitch.QLDPCPapers.Verification

  Executable certificates for the ChainQ surface programs in
  `QLDPCPapers.ChainQProgram`.

  Checked here:
  * compiled parameters `n,k`;
  * expected stabilizer matrix sizes and CSS commutation;
  * operation-bearing rows elaborate to typed blocks and support the batched
    transversal logical CNOT source primitive.

  Not checked here: distance claims and stochastic fault-tolerance/decoder
  thresholds.  Those remain explicit obligations outside the current computable
  ChainQ/TypeChecker kernel.
-/
import Compiler.CodeSwitch.QLDPCPapers.Concrete

namespace Compiler.CodeSwitch.QLDPCPaperVerification

open ChainQ ChainQ.GF2 TypeChecker
open Compiler.CodeSwitch.QLDPCPaperConcrete

/-! ## Parameter and stabilizer certificates. -/

def hasCodeParams (checkedCode : Except ChainQError CheckedCSSCode)
    (nVal kVal : Nat) : Bool :=
  match checkedCode with
  | .ok cc => cc.code.n == nVal && cc.code.k == kVal
  | .error _ => false

def hasCSSStabilizerSet (checkedCode : Except ChainQError CheckedCSSCode)
    (nVal xCount zCount : Nat) : Bool :=
  match checkedCode with
  | .ok cc =>
      cc.code.n == nVal &&
      cc.code.hx.length == xCount &&
      cc.code.hz.length == zCount &&
      cc.code.hx.all (fun row => decide (row.length = nVal)) &&
      cc.code.hz.all (fun row => decide (row.length = nVal)) &&
      cc.code.cssCondition &&
      cc.code.valid
  | .error _ => false

def allListedCodeParamsOk : Bool :=
  hasCodeParams adapterBB1 98 6 &&
  hasCodeParams adapterLP2 200 20 &&
  hasCodeParams dimJumpBB18 18 2 &&
  hasCodeParams dimJumpBB30 30 2 &&
  hasCodeParams dimJumpBB54 54 2 &&
  hasCodeParams liftedToric16 16 2 &&
  hasCodeParams liftedToric36 36 2

def allListedStabilizersCommuteOk : Bool :=
  -- BB codes have `l*m` X-checks and `l*m` Z-checks.
  hasCSSStabilizerSet adapterBB1 98 49 49 &&
  hasCSSStabilizerSet dimJumpBB18 18 9 9 &&
  hasCSSStabilizerSet dimJumpBB30 30 15 15 &&
  hasCSSStabilizerSet dimJumpBB54 54 27 27 &&
  -- Lifted products have `rA*nA*ell` X-checks and Z-checks.
  hasCSSStabilizerSet adapterLP2 200 96 96 &&
  hasCSSStabilizerSet liftedToric16 16 8 8 &&
  hasCSSStabilizerSet liftedToric36 36 18 18

example : allListedCodeParamsOk = true := by native_decide
example : allListedStabilizersCommuteOk = true := by native_decide

/-! ## Batched transversal logical CNOT support. -/

def lowersToBatchedCNOT (Gamma : TypedEnv) (nVal kVal : Nat) : Bool :=
  match Compiler.compile? Compiler.CompileMode.executable
      { caps := [], anc := { blk := 0, idx := 0 } }
      Gamma (batchSelfCNOTSource nVal kVal) with
  | .ok c =>
      match c.prog with
      | [.transversalCNOTBatch spec] =>
          spec.controlBlock == 0 &&
          spec.targetBlock == 1 &&
          spec.incidence == identityIncidence nVal &&
          spec.logicalIncidence == ChainQ.GF2.identMat kVal &&
          ok? (Compiler.checkLogicalExec [] Gamma c.prog)
      | _ => false
  | .error _ => false

def supportsBatchedIdentityCNOT
    (checkedCode : Except ChainQError CheckedCSSCode) (nVal kVal : Nat) : Bool :=
  match twoCopyEnv? checkedCode with
  | .ok Gamma =>
      ok? (checkTransversalCNOTBatch Gamma
        { controlBlock := 0,
          targetBlock := 1,
          incidence := identityIncidence nVal,
          logicalIncidence := ChainQ.GF2.identMat kVal }) &&
      lowersToBatchedCNOT Gamma nVal kVal &&
      ! singletonSelfCNOTOk checkedCode nVal
  | .error _ => false

def operationRowsSupportBatchedCNOTOk : Bool :=
  supportsBatchedIdentityCNOT dimJumpBB18 18 2 &&
  supportsBatchedIdentityCNOT dimJumpBB30 30 2 &&
  supportsBatchedIdentityCNOT dimJumpBB54 54 2 &&
  supportsBatchedIdentityCNOT liftedToric16 16 2 &&
  supportsBatchedIdentityCNOT liftedToric36 36 2

example : operationRowsSupportBatchedCNOTOk = true := by native_decide

/-! ## Distance theorem profiles.

    Distance is not searched for in Lean.  These checks only attach cited
    paper-table theorem profiles.  Code-row parameter correctness is checked
    separately above by `allListedCodeParamsOk`.
-/

def hasPaperTableDistanceProfile (nVal kVal dVal : Nat) : Bool :=
  match knownPaperTableProfileByParams? nVal kVal dVal with
  | some bounds => bounds.meetsLower dVal
  | none => false

def allPaperDistanceProfilesOk : Bool :=
  hasPaperTableDistanceProfile 98 6 12 &&
  hasPaperTableDistanceProfile 200 20 10 &&
  hasPaperTableDistanceProfile 18 2 3 &&
  hasPaperTableDistanceProfile 30 2 5 &&
  hasPaperTableDistanceProfile 54 2 6 &&
  hasPaperTableDistanceProfile 16 2 4 &&
  hasPaperTableDistanceProfile 36 2 6

example : allPaperDistanceProfilesOk = true := by decide

end Compiler.CodeSwitch.QLDPCPaperVerification
