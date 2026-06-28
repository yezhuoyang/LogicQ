/-
  Compiler.CodeSwitch.QLDPCPapers.Concrete

  Concrete LP/BB instances from the qLDPC-operation papers, wired into the
  executable ChainQ/TypeChecker certificate checks.

  Sources encoded here:
  * arXiv:2410.03628, Universal adapters: BB1 [[98,6,12]] and LP2 [[200,20,10]].
  * arXiv:2510.07269, Transversal dimension jump: BB/BT and lifted-toric LP rows.

  We keep the large [[98]]/[[200]] examples as constructor/parameter/CSS
  regressions. Full logical-basis transversal checks on those instances are too
  expensive for ordinary `decide` gates, so the primitive semantic tests use the
  smaller paper rows from the same tables.
-/
import Compiler.CodeSwitch.QLDPCPapers
import Compiler.CodeSwitch.QLDPCPapers.ChainQProgram
import Compiler.Mixed.Lower.Public
import TypeChecker.Judgment.Transversal.CNOT
import ChainQ.Syntax

namespace Compiler.CodeSwitch.QLDPCPaperConcrete

open ChainQ ChainQ.GF2 TypeChecker

/-! ## Paper code instances. -/

abbrev adapterBB1Decl : NamedCodeDecl :=
  QLDPCPaperProgram.adapterBB1Decl
def adapterBB1 : Except ChainQError CheckedCSSCode :=
  adapterBB1Decl.check?

abbrev adapterLP2Decl : NamedCodeDecl :=
  QLDPCPaperProgram.adapterLP2Decl
def adapterLP2 : Except ChainQError CheckedCSSCode :=
  adapterLP2Decl.check?

-- Transversal dimension jump, arXiv:2510.07269, BB/BT component rows.
abbrev dimJumpBB18Decl : NamedCodeDecl :=
  QLDPCPaperProgram.dimJumpBB18Decl
def dimJumpBB18 : Except ChainQError CheckedCSSCode :=
  dimJumpBB18Decl.check?

abbrev dimJumpBB30Decl : NamedCodeDecl :=
  QLDPCPaperProgram.dimJumpBB30Decl
def dimJumpBB30 : Except ChainQError CheckedCSSCode :=
  dimJumpBB30Decl.check?

abbrev dimJumpBB54Decl : NamedCodeDecl :=
  QLDPCPaperProgram.dimJumpBB54Decl
def dimJumpBB54 : Except ChainQError CheckedCSSCode :=
  dimJumpBB54Decl.check?

-- Transversal dimension jump, arXiv:2510.07269, lifted-toric LP rows.
abbrev liftedToric16Decl : NamedCodeDecl :=
  QLDPCPaperProgram.liftedToric16Decl
def liftedToric16 : Except ChainQError CheckedCSSCode :=
  liftedToric16Decl.check?

abbrev liftedToric36Decl : NamedCodeDecl :=
  QLDPCPaperProgram.liftedToric36Decl
def liftedToric36 : Except ChainQError CheckedCSSCode :=
  liftedToric36Decl.check?

/-! ## Shared typed-environment helpers. -/

def typedBlockOf? (checkedCode : Except ChainQError CheckedCSSCode) : Except TypeError TypedBlock :=
  match checkedCode with
  | .ok cc => cssToTypedBlock? cc
  | .error _ => .error (.malformedBlock 0)

def twoCopyEnv? (checkedCode : Except ChainQError CheckedCSSCode) : Except TypeError TypedEnv :=
  match typedBlockOf? checkedCode with
  | .ok tb => .ok { blocks := [tb, tb] }
  | .error e => .error e

def identityIncidence (n : Nat) : BoolMat := ChainQ.GF2.identMat n

def batchSelfCNOTOk (checkedCode : Except ChainQError CheckedCSSCode) (n k : Nat) : Bool :=
  match twoCopyEnv? checkedCode with
  | .ok Gamma =>
      ok? (checkTransversalCNOTBatch Gamma
        { controlBlock := 0,
          targetBlock := 1,
          incidence := identityIncidence n,
          logicalIncidence := ChainQ.GF2.identMat k })
  | .error _ => false

def singletonSelfCNOTOk (checkedCode : Except ChainQError CheckedCSSCode) (n : Nat) : Bool :=
  match twoCopyEnv? checkedCode with
  | .ok Gamma =>
      ok? (checkTransversalCNOT Gamma
        { control := { blk := 0, idx := 0 },
          target := { blk := 1, idx := 0 },
          incidence := identityIncidence n })
  | .error _ => false

def batchSelfCNOTSource (n k : Nat) : List Compiler.LogicalOp :=
  [.transversalLogicalCNOTBatch 0 1 (identityIncidence n) (ChainQ.GF2.identMat k)]

def batchSelfCNOTSourceCompilesOk
    (checkedCode : Except ChainQError CheckedCSSCode) (n k : Nat) : Bool :=
  match twoCopyEnv? checkedCode with
  | .ok Gamma =>
      ok? (Compiler.compile? Compiler.CompileMode.executable
        { caps := [], anc := { blk := 0, idx := 0 } }
        Gamma (batchSelfCNOTSource n k))
  | .error _ => false

def batchSelfCNOTSourceLowersToBatch
    (checkedCode : Except ChainQError CheckedCSSCode) (n k : Nat) : Bool :=
  match twoCopyEnv? checkedCode with
  | .ok Gamma =>
      match Compiler.compile? Compiler.CompileMode.executable
          { caps := [], anc := { blk := 0, idx := 0 } }
          Gamma (batchSelfCNOTSource n k) with
      | .ok c =>
          match c.prog with
          | [.transversalCNOTBatch spec] =>
              spec.controlBlock == 0 && spec.targetBlock == 1 &&
              spec.incidence == identityIncidence n &&
              spec.logicalIncidence == ChainQ.GF2.identMat k
          | _ => false
      | .error _ => false
  | .error _ => false

/-! ## Full paper instances.

    `adapterBB1` and `adapterLP2` are intentionally defined above as concrete
    values, but not reduced by ordinary `by decide` examples here. Their rank and
    logical-basis reductions are large enough to make routine module builds slow.
    Use `#eval`/CI-heavy checks for those full-size parameter confirmations. -/

/-! ## Constructor regressions for dimension-jump paper rows. -/

example : (match dimJumpBB18 with | .ok cc => cc.code.n | .error _ => 0) = 18 := by decide
example : (match dimJumpBB18 with | .ok cc => cc.code.k | .error _ => 0) = 2 := by decide
example : (match dimJumpBB30 with | .ok cc => cc.code.n | .error _ => 0) = 30 := by decide
example : (match dimJumpBB30 with | .ok cc => cc.code.k | .error _ => 0) = 2 := by decide
example : (match dimJumpBB54 with | .ok cc => cc.code.n | .error _ => 0) = 54 := by native_decide
example : (match dimJumpBB54 with | .ok cc => cc.code.k | .error _ => 0) = 2 := by native_decide

example : (match liftedToric16 with | .ok cc => cc.code.n | .error _ => 0) = 16 := by decide
example : (match liftedToric16 with | .ok cc => cc.code.k | .error _ => 0) = 2 := by decide
example : (match liftedToric36 with | .ok cc => cc.code.n | .error _ => 0) = 36 := by decide
example : (match liftedToric36 with | .ok cc => cc.code.k | .error _ => 0) = 2 := by decide

/-! ## Primitive semantic regressions on concrete paper LP/BB codes. -/

-- A physical identity matching between two identical high-rate blocks implements
-- the whole batched logical CNOT incidence, not just one addressed pair.
example : batchSelfCNOTOk dimJumpBB18 18 2 = true := by native_decide
example : batchSelfCNOTOk liftedToric16 16 2 = true := by native_decide
example : batchSelfCNOTSourceCompilesOk dimJumpBB18 18 2 = true := by native_decide
example : batchSelfCNOTSourceCompilesOk liftedToric16 16 2 = true := by native_decide
example : batchSelfCNOTSourceLowersToBatch dimJumpBB18 18 2 = true := by native_decide

-- The singleton primitive correctly rejects that same whole-block operation:
-- it is not "CNOT logical 0 -> logical 0"; it is a batched CNOT on both logicals.
example : singletonSelfCNOTOk dimJumpBB18 18 = false := by native_decide
example : singletonSelfCNOTOk liftedToric16 16 = false := by native_decide

-- Shape safety: a logical incidence matrix with the wrong logical arity is rejected.
example : (match twoCopyEnv? dimJumpBB18 with
           | .ok Gamma =>
               ok? (checkTransversalCNOTBatch Gamma
                 { controlBlock := 0, targetBlock := 1,
                   incidence := identityIncidence 18,
                   logicalIncidence := [[true]] })
           | .error _ => false) = false := by native_decide

end Compiler.CodeSwitch.QLDPCPaperConcrete
