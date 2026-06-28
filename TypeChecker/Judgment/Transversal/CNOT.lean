/-
  TypeChecker.Judgment.Transversal.CNOT -- inter-block transversal logical CNOT.

  This is the first-class checker for source syntax of the form

      Transversal Logical CNOT q_control q_target

  The certificate is a physical CNOT incidence matrix between two live blocks.  The
  checker enforces the paper-level "physical transversality" condition directly:
  every physical qubit participates in at most one CNOT, i.e. every row and every
  column of the incidence matrix has weight at most one.  It then recomputes the
  joint symplectic action and checks that the induced logical operation is exactly
  the requested logical CNOT, modulo the product stabilizer.
-/
import TypeChecker.Judgment.Transversal.Check
import Logical.Basic

namespace TypeChecker
open ChainQ ChainQ.GF2 Logical

/-! ## Certificate data. -/

/-- A physical incidence certificate for a one-way transversal/homomorphic CNOT.
    `incidence[i][j] = true` means "apply physical CNOT from control physical
    qubit `i` to target physical qubit `j`". -/
structure TransversalCNOTSpec where
  control   : LQubit
  target    : LQubit
  incidence : BoolMat
  deriving Repr, DecidableEq

/-- Evidence that an incidence-certified transversal CNOT is legal and induces
    exactly the requested logical CNOT. -/
structure TypedTransversalCNOT where
  spec       : TransversalCNOTSpec
  map        : BoolMat
  jointStab  : BoolMat
  inducedLX  : BoolMat
  inducedLZ  : BoolMat
  expectedLX : BoolMat
  expectedLZ : BoolMat
  deriving Repr

/-- A block-level/batched physical CNOT certificate.  The physical `incidence`
    still describes one-way CNOTs between physical qubits, while
    `logicalIncidence[i][j] = true` requests a logical CNOT from logical `i` of
    `controlBlock` to logical `j` of `targetBlock`.

    This is the form needed by high-rate qLDPC constructions: a sparse physical
    transversal can implement many logical CNOTs in parallel, and a singleton
    logical incidence recovers `TransversalCNOTSpec`. -/
structure TransversalCNOTBatchSpec where
  controlBlock     : BlockId
  targetBlock      : BlockId
  incidence        : BoolMat
  logicalIncidence : BoolMat
  deriving Repr, DecidableEq

/-- Evidence that a batched incidence-certified transversal CNOT is legal. -/
structure TypedTransversalCNOTBatch where
  spec       : TransversalCNOTBatchSpec
  map        : BoolMat
  jointStab  : BoolMat
  inducedLX  : BoolMat
  inducedLZ  : BoolMat
  expectedLX : BoolMat
  expectedLZ : BoolMat
  deriving Repr

/-! ## Physical and logical helpers. -/

def Internal.atMostOneTrue (row : BoolVec) : Bool :=
  decide (row.countP (fun b => b) <= 1)

/-- Shape plus row/column weight-at-most-one, the computable physical
    transversality condition used by dimension-jump and homomorphic-CNOT papers. -/
def Internal.physicallyTransversalIncidence (nC nT : Nat) (A : BoolMat) : Bool :=
  decide (A.length = nC) &&
  A.all (fun r => decide (r.length = nT) && Internal.atMostOneTrue r) &&
  (transpose A nT).all Internal.atMostOneTrue

/-- Embed a Pauli row from the control block into the joint block
    `(X_C, X_T, Z_C, Z_T)`. -/
def Internal.embedControlRow (nC nT : Nat) (row : BoolVec) : BoolVec :=
  row.take nC ++ List.replicate nT false ++ row.drop nC ++ List.replicate nT false

/-- Embed a Pauli row from the target block into the joint block
    `(X_C, X_T, Z_C, Z_T)`. -/
def Internal.embedTargetRow (nC nT : Nat) (row : BoolVec) : BoolVec :=
  List.replicate nC false ++ row.take nT ++ List.replicate nC false ++ row.drop nT

def Internal.embedControlRows (nC nT : Nat) (rows : BoolMat) : BoolMat :=
  rows.map (Internal.embedControlRow nC nT)

def Internal.embedTargetRows (nC nT : Nat) (rows : BoolMat) : BoolMat :=
  rows.map (Internal.embedTargetRow nC nT)

def Internal.jointStab (C T : Block) : BoolMat :=
  Internal.embedControlRows C.n T.n C.stab ++ Internal.embedTargetRows C.n T.n T.stab

def Internal.jointLX (C T : Block) : BoolMat :=
  Internal.embedControlRows C.n T.n C.lx ++ Internal.embedTargetRows C.n T.n T.lx

def Internal.jointLZ (C T : Block) : BoolMat :=
  Internal.embedControlRows C.n T.n C.lz ++ Internal.embedTargetRows C.n T.n T.lz

def Internal.zeroJointRow (nC nT : Nat) : BoolVec :=
  List.replicate (2 * (nC + nT)) false

def Internal.mapIdxRowsAux (f : Nat -> BoolVec -> BoolVec) : Nat -> BoolMat -> BoolMat
  | _, [] => []
  | i, row :: rows => f i row :: Internal.mapIdxRowsAux f (i + 1) rows

def Internal.mapIdxRows (f : Nat -> BoolVec -> BoolVec) (rows : BoolMat) : BoolMat :=
  Internal.mapIdxRowsAux f 0 rows

/-- XOR the selected rows.  A malformed selector simply ignores missing rows via
    `zip`; callers shape-check selectors before using this in certificates. -/
def Internal.xorSelectedRows (zero : BoolVec) (selectors : BoolVec) (rows : BoolMat) :
    BoolVec :=
  (selectors.zip rows).foldl
    (fun acc p => if p.1 then vecXor acc p.2 else acc) zero

/-- Shape check for a logical CNOT incidence matrix. -/
def Internal.logicalIncidenceWf (kC kT : Nat) (L : BoolMat) : Bool :=
  decide (L.length = kC) && L.all (fun row => decide (row.length = kT))

/-- A singleton logical-incidence matrix for one requested logical CNOT. -/
def Internal.singletonLogicalIncidence (kC kT controlIdx targetIdx : Nat) : BoolMat :=
  (List.range kC).map (fun i =>
    (List.range kT).map (fun j => decide (i = controlIdx && j = targetIdx)))

/-- Expected logical-X image for a batched logical CNOT incidence:
    `X_c[i] -> X_c[i] * Π_j X_t[j]^{L[i,j]}`. -/
def Internal.expectedCNOTBatchLX (C T : Block) (logicalIncidence : BoolMat) : BoolMat :=
  let cLX := Internal.embedControlRows C.n T.n C.lx
  let tLX := Internal.embedTargetRows C.n T.n T.lx
  let zero := Internal.zeroJointRow C.n T.n
  (cLX.zip logicalIncidence).map
    (fun p => vecXor p.1 (Internal.xorSelectedRows zero p.2 tLX)) ++ tLX

/-- Expected logical-Z image for a batched logical CNOT incidence:
    `Z_t[j] -> Π_i Z_c[i]^{L[i,j]} * Z_t[j]`. -/
def Internal.expectedCNOTBatchLZ (C T : Block) (logicalIncidence : BoolMat) : BoolMat :=
  let cLZ := Internal.embedControlRows C.n T.n C.lz
  let tLZ := Internal.embedTargetRows C.n T.n T.lz
  let zero := Internal.zeroJointRow C.n T.n
  let logicalColumns := transpose logicalIncidence T.lz.length
  cLZ ++ (tLZ.zip logicalColumns).map
    (fun p => vecXor (Internal.xorSelectedRows zero p.2 cLZ) p.1)

/-- Expected logical-X image for CNOT(control,target):
    `X_c -> X_c X_t`, all other X-logicals unchanged. -/
def Internal.expectedCNOTLX (C T : Block) (controlIdx targetIdx : Nat) : BoolMat :=
  let cLX := Internal.embedControlRows C.n T.n C.lx
  let tLX := Internal.embedTargetRows C.n T.n T.lx
  let targetX := tLX.getD targetIdx (Internal.zeroJointRow C.n T.n)
  Internal.mapIdxRows (fun i row => if i == controlIdx then vecXor row targetX else row) cLX ++ tLX

/-- Expected logical-Z image for CNOT(control,target):
    `Z_t -> Z_c Z_t`, all other Z-logicals unchanged. -/
def Internal.expectedCNOTLZ (C T : Block) (controlIdx targetIdx : Nat) : BoolMat :=
  let cLZ := Internal.embedControlRows C.n T.n C.lz
  let tLZ := Internal.embedTargetRows C.n T.n T.lz
  let controlZ := cLZ.getD controlIdx (Internal.zeroJointRow C.n T.n)
  cLZ ++ Internal.mapIdxRows (fun i row => if i == targetIdx then vecXor row controlZ else row) tLZ

/-- Row-wise equality modulo a stabilizer span. -/
def Internal.rowsEqualModStab (S A B : BoolMat) : Bool :=
  decide (A.length = B.length) &&
  (A.zip B).all (fun p => decide (p.1.length = p.2.length) && inSpan S (vecXor p.1 p.2))

/-- The joint symplectic map of physical CNOTs described by incidence `A`.
    Row-vector convention: Pauli rows act by `v |-> v * M`. -/
def Internal.cnotMap (nC nT : Nat) (A : BoolMat) : BoolMat :=
  let n := nC + nT
  let total := 2 * n
  let a := fun i j => (A.getD i []).getD j false
  let xControlRows := (List.range nC).map (fun i =>
    (List.range total).map (fun col =>
      decide (col = i) ||
      (List.range nT).any (fun j => decide (col = nC + j) && a i j)))
  let xTargetRows := (List.range nT).map (fun j =>
    (List.range total).map (fun col => decide (col = nC + j)))
  let zControlRows := (List.range nC).map (fun i =>
    (List.range total).map (fun col => decide (col = n + i)))
  let zTargetRows := (List.range nT).map (fun j =>
    (List.range total).map (fun col =>
      decide (col = n + nC + j) ||
      (List.range nC).any (fun i => decide (col = n + i) && a i j)))
  xControlRows ++ xTargetRows ++ zControlRows ++ zTargetRows

/-! ## Checker. -/

def checkTransversalCNOT (Gamma : TypedEnv) (spec : TransversalCNOTSpec) :
    Except TypeError TypedTransversalCNOT :=
  if spec.control == spec.target then
    .error (.certFailed "transversal logical CNOT cannot use the same logical qubit twice")
  else if spec.control.blk == spec.target.blk then
    .error (.certFailed "transversal logical CNOT currently requires two distinct blocks")
  else
    match Gamma.block? spec.control.blk, Gamma.block? spec.target.blk with
    | none, _ => .error (.badBlock spec.control.blk)
    | _, none => .error (.badBlock spec.target.blk)
    | some cTB, some tTB =>
      let C := cTB.block
      let T := tTB.block
      if !C.live then
        .error .notLive
      else if !T.live then
        .error .notLive
      else if !(decide (spec.control.idx < C.lx.length)) then
        .error (.badLogicalIndex spec.control.blk spec.control.idx)
      else if !(decide (spec.target.idx < T.lx.length)) then
        .error (.badLogicalIndex spec.target.blk spec.target.idx)
      else if !Internal.physicallyTransversalIncidence C.n T.n spec.incidence then
        .error (.shapeMismatch "transversal CNOT incidence must be nC x nT with row/column weight <= 1")
      else
        let n := C.n + T.n
        let M := Internal.cnotMap C.n T.n spec.incidence
        let S := Internal.jointStab C T
        let LX := Internal.jointLX C T
        let LZ := Internal.jointLZ C T
        let inducedLX := applyMap n M LX
        let inducedLZ := applyMap n M LZ
        let expectedLX := Internal.expectedCNOTLX C T spec.control.idx spec.target.idx
        let expectedLZ := Internal.expectedCNOTLZ C T spec.control.idx spec.target.idx
        if !preservesSymp n M then
          .error .notSymplectic
        else if !((applyMap n M S).all (fun r => inSpan S r)) then
          .error .stabilizerNotPreserved
        else if !Internal.rowsEqualModStab S inducedLX expectedLX then
          .error (.certFailed "transversal CNOT does not induce the requested logical X action")
        else if !Internal.rowsEqualModStab S inducedLZ expectedLZ then
          .error (.certFailed "transversal CNOT does not induce the requested logical Z action")
        else
          .ok { spec, map := M, jointStab := S, inducedLX, inducedLZ, expectedLX, expectedLZ }

/-- Batched/block-level transversal CNOT checker.  This is the qLDPC-friendly
    generalization of `checkTransversalCNOT`: it verifies the physical sparse
    incidence and the complete induced logical CNOT incidence in one certificate. -/
def checkTransversalCNOTBatch (Gamma : TypedEnv) (spec : TransversalCNOTBatchSpec) :
    Except TypeError TypedTransversalCNOTBatch :=
  if spec.controlBlock == spec.targetBlock then
    .error (.certFailed "batched transversal CNOT requires two distinct blocks")
  else
    match Gamma.block? spec.controlBlock, Gamma.block? spec.targetBlock with
    | none, _ => .error (.badBlock spec.controlBlock)
    | _, none => .error (.badBlock spec.targetBlock)
    | some cTB, some tTB =>
      let C := cTB.block
      let T := tTB.block
      if !C.live then
        .error .notLive
      else if !T.live then
        .error .notLive
      else if !Internal.logicalIncidenceWf C.lx.length T.lx.length spec.logicalIncidence then
        .error (.shapeMismatch "logical CNOT incidence must be kC x kT")
      else if !Internal.physicallyTransversalIncidence C.n T.n spec.incidence then
        .error (.shapeMismatch "transversal CNOT incidence must be nC x nT with row/column weight <= 1")
      else
        let n := C.n + T.n
        let M := Internal.cnotMap C.n T.n spec.incidence
        let S := Internal.jointStab C T
        let LX := Internal.jointLX C T
        let LZ := Internal.jointLZ C T
        let inducedLX := applyMap n M LX
        let inducedLZ := applyMap n M LZ
        let expectedLX := Internal.expectedCNOTBatchLX C T spec.logicalIncidence
        let expectedLZ := Internal.expectedCNOTBatchLZ C T spec.logicalIncidence
        if !preservesSymp n M then
          .error .notSymplectic
        else if !((applyMap n M S).all (fun r => inSpan S r)) then
          .error .stabilizerNotPreserved
        else if !Internal.rowsEqualModStab S inducedLX expectedLX then
          .error (.certFailed "batched transversal CNOT does not induce the requested logical X action")
        else if !Internal.rowsEqualModStab S inducedLZ expectedLZ then
          .error (.certFailed "batched transversal CNOT does not induce the requested logical Z action")
        else
          .ok { spec, map := M, jointStab := S, inducedLX, inducedLZ, expectedLX, expectedLZ }

end TypeChecker
