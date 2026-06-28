/-
  Compiler.Verification.Basic -- post-compilation verification harnesses.

  These check compiled artifacts directly.  They do not need to know how a magic
  qLDPC protocol was synthesized; once the artifact is PPM, Mixed, or a richer
  QStab stabilizer program, verification is ordinary type/dataflow checking plus
  explicit expected readout/measurement obligations.
-/
import Compiler.Mixed.Check
import Compiler.LS.PPM
import Compiler.LS.Extract
import Compiler.QStab2QClifford.Basic
import QStab.Basic

namespace Compiler.Verification
open Compiler TypeChecker PPM QStab ChainQ.GF2

/-- Expected logical Pauli measurements after lowering to PPM. -/
structure PPMVerificationSpec where
  expectedTargets : List MTarget := []
  deriving Repr, Inhabited

/-- Verify a PPM artifact: it type-checks from the initial PPM state and its
    logical measurement targets are exactly the expected list. -/
def verifyPPMProgram (Gamma : TypedEnv) (caps : List Capability)
    (stmt : PPM.Stmt) (spec : PPMVerificationSpec) : Except TypeError PPMState := do
  let st ← checkPPMProgram Gamma caps stmt
  if measTargets stmt == spec.expectedTargets then
    .ok st
  else
    .error (.certFailed "compiled PPM measurement targets do not match the verification spec")

/-- Collect all PPM measurement targets inside a mixed logical-execution program. -/
def logicalExecMeasTargets : LogicalExec -> List MTarget
  | [] => []
  | .ppm stmt :: rest => measTargets stmt ++ logicalExecMeasTargets rest
  | _ :: rest => logicalExecMeasTargets rest

/-- Expected obligations for a compiled mixed program.  By default verification
    requires an executable artifact with no deferred magic obligation. -/
structure LogicalExecVerificationSpec where
  expectedPPMTargets : List MTarget := []
  requireNoMagic : Bool := true
  deriving Repr, Inhabited

/-- Verify a compiled mixed artifact using the existing operation checker, then
    check the PPM measurement interface it exposes. -/
def verifyLogicalExec (caps : List Capability) (Gamma : TypedEnv)
    (prog : LogicalExec) (spec : LogicalExecVerificationSpec) :
    Except TypeError TypedEnv := do
  if spec.requireNoMagic && !progNoMagic prog then
    .error (.notImplemented "verification artifact still contains a deferred magic obligation")
  else
    let Gamma' ← checkLogicalExec caps Gamma prog
    if logicalExecMeasTargets prog == spec.expectedPPMTargets then
      .ok Gamma'
    else
      .error (.certFailed "compiled mixed PPM targets do not match the verification spec")

/-- A noiseless QStab readout obligation.  `false` is the all-+1/no-defect value. -/
structure QStabReadoutSpec where
  var : QVar
  expectedNoiseless : Bool
  deriving Repr, Inhabited

def readoutsHold (readVar : QVar -> Bool) : List QStabReadoutSpec -> Bool
  | [] => true
  | r :: rest => (readVar r.var == r.expectedNoiseless) && readoutsHold readVar rest

structure QStabVerificationSpec where
  readouts : List QStabReadoutSpec := []
  deriving Repr, Inhabited

/-- Verify a pure QStab dataflow artifact. -/
def verifyQStabDataflow (prog : QStab.Prog) (spec : QStabVerificationSpec) :
    Except TypeError Unit :=
  if !prog.wf then
    .error (.certFailed "QStab dataflow is not well-formed")
  else if readoutsHold (fun v => QStab.evalVar prog (fun _ => false) v) spec.readouts then
    .ok ()
  else
    .error (.certFailed "QStab noiseless readout obligations failed")

/-- Verify a richer stabilizer-formalism QStab program by checking its quantum
    instruction dataflow discipline and its projected measurement/parity readouts. -/
def verifyStabilizerProgram (prog : StabilizerProg) (spec : QStabVerificationSpec) :
    Except TypeError Unit :=
  if !prog.wf then
    .error (.certFailed "stabilizer program has an invalid classical dependency")
  else if readoutsHold (fun v => prog.evalVar (fun _ => false) v) spec.readouts then
    .ok ()
  else
    .error (.certFailed "stabilizer program noiseless readout obligations failed")

/-! ## Witness-based verification of lower layers.

    These checks do not claim to synthesize lattice surgery.  They verify that a
    supplied compiled artifact is exactly the QStab object implied by the logical
    PPM instruction and an explicit physical witness or certificate. -/

inductive VerificationError
  | typeError (e : TypeError)
  | lsError (e : Compiler.LS.LSError)
  | qcliffordError (e : Compiler.QStab2QClifford.CompileError)
  | certFailed (msg : String)
  | unsupportedMixed (note : String)   -- a Mixed instruction this verifier does NOT yet lower (honest deferral)
  | layoutError (note : String)        -- a malformed / mismatched physical layout
  deriving Repr

def liftType {α : Type} : Except TypeError α -> Except VerificationError α
  | .ok a => .ok a
  | .error e => .error (.typeError e)

def liftLS {α : Type} : Except Compiler.LS.LSError α -> Except VerificationError α
  | .ok a => .ok a
  | .error e => .error (.lsError e)

def liftQClifford {α : Type} :
    Except Compiler.QStab2QClifford.CompileError α -> Except VerificationError α
  | .ok a => .ok a
  | .error e => .error (.qcliffordError e)

def sameStabilizerInstr : StabilizerInstr -> StabilizerInstr -> Bool
  | .bind s1, .bind s2 => decide (s1 = s2)
  | .prepZero q1, .prepZero q2 => decide (q1 = q2)
  | .prepPlus q1, .prepPlus q2 => decide (q1 = q2)
  | .H q1, .H q2 => decide (q1 = q2)
  | .S q1, .S q2 => decide (q1 = q2)
  | .X q1, .X q2 => decide (q1 = q2)
  | .Z q1, .Z q2 => decide (q1 = q2)
  | .CNOT c1 t1, .CNOT c2 t2 => decide (c1 = c2) && decide (t1 = t2)
  | .CZ a1 b1, .CZ a2 b2 => decide (a1 = a2) && decide (b1 = b2)
  | .ifPauli src1 p1 q1, .ifPauli src2 p2 q2 =>
      decide (src1 = src2) && decide (p1 = p2) && decide (q1 = q2)
  | _, _ => false

def sameStabilizerProg : StabilizerProg -> StabilizerProg -> Bool
  | [], [] => true
  | i :: is, j :: js => sameStabilizerInstr i j && sameStabilizerProg is js
  | _, _ => false

structure PPMMeasurementQStabSpec where
  target : MTarget
  numQubits : Nat
  sched : Option Sched := none
  witness : Compiler.LS.SPauli
  cert? : Option Compiler.LS.SurgeryCert := none
  requireExtractable : Bool := false
  readouts : List QStabReadoutSpec := [{ var := 1, expectedNoiseless := false }]

def lowerPPMWitnessQStab? (spec : PPMMeasurementQStabSpec) :
    Except VerificationError StabilizerProg := do
  let op <- match spec.cert? with
    | none =>
        liftLS (Compiler.LS.ppmMeasToLS? spec.sched spec.target (some spec.witness))
    | some cert =>
        liftLS (Compiler.LS.ppmMeasToLSWithCert? spec.numQubits spec.sched spec.target cert spec.witness)
  let lsProg : Compiler.LS.Program :=
    { numQubits := spec.numQubits, ops := [op, .parity [0]] }
  let lowered <- liftLS (Compiler.LS.lowerChecked lsProg)
  return lowered.1

/-! ### Strengthening: the physical witness must REPRESENT the logical target.

    `verifyPPMMeasurementQStab` previously merely TRUSTED the supplied `LS.SPauli`
    witness — any well-formed measurement was accepted as "the" physical realisation
    of the logical PPM target, so a logical `Z̄` could be "witnessed" by a physical
    `X`/`Y` and still pass (the QStab artifact then faithfully matches that bad
    witness, and `X`/`Y` are otherwise valid measurements).  We now COMPUTE the dense
    physical Pauli representative of the logical target from the `TypedEnv`'s per-block
    logical bases (`lx`/`lz`, via `TypeChecker.targetPOf` in the merged symplectic
    space) and REQUIRE the densified witness to equal it.

    Convention (`ChainQ.GF2`): a width-`2·m` symplectic vector is `[X-part (m bits) |
    Z-part (m bits)]`; qubit `i` carries `(xᵢ, zᵢ) ↦ I/X/Z/Y`. -/

/-- Map a width-`2·m` symplectic Pauli vector `[X-part | Z-part]` to a dense physical
    `QStab.PauliString` over `m` qubits (`(xᵢ, zᵢ) ↦ I/X/Z/Y`). -/
def symToPauliString (m : Nat) (v : ChainQ.GF2.BoolVec) : QStab.PauliString :=
  (List.range m).map (fun i =>
    match v.getD i false, v.getD (m + i) false with
    | false, false => Physical.Pauli.I
    | true,  false => Physical.Pauli.X
    | false, true  => Physical.Pauli.Z
    | true,  true  => Physical.Pauli.Y)

/-- The dense physical Pauli representative of a logical PPM `target`, computed from
    the `TypedEnv` (the touched blocks' `lx`/`lz` symplectic rows, lifted into their
    combined physical space by `TypeChecker.targetPOf`).  `none` exactly when a touched
    block is unknown / not live — i.e. when the representative is NOT computable (never
    a silent identity).  After a successful `checkPPM` this is always `some`. -/
def targetPauliRep? (Gamma : TypedEnv) (target : PPM.MTarget) : Option QStab.PauliString :=
  match gather Gamma (dedupNat (target.map (fun f => f.1.blk))) with
  | none                => none
  | some (bos, mergedN) => some (symToPauliString mergedN (targetPOf bos mergedN target))

/-- The witness check: WHEN the `TypedEnv` representative of the logical target is
    computable, the supplied witness (densified over `spec.numQubits`) must equal it.
    A non-computable representative (`none`) imposes no extra constraint — the other
    checks (type-check, artifact match, cert) still apply.  This is what removes the
    blind trust in the witness: a physical Pauli that does not represent the logical
    operator is rejected even if the QStab artifact faithfully matches it. -/
def witnessRepresentsTarget (Gamma : TypedEnv) (spec : PPMMeasurementQStabSpec) :
    Except VerificationError Unit :=
  match targetPauliRep? Gamma spec.target with
  | none     => .ok ()
  | some rep =>
      if decide (Compiler.LS.SPauli.toDense spec.numQubits spec.witness = rep) then .ok ()
      else .error (.certFailed
        "physical witness does not densify to the TypedEnv representative of the logical PPM target")

def verifyPPMMeasurementQStab (Gamma : TypedEnv) (caps : List Capability)
    (artifact : StabilizerProg) (spec : PPMMeasurementQStabSpec) :
    Except VerificationError Unit := do
  let _typed <- liftType (checkPPM Gamma caps spec.target)
  witnessRepresentsTarget Gamma spec
  let expected <- lowerPPMWitnessQStab? spec
  if !sameStabilizerProg artifact expected then
    .error (.certFailed "QStab artifact does not match the logical PPM witness lowering")
  else do
    liftType (verifyStabilizerProgram artifact { readouts := spec.readouts })
    if spec.requireExtractable && !(Compiler.LS.extractObligations artifact.dataflow).isEmpty then
      .error (.certFailed "QStab artifact contains a measurement not extractable by current schemes")
    else
      .ok ()

structure QCliffordVerificationSpec where
  source : QStab.Prog
  cfg : Compiler.QStab2QClifford.CompileConfig
  readouts : List QStabReadoutSpec := []

def verifyQCliffordCircuit (circuit : QClifford.Circuit) (spec : QCliffordVerificationSpec) :
    Except VerificationError Unit := do
  liftType (verifyQStabDataflow spec.source { readouts := spec.readouts })
  let expected <- liftQClifford (Compiler.QStab2QClifford.compile? spec.cfg spec.source)
  if decide (circuit = expected) then
    .ok ()
  else
    .error (.certFailed "QClifford circuit does not match the checked QStab extraction")

/-! ## Executable smoke checks. -/

example : ok? (verifyPPMProgram tenvQ [] (.meas 0 [(⟨0, 0⟩, PLetter.Z)])
    { expectedTargets := [[(⟨0, 0⟩, PLetter.Z)]] }) = true := by decide

example : ok? (verifyPPMProgram tenvQ [] (.meas 0 [(⟨0, 0⟩, PLetter.Z)])
    { expectedTargets := [[(⟨0, 0⟩, PLetter.X)]] }) = false := by decide

example : ok? (verifyLogicalExec [] tenvQ
    [.transversal 0 hGate2x2, .ppm (.meas 0 [(⟨0, 0⟩, PLetter.Z)])]
    { expectedPPMTargets := [[(⟨0, 0⟩, PLetter.Z)]] }) = true := by decide

example : ok? (verifyLogicalExec [] tenvQ
    [.magic { kind := .tGate, target := ⟨0, 0⟩ }]
    {}) = false := by decide

example : ok? (verifyQStabDataflow QStab.progReadout
    { readouts := [{ var := 7, expectedNoiseless := false }] }) = true := by decide

example : ok? (verifyStabilizerProgram QStab.exampleStabilizerProg
    { readouts := [{ var := 1, expectedNoiseless := false }] }) = true := by decide

example : ok? (verifyStabilizerProgram [.ifPauli 0 .X 0]
    { readouts := [] }) = false := by decide

def ppmZSpec : PPMMeasurementQStabSpec :=
  { target := [({ blk := 0, idx := 0 }, PLetter.Z)]
    numQubits := 1
    sched := some ⟨0, 0⟩
    witness := [(0, .Z)]
    requireExtractable := true }

def ppmZArtifact : StabilizerProg :=
  [ .bind (.prop (some ⟨0, 0⟩) (Physical.ofString "Z")),
    .bind (.parity [0]) ]

example : ok? (verifyPPMMeasurementQStab tenvQ [] ppmZArtifact ppmZSpec) = true := by decide

example :
    ok? (verifyPPMMeasurementQStab tenvQ [] ([.prepZero 0] ++ ppmZArtifact) ppmZSpec) = false := by
  decide

def ppmYSpec : PPMMeasurementQStabSpec :=
  { ppmZSpec with witness := [(0, .Y)] }

example : ok? (verifyPPMMeasurementQStab tenvQ [] ppmZArtifact ppmYSpec) = false := by decide

def ppmYArtifact : StabilizerProg :=
  [ .bind (.prop (some ⟨0, 0⟩) (Physical.ofString "Y")),
    .bind (.parity [0]) ]

example : ok? (verifyPPMMeasurementQStab tenvQ [] ppmYArtifact ppmYSpec) = false := by decide

def qcliffordZSpec : QCliffordVerificationSpec :=
  { source := [.prop none (Physical.ofString "Z")]
    cfg := { specOf := fun _ => Compiler.QStab2QClifford.destZ 0 }
    readouts := [{ var := 0, expectedNoiseless := false }] }

example :
    ok? (verifyQCliffordCircuit [.meas 0 0] qcliffordZSpec) = true := by
  decide

example :
    ok? (verifyQCliffordCircuit [.H 0, .meas 0 0] qcliffordZSpec) = false := by
  decide

/-! ## Witness-represents-target strengthening (TypedEnv-computed representative).

    These exercise the new check that the supplied physical witness ACTUALLY
    represents the logical target — not merely that the artifact matches the witness. -/

-- the TypedEnv representative of the logical `Z̄` on the bare qubit IS a physical `Z`:
example : targetPauliRep? tenvQ [(⟨0, 0⟩, PLetter.Z)] = some (Physical.ofString "Z") := by decide

-- (a) logical Z with the MATCHING physical Z witness is accepted (rep = witness):
example : ok? (verifyPPMMeasurementQStab tenvQ [] ppmZArtifact ppmZSpec) = true := by decide

/-- A logical-`Z̄` spec whose witness is a physical `X` — an INVALID realisation.
    `requireExtractable := false`, so the rejection is due to the witness/representative
    mismatch ALONE (a physical `X` IS extractable, so the extractability gate would not
    catch it). -/
def ppmZBadXSpec : PPMMeasurementQStabSpec :=
  { target := [(⟨0, 0⟩, PLetter.Z)]
    numQubits := 1
    sched := some ⟨0, 0⟩
    witness := [(0, .X)]
    requireExtractable := false }

/-- The QStab artifact that FAITHFULLY matches the (bad) `X` witness lowering. -/
def ppmXArtifact : StabilizerProg :=
  [ .bind (.prop (some ⟨0, 0⟩) (Physical.ofString "X")),
    .bind (.parity [0]) ]

-- (b) the bad-`X` case: the artifact DOES match the witness lowering (artifact-match
-- gate passes), and the physical `X` IS extractable (extractability gate passes) …
example : (match lowerPPMWitnessQStab? ppmZBadXSpec with
           | .ok p => sameStabilizerProg p ppmXArtifact | .error _ => false) = true := by decide
example : (Compiler.LS.extractObligations ppmXArtifact.dataflow).isEmpty = true := by decide
-- … yet verification now REJECTS it: a physical `X` does not represent the logical `Z̄`:
example : ok? (verifyPPMMeasurementQStab tenvQ [] ppmXArtifact ppmZBadXSpec) = false := by decide

/-- The same hole with a physical `Y` witness. -/
def ppmZBadYSpec : PPMMeasurementQStabSpec := { ppmZBadXSpec with witness := [(0, .Y)] }

-- (b) the bad-`Y` case: the artifact matches the bad witness lowering, yet it is REJECTED
-- (here `ppmYArtifact`, defined above, is exactly the `Y` witness lowering):
example : (match lowerPPMWitnessQStab? ppmZBadYSpec with
           | .ok p => sameStabilizerProg p ppmYArtifact | .error _ => false) = true := by decide
example : ok? (verifyPPMMeasurementQStab tenvQ [] ppmYArtifact ppmZBadYSpec) = false := by decide

/-! ### The cert-gated path still works (and is now ALSO backstopped by the rep check). -/

/-- An honest surgery certificate whose measured parity is the physical `Z`
    (matching the logical `Z̄` target). -/
def ppmZCert : Compiler.LS.SurgeryCert where
  measuredParity        := Physical.ofString "Z"
  preservedLogicals     := [Physical.ofString "X"]
  byproductFrame        := []
  claimedMergedCommutes := true
  claimedDetectorsDet   := true
  claimedIrreducible    := true
  faults                := {}

def ppmZCertSpec : PPMMeasurementQStabSpec := { ppmZSpec with cert? := some ppmZCert }

-- (c) the cert-gated verification of a logical Z with a matching Z witness + artifact
-- is still ACCEPTED (existing cert behaviour intact):
example : ok? (verifyPPMMeasurementQStab tenvQ [] ppmZArtifact ppmZCertSpec) = true := by decide

/-- A cert that (dishonestly) certifies a physical `X` parity for the logical `Z̄`
    target, with a matching `X` witness + artifact: the cert path WOULD lower it (the
    witness densifies to the cert's `X` parity), but the rep check now BACKSTOPS it. -/
def ppmZCertBadSpec : PPMMeasurementQStabSpec :=
  { ppmZBadXSpec with cert? := some { ppmZCert with measuredParity := Physical.ofString "X" } }

-- (c) the cert path alone would accept the bad witness (it densifies to the cert parity) …
example : (lowerPPMWitnessQStab? ppmZCertBadSpec).toOption.isSome = true := by decide
-- … but the strengthened verifier REJECTS it (the witness does not represent `Z̄`):
example : ok? (verifyPPMMeasurementQStab tenvQ [] ppmXArtifact ppmZCertBadSpec) = false := by decide

/-! ## MixedIR → QStab verification (the DIRECT transversal fragment).

    MixedIR carries the QEC type system; QStab is stripped physical stabilizer
    instructions.  This verifier carries the Mixed type/certificate information down to
    QStab: it (1) runs the EXISTING Mixed checker (`checkInstr`, which for these
    instructions is exactly `checkTransversal` / `checkTransversalCNOT` /
    `checkTransversalCNOTBatch`), (2) reconstructs the PHYSICAL operation implied by the
    certificate (the H/S on every physical qubit of the block, or the physical `.CNOT`s
    of the incidence), and (3) requires the supplied artifact to match it structurally,
    then (4) runs `verifyStabilizerProgram`.  Unsupported Mixed instructions
    (automorphism / switch / PPM-program / magic / pauli) return an explicit
    `unsupportedMixed` — never a silent accept.

    SCOPE: this is the FIRST MixedIR→QStab edge and covers only the direct transversal
    fragment.  Automorphism / code-switch / PPM-program-wide lowering are NOT claimed. -/

/-- A Bool no-duplicates check over `Nat`. -/
def nodupNat : List Nat → Bool
  | []      => true
  | x :: xs => !xs.contains x && nodupNat xs

/-- A PHYSICAL LAYOUT: each Mixed block id is placed at a CONTIGUOUS range of QStab
    physical qubits.  A placement `(b, base, count)` maps block `b`'s local physical
    qubit `i ∈ [0, count)` to the QStab physical qubit `base + i`. -/
structure PhysLayout where
  placements : List (Nat × Nat × Nat)   -- (blockId, base, count)
  deriving Repr, DecidableEq

/-- The `(base, count)` placement of block `b` (`none` if the block is unknown). -/
def PhysLayout.find? (L : PhysLayout) (b : Nat) : Option (Nat × Nat) :=
  (L.placements.find? (fun p => p.1 == b)).map (fun p => p.2)

/-- The QStab physical qubit for block `b`'s local physical qubit `i`; `none` if the
    block is unknown to the layout or `i` is out of range. -/
def PhysLayout.qubit? (L : PhysLayout) (b i : Nat) : Option Physical.PQubit :=
  match L.find? b with
  | none             => none
  | some (base, cnt) => if i < cnt then some (base + i) else none

/-- All QStab physical qubits assigned to block `b`, in local order (`none` if the
    block is unknown). -/
def PhysLayout.blockQubits? (L : PhysLayout) (b : Nat) : Option (List Physical.PQubit) :=
  (L.find? b).map (fun bc => (List.range bc.2).map (fun i => bc.1 + i))

/-- Every QStab physical destination the layout assigns. -/
def PhysLayout.dests (L : PhysLayout) : List Physical.PQubit :=
  L.placements.flatMap (fun p => (List.range p.2.2).map (fun i => p.2.1 + i))

/-- A layout is WELL-FORMED: distinct block ids AND no two `(block, local qubit)` pairs
    map to the same physical destination (so the ranges do not overlap / duplicate). -/
def PhysLayout.wf (L : PhysLayout) : Bool :=
  nodupNat (L.placements.map (fun p => p.1)) && nodupNat L.dests

/-- The `(i, j)` positions where `incidence[i][j] = true`, row-major (control physical
    qubit `i` outer, target physical qubit `j` inner). -/
def cnotTrueEntries (incidence : ChainQ.GF2.BoolMat) : List (Nat × Nat) :=
  (List.range incidence.length).flatMap (fun i =>
    let row := incidence.getD i []
    (List.range row.length).filterMap (fun j =>
      if row.getD j false then some (i, j) else none))

/-- Lower a list of physical-CNOT incidence positions to QStab `.CNOT`s through the
    layout, preserving order.  Any position referencing a qubit absent from the layout
    is a `layoutError`. -/
def cnotEntriesToQStab (cBlk tBlk : Nat) (L : PhysLayout) :
    List (Nat × Nat) → Except VerificationError StabilizerProg
  | []            => .ok []
  | (i, j) :: rest =>
    match L.qubit? cBlk i, L.qubit? tBlk j with
    | some c, some t =>
        match cnotEntriesToQStab cBlk tBlk L rest with
        | .ok cs   => .ok (StabilizerInstr.CNOT c t :: cs)
        | .error e => .error e
    | _, _ => .error (.layoutError "CNOT incidence references a physical qubit absent from the layout")

/-- A layout COMPLETELY COVERS block `b`: the block exists in `Gamma`, the layout has a
    placement for it, AND that placement's physical-qubit count equals the typed block's
    `n` — so EVERY physical qubit of `b` is mapped, not just the ones a sparse incidence
    happens to touch.  This is what makes the QStab physical interpretation COMPLETE: a
    partial layout (e.g. mapping 1 of 2 physical qubits) is rejected even when the
    artifact only references the mapped qubits. -/
def requireLayoutCoversBlock (Gamma : TypedEnv) (L : PhysLayout) (b : Nat) :
    Except VerificationError Unit :=
  match Gamma.block? b with
  | none => .error (.typeError (.badBlock b))
  | some tb =>
    match L.find? b with
    | none          => .error (.layoutError s!"layout has no placement for block {b}")
    | some (_, cnt) =>
      if decide (cnt = tb.block.n) then .ok ()
      else .error (.layoutError
        s!"layout placement for block {b} covers {cnt} physical qubits but the block has {tb.block.n}")

/-! ## Layout-aware logical Pauli representative + PPM/Pauli QStab verification.

    `targetPauliRep?` (above) gives the COMPACT merged-block representative — its qubit
    order follows `gather`, NOT the QStab program's global qubit indices.  The functions
    below give the LAYOUT-AWARE representative over the GLOBAL QStab physical qubits fixed
    by a `PhysLayout`, so a global artifact cannot be faked by relying on a different
    (compact) ordering.  Every step is total and HONEST: an unknown block, an
    uncovered/missing layout placement, an out-of-range logical index, or a local qubit
    with no global image is an explicit error — never a silent identity. -/

/-- The total QStab physical-qubit count a layout spans (`max destination + 1`). -/
def PhysLayout.size (L : PhysLayout) : Nat :=
  match L.dests with
  | [] => 0
  | _  => (L.dests.foldl Nat.max 0) + 1

/-- The per-block symplectic restriction (width `2·n`) of a target's factors ON block
    `blk`: the XOR of the factor representatives.  `none` if any factor's logical index
    is out of range (`factorRep?` is the SAFE, never-zero accessor) — never a silent
    identity. -/
def blockRestrict? (blk : Block) : PPM.MTarget → Option ChainQ.GF2.BoolVec
  | []        => some (zeros (2 * blk.n))
  | f :: rest =>
    match factorRep? blk f.1.idx f.2, blockRestrict? blk rest with
    | some r, some acc => some (ChainQ.GF2.vecXor r acc)
    | _, _             => none

/-- Place block `b`'s restriction `v` (width `2·n`) at GLOBAL qubits via the layout: a
    `(global qubit, x-bit, z-bit)` for every NON-identity local qubit.  A local qubit
    with no layout image is an explicit `layoutError`. -/
def placeLocals (L : PhysLayout) (b n : Nat) (v : ChainQ.GF2.BoolVec) :
    List Nat → Except VerificationError (List (Nat × Bool × Bool))
  | []        => .ok []
  | i :: rest =>
    let x := v.getD i false
    let z := v.getD (n + i) false
    match placeLocals L b n v rest with
    | .error e => .error e
    | .ok tail =>
      if x || z then
        match L.qubit? b i with
        | none   => .error (.layoutError s!"block {b} local qubit {i} has no layout image")
        | some g => .ok ((g, x, z) :: tail)
      else .ok tail

/-- Require a layout to cover EVERY block in the list (`requireLayoutCoversBlock`). -/
def requireAllCovered (Gamma : TypedEnv) (L : PhysLayout) :
    List Nat → Except VerificationError Unit
  | []      => .ok ()
  | b :: rest =>
    match requireLayoutCoversBlock Gamma L b with
    | .error e => .error e
    | .ok _    => requireAllCovered Gamma L rest

/-- The GLOBAL `(qubit, x, z)` contributions of a target under a layout, block by block. -/
def globalPauliContribs (Gamma : TypedEnv) (L : PhysLayout) (P : PPM.MTarget) :
    List Nat → Except VerificationError (List (Nat × Bool × Bool))
  | []        => .ok []
  | b :: rest =>
    match Gamma.block? b with
    | none => .error (.typeError (.badBlock b))
    | some tb =>
      match blockRestrict? tb.block (P.filter (fun f => f.1.blk == b)) with
      | none => .error (.certFailed s!"out-of-range logical index in block {b}")
      | some v =>
        match placeLocals L b tb.block.n v (List.range tb.block.n) with
        | .error e => .error e
        | .ok here =>
          match globalPauliContribs Gamma L P rest with
          | .error e => .error e
          | .ok more => .ok (here ++ more)

/-- Densify global `(qubit, x, z)` contributions into a `QStab.PauliString` over `[0, N)`:
    `(x,z) ↦ I/X/Z/Y` (X AND Z on the same global qubit ⟹ `Y`).  Qubits with no
    contribution are `I`. -/
def contribsToDense (N : Nat) (contribs : List (Nat × Bool × Bool)) : QStab.PauliString :=
  (List.range N).map (fun g =>
    match contribs.find? (fun c => c.1 == g) with
    | some (_, x, z) =>
        match x, z with
        | true,  true  => Physical.Pauli.Y
        | true,  false => Physical.Pauli.X
        | false, true  => Physical.Pauli.Z
        | false, false => Physical.Pauli.I
    | none => Physical.Pauli.I)

/-- **The LAYOUT-AWARE logical Pauli representative.**  The dense physical
    `QStab.PauliString` (over the layout's global qubit range `[0, L.size)`) of a logical
    PPM target, using `PhysLayout` GLOBAL indices.  Errors on a malformed layout, an
    uncovered block, an unknown block, an out-of-range logical index, or a local qubit
    with no global image — NEVER a silent identity.  (X+Z on a global qubit ⟹ `Y`.) -/
def layoutPauliRep? (Gamma : TypedEnv) (L : PhysLayout) (P : PPM.MTarget) :
    Except VerificationError QStab.PauliString :=
  if !L.wf then
    .error (.layoutError "physical layout is malformed (duplicate block id or destination)")
  else
    let touched := dedupNat (P.map (fun f => f.1.blk))
    match requireAllCovered Gamma L touched with
    | .error e => .error e
    | .ok _ =>
      match globalPauliContribs Gamma L P touched with
      | .error e     => .error e
      | .ok contribs => .ok (contribsToDense L.size contribs)

/-- Lower a dense physical Pauli to APPLY-gates: `.X`/`.Z` per qubit; for `Y` emit `.X`
    then `.Z` on that qubit (a fixed honest convention — the physical operator is `XZ`,
    i.e. `Y` up to the global phase this stabilizer-level artifact ignores).  `I` ⟹
    nothing.  Iterates qubits ASCENDING, so the artifact order is canonical. -/
def pauliStringToGates (P : QStab.PauliString) : StabilizerProg :=
  (List.range P.length).flatMap (fun g =>
    match P.getD g Physical.Pauli.I with
    | Physical.Pauli.I => ([] : StabilizerProg)
    | Physical.Pauli.X => [StabilizerInstr.X g]
    | Physical.Pauli.Z => [StabilizerInstr.Z g]
    | Physical.Pauli.Y => [StabilizerInstr.X g, StabilizerInstr.Z g])

/-- The expected QStab gates that APPLY a logical Pauli target on the layout-aware
    physical support (`.X`/`.Z`, and `.X;.Z` for `Y`). -/
def expectedPauliGatesQStab (Gamma : TypedEnv) (L : PhysLayout) (target : PPM.MTarget) :
    Except VerificationError StabilizerProg :=
  match layoutPauliRep? Gamma L target with
  | .error e => .error e
  | .ok rep  => .ok (pauliStringToGates rep)

/-- Flatten a STRAIGHT-LINE PPM statement (`seq`/`skip`/`meas` only) into its ordered
    measurement list.  `none` if it contains ANY non-straight-line effect
    (`frame`/`discard`/`ite`/`forLoop`/`abort`) — those carry frame/discard/control
    effects that must NOT be silently erased into a pure measurement artifact. -/
def straightLineMeas? : PPM.Stmt → Option (List (PPM.CVar × PPM.MTarget))
  | .skip      => some []
  | .meas r P  => some [(r, P)]
  | .seq s₁ s₂ =>
    match straightLineMeas? s₁, straightLineMeas? s₂ with
    | some a, some b => some (a ++ b)
    | _, _           => none
  | _          => none

/-- Lower an ordered measurement list to QStab `.bind (.prop none rep)`s, one per logical
    `.meas`, where `rep` is the LAYOUT-AWARE physical representative of the measured
    logical target (each target re-checked by `checkPPM`). -/
def measListToQStab (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout) :
    List (PPM.CVar × PPM.MTarget) → Except VerificationError StabilizerProg
  | []             => .ok []
  | (_, P) :: rest =>
    match checkPPM Gamma caps P with
    | .error e => .error (.typeError e)
    | .ok _ =>
      match layoutPauliRep? Gamma L P with
      | .error e => .error e
      | .ok rep  =>
        match measListToQStab Gamma caps L rest with
        | .error e => .error e
        | .ok more => .ok (StabilizerInstr.bind (.prop none rep) :: more)

/-- The expected QStab lowering of a (straight-line) PPM fragment: one physical
    measurement per logical `.meas`.  A non-straight-line fragment is `unsupportedMixed`
    (its frame/discard/control effects are NOT a pure QStab measurement list, and are
    NOT silently dropped). -/
def expectedPPMFragmentQStab (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (stmt : PPM.Stmt) : Except VerificationError StabilizerProg :=
  match straightLineMeas? stmt with
  | none    => .error (.unsupportedMixed
      "PPM fragment contains frame/discard/ite/forLoop/abort — non-QStab effects are not lowerable to a pure measurement artifact")
  | some ms => measListToQStab Gamma caps L ms

/-- The expected QStab lowering of a DIRECT transversal single-qubit gate on block `b`:
    `.H` (for `hGate2x2`) or `.S` (for `sGate2x2`) on EVERY physical qubit of `b`, via the
    layout.  Requires the layout to COMPLETELY COVER `b` (`requireLayoutCoversBlock`); any
    gate other than H/S is unsupported. -/
def expectedTransversalQStab (Gamma : TypedEnv) (L : PhysLayout) (b : Nat)
    (g : ChainQ.GF2.BoolMat) : Except VerificationError StabilizerProg := do
  requireLayoutCoversBlock Gamma L b
  match L.blockQubits? b with
  | none    => .error (.layoutError s!"layout has no placement for block {b}")
  | some qs =>
    if decide (g = hGate2x2) then
      .ok (qs.map (fun q => StabilizerInstr.H q))
    else if decide (g = sGate2x2) then
      .ok (qs.map (fun q => StabilizerInstr.S q))
    else
      .error (.unsupportedMixed "direct transversal lowering supports only the H and S gates")

/-- The expected QStab lowering of a transversal logical CNOT: a physical `.CNOT` from
    control physical qubit `i` to target physical qubit `j` for every `incidence[i][j]`,
    addressed through the layout (row-major over the incidence).  Requires the layout to
    COMPLETELY COVER BOTH the control and target blocks (`requireLayoutCoversBlock`) — so a
    partial layout that only maps the incidence-touched qubits is rejected, not silently
    accepted because the artifact happens to cover the touched gates. -/
def expectedCNOTQStab (Gamma : TypedEnv) (cBlk tBlk : Nat) (incidence : ChainQ.GF2.BoolMat)
    (L : PhysLayout) : Except VerificationError StabilizerProg := do
  requireLayoutCoversBlock Gamma L cBlk
  requireLayoutCoversBlock Gamma L tBlk
  cnotEntriesToQStab cBlk tBlk L (cnotTrueEntries incidence)

/-- Lower ONE direct-fragment Mixed instruction to its expected QStab program, GIVEN it
    has already been type-checked in `Gamma` (NO `checkInstr` here — the single-instruction
    and program verifiers run the checker themselves, the latter while threading state).
    Coverage of every involved block is required; unsupported instructions are an explicit
    `unsupportedMixed`. -/
def directMixedQStabLowering (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout) :
    MixedInstr → Except VerificationError StabilizerProg
  | .transversal b g        => expectedTransversalQStab Gamma L b g
  | .transversalCNOT s      => expectedCNOTQStab Gamma s.control.blk s.target.blk s.incidence L
  | .transversalCNOTBatch s => expectedCNOTQStab Gamma s.controlBlock s.targetBlock s.incidence L
  | .pauli q p              => expectedPauliGatesQStab Gamma L [(q, p)]
  | .ppm stmt               => expectedPPMFragmentQStab Gamma caps L stmt
  | .automorphism _ _ => .error (.unsupportedMixed
      "automorphism has no canonical structural lowering; use verifyAutomorphismQStab (semantic induced-map comparison) for single-instruction verification")
  | .switch _ _ _     => .error (.unsupportedMixed
      "code-switch → QStab deferred: needs the homomorphic-CNOT bridge incidence, teleportation/gauge-fix measurements, outcome-driven frame corrections, the C→D layout transition + post-switch env/layout, and the intermediate merged stabilizers (checkSwitch certifies only the symplectic coercion f)")
  | .magic _          => .error (.unsupportedMixed "magic obligation has no QStab lowering")

/-- Run the Mixed checker on `instr` (from the initial PPM state) and compute the expected
    QStab lowering for the supported fragment (transversal / CNOT / pauli / straight-line
    PPM). -/
def expectedDirectMixedQStab (Gamma : TypedEnv) (caps : List Capability)
    (L : PhysLayout) (instr : MixedInstr) : Except VerificationError StabilizerProg := do
  let _ ← liftType (checkInstr caps Gamma PPMState.init instr)
  directMixedQStabLowering Gamma caps L instr

/-- **The MixedIR → QStab verifier (direct transversal fragment).**  (1) requires a
    well-formed layout; (2) runs the existing Mixed checker and computes the expected
    QStab lowering of the typed instruction; (3) requires structural equality with the
    supplied artifact; (4) runs `verifyStabilizerProgram` on it.  A reversed / missing /
    extra physical gate fails step (3); an illegal logical instruction (e.g. transversal
    H on a Z-type code, or a fan-out incidence) fails step (2) and is NEVER salvaged by
    the artifact comparison. -/
def verifyDirectMixedInstrQStab (Gamma : TypedEnv) (caps : List Capability)
    (layout : PhysLayout) (instr : MixedInstr) (artifact : StabilizerProg)
    (spec : QStabVerificationSpec := {}) : Except VerificationError Unit :=
  if !layout.wf then
    .error (.layoutError "physical layout is malformed (duplicate block id or destination)")
  else
    match expectedDirectMixedQStab Gamma caps layout instr with
    | .error e     => .error e
    | .ok expected =>
      if !sameStabilizerProg artifact expected then
        .error (.certFailed "QStab artifact does not match the expected direct-fragment lowering")
      else
        liftType (verifyStabilizerProgram artifact spec)

/-! ## Program-level MixedIR → QStab verification (the next milestone).

    A MixedIR PROGRAM lowers to the CONCATENATION of its instructions' QStab programs.
    This verifier THREADS the `TypedEnv` + `PPMState` across the list (so cross-instruction
    resource discipline — a discard, a switch's new env — is enforced by `checkInstr` from
    the threaded state, exactly as `checkLogicalExecAux` does), lowers each instruction
    against the env in force AT that instruction, and concatenates.  Direct fragment only;
    an unsupported instruction anywhere is an explicit `unsupportedMixed`. -/

/-- Thread `TypedEnv`/`PPMState` across a Mixed program, type-checking each instruction
    from the threaded state and concatenating the per-instruction QStab lowerings. -/
def expectedDirectMixedProgQStab (caps : List Capability) (L : PhysLayout) :
    TypedEnv → PPMState → LogicalExec → Except VerificationError StabilizerProg
  | _,     _,  []           => .ok []
  | Gamma, st, instr :: rest =>
    match checkInstr caps Gamma st instr with
    | .error e          => .error (.typeError e)
    | .ok (Gamma', st') =>
      match directMixedQStabLowering Gamma caps L instr with
      | .error e   => .error e
      | .ok prog   =>
        match expectedDirectMixedProgQStab caps L Gamma' st' rest with
        | .error e     => .error e
        | .ok progRest => .ok (prog ++ progRest)

/-- **The program-level MixedIR → QStab verifier.**  (1) requires a well-formed layout;
    (2) threads `TypedEnv`/`PPMState` across the program, computing the CONCATENATED
    expected QStab lowering instruction by instruction; (3) requires structural equality
    with the supplied (concatenated) artifact; (4) runs `verifyStabilizerProgram`.  A
    reordered / missing / extra physical gate ANYWHERE fails step (3); an illegal
    instruction fails step (2); an unsupported instruction is `unsupportedMixed`. -/
def verifyDirectMixedProgQStab (Gamma : TypedEnv) (caps : List Capability)
    (layout : PhysLayout) (prog : LogicalExec) (artifact : StabilizerProg)
    (spec : QStabVerificationSpec := {}) : Except VerificationError Unit :=
  if !layout.wf then
    .error (.layoutError "physical layout is malformed (duplicate block id or destination)")
  else
    match expectedDirectMixedProgQStab caps layout Gamma PPMState.init prog with
    | .error e     => .error e
    | .ok expected =>
      if !sameStabilizerProg artifact expected then
        .error (.certFailed "QStab artifact does not match the expected direct-fragment program lowering")
      else
        liftType (verifyStabilizerProgram artifact spec)

/-! ## Standalone layout-aware PPM verifiers. -/

/-- **The LAYOUT-AWARE PPM measurement verifier.**  Type-checks the logical PPM `target`,
    then requires the supplied QStab artifact to measure EXACTLY the layout-aware physical
    representative (a `.prop` of `layoutPauliRep?` over global indices, read out by a
    `.parity [0]`).  This is the form the MixedIR verifier uses — a compact-ordered
    artifact that would pass the old `verifyPPMMeasurementQStab` is rejected here when the
    layout places the support at different global qubits. -/
def verifyPPMMeasurementQStabLayout (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (sched : Option Sched) (target : PPM.MTarget) (artifact : StabilizerProg)
    (spec : QStabVerificationSpec := { readouts := [{ var := 1, expectedNoiseless := false }] }) :
    Except VerificationError Unit :=
  match liftType (checkPPM Gamma caps target) with
  | .error e => .error e
  | .ok _ =>
    match layoutPauliRep? Gamma L target with
    | .error e => .error e
    | .ok rep =>
      let expected : StabilizerProg := [.bind (.prop sched rep), .bind (.parity [0])]
      if !sameStabilizerProg artifact expected then
        .error (.certFailed "QStab artifact does not measure the layout-aware physical representative of the PPM target")
      else
        liftType (verifyStabilizerProgram artifact spec)

/-- **The straight-line PPM-fragment verifier (item 4).**  Runs the existing Mixed/PPM
    checker (`checkInstr (.ppm stmt)`), computes the straight-line measurement lowering
    (one layout-aware `.prop` per `.meas`; `frame`/`discard`/`ite`/`forLoop`/`abort` are
    explicit `unsupportedMixed`, NOT silently erased), requires structural equality, and
    runs `verifyStabilizerProgram`. -/
def verifyPPMFragmentQStab (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (stmt : PPM.Stmt) (artifact : StabilizerProg) (spec : QStabVerificationSpec := {}) :
    Except VerificationError Unit :=
  if !L.wf then
    .error (.layoutError "physical layout is malformed (duplicate block id or destination)")
  else
    match liftType (checkInstr caps Gamma PPMState.init (.ppm stmt)) with
    | .error e => .error e
    | .ok _ =>
      match expectedPPMFragmentQStab Gamma caps L stmt with
      | .error e     => .error e
      | .ok expected =>
        if !sameStabilizerProg artifact expected then
          .error (.certFailed "QStab artifact does not match the straight-line PPM fragment's measurement lowering")
        else
          liftType (verifyStabilizerProgram artifact spec)

/-! ## Milestone B — a symplectic Clifford simulator for the QStab Clifford subset.

    To verify `.automorphism` / general `.transversal` we cannot use canonical structural
    equality (many physical gate sequences realise the same logical Clifford).  Instead we
    SIMULATE the artifact in the Heisenberg picture: apply its conjugation action to each
    basis Pauli of the block and read off the induced `2n×2n` symplectic matrix (in the
    `[X-half | Z-half]` convention — row `k` = image of the `k`-th basis Pauli, matching
    `Internal.transversalMap`).  Supported gates: `.H` `.S` `.CNOT` `.CZ` (genuine
    symplectic action) and `.X` `.Z` (phase-only ⟹ symplectic IDENTITY, but still required
    to be IN the block layout).  `.bind`/`.prepZero`/`.prepPlus`/`.ifPauli` are rejected —
    they are NOT pure-Clifford automorphism gates and are not modeled.  Phase is ignored
    (exactly the symplectic level `checkLogicalAutomorphism`/`checkTransversal` certify). -/

/-- The LOCAL physical-qubit index (within block `b`) of a GLOBAL QStab qubit `g`, or
    `none` if `g` is not in `b`'s layout placement. -/
def PhysLayout.localOf? (L : PhysLayout) (b g : Nat) : Option Nat :=
  match L.find? b with
  | none             => none
  | some (base, cnt) => if decide (base ≤ g) && decide (g < base + cnt) then some (g - base) else none

/-- The `k`-th unit Pauli vector of width `m` (a single `1` at position `k`). -/
def unitVec (m k : Nat) : ChainQ.GF2.BoolVec := (List.range m).map (fun j => decide (j = k))

/-- `H` on local qubit `i`: swap `X_i ↔ Z_i` (positions `i` and `n+i`). -/
def hSym (n i : Nat) (v : ChainQ.GF2.BoolVec) : ChainQ.GF2.BoolVec :=
  (List.range v.length).map (fun j =>
    if j == i then v.getD (n + i) false
    else if j == n + i then v.getD i false
    else v.getD j false)

/-- `S` on local qubit `i`: `Z_i ← Z_i ⊕ X_i` (the `z`-bit at `n+i` XORs in the `x`-bit at `i`). -/
def sSym (n i : Nat) (v : ChainQ.GF2.BoolVec) : ChainQ.GF2.BoolVec :=
  (List.range v.length).map (fun j =>
    if j == n + i then xor (v.getD (n + i) false) (v.getD i false) else v.getD j false)

/-- `CNOT` control `c`, target `t` (local): `x_t ⊕= x_c` and `z_c ⊕= z_t`. -/
def cnotSym (n c t : Nat) (v : ChainQ.GF2.BoolVec) : ChainQ.GF2.BoolVec :=
  (List.range v.length).map (fun j =>
    if j == t then xor (v.getD t false) (v.getD c false)
    else if j == n + c then xor (v.getD (n + c) false) (v.getD (n + t) false)
    else v.getD j false)

/-- `CZ` on local `a`, `c` (symmetric): `z_c ⊕= x_a` and `z_a ⊕= x_c`. -/
def czSym (n a c : Nat) (v : ChainQ.GF2.BoolVec) : ChainQ.GF2.BoolVec :=
  (List.range v.length).map (fun j =>
    if j == n + c then xor (v.getD (n + c) false) (v.getD a false)
    else if j == n + a then xor (v.getD (n + a) false) (v.getD c false)
    else v.getD j false)

/-- The conjugation action of ONE QStab gate on a Pauli vector `v` (local, width `2n`),
    resolving global qubits to block-`b` local indices via the layout.  A gate outside the
    block layout, or a non-Clifford-automorphism instruction, is an explicit error. -/
def applyQStabGateSym (L : PhysLayout) (b n : Nat) (v : ChainQ.GF2.BoolVec) :
    StabilizerInstr → Except VerificationError ChainQ.GF2.BoolVec
  | .H g => match L.localOf? b g with
            | some i => .ok (hSym n i v)
            | none   => .error (.layoutError "QStab gate addresses a qubit outside the target block's layout")
  | .S g => match L.localOf? b g with
            | some i => .ok (sSym n i v)
            | none   => .error (.layoutError "QStab gate addresses a qubit outside the target block's layout")
  | .X g => match L.localOf? b g with
            | some _ => .ok v        -- phase-only ⟹ symplectic identity (but must be in-block)
            | none   => .error (.layoutError "QStab .X addresses a qubit outside the target block's layout")
  | .Z g => match L.localOf? b g with
            | some _ => .ok v
            | none   => .error (.layoutError "QStab .Z addresses a qubit outside the target block's layout")
  | .CNOT c t => match L.localOf? b c, L.localOf? b t with
                 | some ci, some ti => .ok (cnotSym n ci ti v)
                 | _, _ => .error (.layoutError "QStab .CNOT addresses a qubit outside the target block's layout")
  | .CZ a c   => match L.localOf? b a, L.localOf? b c with
                 | some ai, some ci => .ok (czSym n ai ci v)
                 | _, _ => .error (.layoutError "QStab .CZ addresses a qubit outside the target block's layout")
  | .bind _        => .error (.unsupportedMixed "QStab .bind (measurement) is not a Clifford-automorphism gate")
  | .prepZero _    => .error (.unsupportedMixed "QStab .prepZero is not modeled by the Clifford-automorphism simulator")
  | .prepPlus _    => .error (.unsupportedMixed "QStab .prepPlus is not modeled by the Clifford-automorphism simulator")
  | .ifPauli _ _ _ => .error (.unsupportedMixed "QStab .ifPauli (feed-forward) is not modeled by the Clifford-automorphism simulator")

/-- Apply a whole QStab program's conjugation action to a Pauli vector (gate by gate). -/
def applyQStabProgSym (L : PhysLayout) (b n : Nat) :
    StabilizerProg → ChainQ.GF2.BoolVec → Except VerificationError ChainQ.GF2.BoolVec
  | [],        v => .ok v
  | g :: rest, v =>
    match applyQStabGateSym L b n v g with
    | .error e => .error e
    | .ok v'   => applyQStabProgSym L b n rest v'

/-- The rows of the induced symplectic matrix: row `k` = image of basis Pauli `e_k`. -/
def cliffordRows (L : PhysLayout) (b n : Nat) (prog : StabilizerProg) :
    List Nat → Except VerificationError ChainQ.GF2.BoolMat
  | []      => .ok []
  | k :: ks =>
    match applyQStabProgSym L b n prog (unitVec (2 * n) k) with
    | .error e => .error e
    | .ok row =>
      match cliffordRows L b n prog ks with
      | .error e => .error e
      | .ok rows => .ok (row :: rows)

/-- **`qstabCliffordMap?`** — the induced `2n×2n` symplectic matrix of a QStab Clifford
    artifact on block `b`, addressed through the layout.  Rejects a malformed layout,
    missing layout coverage of `b`, an unknown block, a gate outside `b`'s layout, or any
    unsupported (measurement/prep/feed-forward) instruction. -/
def qstabCliffordMap? (Gamma : TypedEnv) (L : PhysLayout) (b : Nat) (prog : StabilizerProg) :
    Except VerificationError ChainQ.GF2.BoolMat :=
  if !L.wf then .error (.layoutError "physical layout is malformed (duplicate block id or destination)")
  else match requireLayoutCoversBlock Gamma L b with
  | .error e => .error e
  | .ok _ =>
    match Gamma.block? b with
    | none    => .error (.typeError (.badBlock b))
    | some tb => cliffordRows L b tb.block.n prog (List.range (2 * tb.block.n))

/-- The verification status / STRENGTH of a Mixed instruction's QStab check.  (The task's
    "deferredUnsupported" is `deferred`.)  Every "Verified" level is at the STABILIZER
    (phase-quotient) level — NONE claims a global phase. -/
inductive VStatus
  | exactVerified                   -- artifact = the exact expected operator, NO Pauli-frame slack
  | symplecticVerified              -- correct symplectic map, modulo an IGNORED Pauli frame (`.X`/`.Z`)
  | logicalModuloStabilizerVerified -- correct induced LOGICAL action on `lx`/`lz`, modulo stabilizers
  | partiallyVerified               -- only a sub-fragment is concretely verified (straight-line PPM)
  | structurallyCheckedOnly         -- a type/cert/addressing checker exists, but NO QStab artifact semantics
  | deferred                        -- no concrete QStab verifier
  deriving DecidableEq, Repr

/-- How strictly to verify a Clifford artifact against an expected symplectic map. -/
inductive CliffordCheck
  | exact          -- reject Pauli-frame gates (`.X`/`.Z`); require induced map = expected EXACTLY
  | symplectic     -- allow `.X`/`.Z` as phase/frame-ignored identity; require induced map = expected
  | logicalModStab -- allow `.X`/`.Z`; require induced LOGICAL action (on `lx`/`lz`) = expected mod stabilizers
  deriving DecidableEq, Repr

/-- The status a successful check establishes in each mode. -/
def cliffordCheckStatus : CliffordCheck → VStatus
  | .exact          => .exactVerified
  | .symplectic     => .symplecticVerified
  | .logicalModStab => .logicalModuloStabilizerVerified

/-- Does the program contain a Pauli-frame gate (`.X`/`.Z`)? -/
def progHasPauliFrame : StabilizerProg → Bool
  | []        => false
  | .X _ :: _ => true
  | .Z _ :: _ => true
  | _ :: rest => progHasPauliFrame rest

/-- Does `M` PRESERVE the block's stabilizer group — map every stabilizer back INTO the
    code (the codespace-preservation condition `checkLogicalAutomorphism` itself requires)?
    Without this, an operation that sends a stabilizer OUTSIDE the code could be "verified"
    in `logicalModStab` mode merely because it fixes the chosen `lx`/`lz` representatives. -/
def preservesBlockStab (blk : Block) (M : ChainQ.GF2.BoolMat) : Bool :=
  (applyMap blk.n M blk.stab).all (fun r => ChainQ.GF2.inSpan blk.stab r)

/-- Compare the artifact's induced action on block `b` to an EXPECTED `2n×2n` map, in the
    requested `mode`, returning the achieved `VStatus` on success.
    * SOUNDNESS (audit fix): in EVERY mode the artifact-induced map (and the `expected`
      map) must PRESERVE THE STABILIZER GROUP (`preservesBlockStab`) — otherwise the
      codespace is not preserved and nothing is verified.
    * `exact` additionally REJECTS Pauli-frame gates (`.X`/`.Z`) — so `[.H 0, .X 0]` is
      `symplecticVerified` but NOT `exactVerified` (the audit's distinction).
    * `symplectic` allows `.X`/`.Z` (phase/frame ignored) and requires `induced = expected`.
    * `logicalModStab` compares the induced LOGICAL action on `lx`/`lz` MODULO stabilizers —
      more permissive (accepts artifacts differing from `expected` by stabilizer redundancy),
      the right "QEC logical correctness" notion — but only AFTER stabilizer preservation. -/
def verifyCliffordMapQStab (Gamma : TypedEnv) (L : PhysLayout) (b : Nat) (mode : CliffordCheck)
    (expected : ChainQ.GF2.BoolMat) (artifact : StabilizerProg) :
    Except VerificationError VStatus :=
  if decide (mode = .exact) && progHasPauliFrame artifact then
    .error (.unsupportedMixed "exact mode: artifact contains a Pauli-frame .X/.Z gate (use .pauli for a frame, or symplectic mode)")
  else
    match qstabCliffordMap? Gamma L b artifact with
    | .error e => .error e
    | .ok induced =>
      match Gamma.block? b with
      | none => .error (.typeError (.badBlock b))
      | some tb =>
        let blk := tb.block
        -- SOUNDNESS GATE (P0 audit fix): the artifact's induced map — AND the claimed
        -- `expected` map — must preserve the stabilizer group (codespace), in EVERY mode,
        -- before any status is returned.  This rules out, e.g., a physical `.S` on an
        -- unmeasured qubit that fixes `lx`/`lz` mod stab but takes a stabilizer outside
        -- the code.  (`induced` is symplectic by construction; this is the missing check.)
        if !preservesBlockStab blk induced then
          .error (.certFailed "QStab artifact's induced map does not preserve the stabilizer group (codespace not preserved)")
        else if !preservesBlockStab blk expected then
          .error (.certFailed "the expected map does not preserve the stabilizer group (not a valid logical operation)")
        else
          match mode with
          | .logicalModStab =>
            if Internal.rowsEqualModStab blk.stab (applyMap blk.n induced blk.lx) (applyMap blk.n expected blk.lx)
                && Internal.rowsEqualModStab blk.stab (applyMap blk.n induced blk.lz) (applyMap blk.n expected blk.lz) then
              .ok .logicalModuloStabilizerVerified
            else .error (.certFailed "artifact's induced LOGICAL action (on lx/lz) ≠ expected, modulo stabilizers")
          | _ =>
            if decide (induced = expected) then .ok (cliffordCheckStatus mode)
            else .error (.certFailed "QStab artifact's induced symplectic map does not equal the expected map")

/-- **Milestone C — verify `.automorphism b M`.**  Type-check via `checkInstr`
    (`checkLogicalAutomorphism`), then require the artifact's induced symplectic map to
    EQUAL `M` exactly.  A shape-invalid / non-symplectic / stabilizer-breaking `M` is
    rejected by the CHECKER, never rescued by a matching artifact. -/
def verifyAutomorphismQStab (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (b : Nat) (M : ChainQ.GF2.BoolMat) (artifact : StabilizerProg)
    (mode : CliffordCheck := .symplectic) : Except VerificationError VStatus :=
  match liftType (checkInstr caps Gamma PPMState.init (.automorphism b M)) with
  | .error e => .error e
  | .ok _ => verifyCliffordMapQStab Gamma L b mode M artifact

/-- **Milestone D — verify a GENERAL `.transversal b g`** (any valid single-qubit
    symplectic `g`, not only H/S) by the SEMANTIC route: type-check via `checkTransversal`,
    then check the artifact's induced map against `Internal.transversalMap n g` (the tensor
    power `g^{⊗n}` the checker certifies as a code automorphism), in the requested `mode`. -/
def verifyTransversalMapQStab (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (b : Nat) (g : ChainQ.GF2.BoolMat) (artifact : StabilizerProg)
    (mode : CliffordCheck := .symplectic) : Except VerificationError VStatus :=
  match liftType (checkInstr caps Gamma PPMState.init (.transversal b g)) with
  | .error e => .error e
  | .ok _ =>
    match Gamma.block? b with
    | none    => .error (.typeError (.badBlock b))
    | some tb => verifyCliffordMapQStab Gamma L b mode (Internal.transversalMap tb.block.n g) artifact

/-! ## Milestone 3 — program-composable SEMANTIC verification via explicit chunks.

    The semantic verifier is single-instruction (a non-canonical artifact can't be sliced
    out of a flat concatenation).  A `MixedQStabChunk` pairs ONE `MixedInstr` with the
    QStab slice that realises it — the chunk boundaries ARE the slicing witness.  The
    chunked verifier threads `TypedEnv`/`PPMState`, verifies each chunk (structural for
    H/S/CNOT/pauli/straight-PPM, SEMANTIC for automorphism/general transversal), and
    requires the concatenation of chunk slices to equal the supplied full artifact. -/

/-- One instruction paired with the QStab slice claimed to realise it. -/
structure MixedQStabChunk where
  instr    : MixedInstr
  artifact : StabilizerProg
  deriving Repr

/-- Verify that ONE chunk's artifact realises its instruction (given it already
    type-checked in `Gamma`): semantic map-check for automorphism / transversal, structural
    canonical-equality for everything else (`switch`/`magic` ⇒ `unsupportedMixed`).
    PRIVATE (P1 audit fix): this assumes its instruction was ALREADY type-checked, so it is
    only sound through `verifyChunkedMixedProgQStab`; do not call it directly. -/
private def verifyChunkArtifact (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (mode : CliffordCheck) : MixedInstr → StabilizerProg → Except VerificationError Unit
  | .automorphism b M, art =>
      match verifyCliffordMapQStab Gamma L b mode M art with
      | .error e => .error e | .ok _ => .ok ()
  | .transversal b g, art =>
      match Gamma.block? b with
      | none => .error (.typeError (.badBlock b))
      | some tb =>
        match verifyCliffordMapQStab Gamma L b mode (Internal.transversalMap tb.block.n g) art with
        | .error e => .error e | .ok _ => .ok ()
  | other, art =>
      match directMixedQStabLowering Gamma caps L other with
      | .error e => .error e
      | .ok expected =>
        if sameStabilizerProg art expected then .ok ()
        else .error (.certFailed "chunk artifact does not match the structural lowering of its instruction")

/-- Thread the env/state across chunks, verify each chunk, and return the concatenated
    chunk artifacts.  PRIVATE: type-checks each chunk (`checkInstr`) BEFORE the (private)
    `verifyChunkArtifact`, so the unsafe helper is only ever reached after type-checking. -/
private def verifyChunkedAux (caps : List Capability) (L : PhysLayout) (mode : CliffordCheck) :
    TypedEnv → PPMState → List MixedQStabChunk → Except VerificationError StabilizerProg
  | _,     _,  []           => .ok []
  | Gamma, st, chunk :: rest =>
    match checkInstr caps Gamma st chunk.instr with
    | .error e => .error (.typeError e)
    | .ok (Gamma', st') =>
      match verifyChunkArtifact Gamma caps L mode chunk.instr chunk.artifact with
      | .error e => .error e
      | .ok _ =>
        match verifyChunkedAux caps L mode Gamma' st' rest with
        | .error e => .error e
        | .ok more => .ok (chunk.artifact ++ more)

/-- **The chunked program verifier.**  Requires a well-formed layout; verifies every chunk
    (threading env/state); requires the supplied full artifact to EQUAL the concatenation
    of the chunk slices; then runs `verifyStabilizerProgram`. -/
def verifyChunkedMixedProgQStab (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (chunks : List MixedQStabChunk) (fullArtifact : StabilizerProg)
    (mode : CliffordCheck := .symplectic) (spec : QStabVerificationSpec := {}) :
    Except VerificationError Unit :=
  if !L.wf then .error (.layoutError "physical layout is malformed (duplicate block id or destination)")
  else
    match verifyChunkedAux caps L mode Gamma PPMState.init chunks with
    | .error e => .error e
    | .ok concatenated =>
      if sameStabilizerProg fullArtifact concatenated then
        liftType (verifyStabilizerProgram fullArtifact spec)
      else .error (.certFailed "the supplied full QStab artifact ≠ the concatenation of the chunk artifacts")

/-! ## Milestone 5 — `.switch` verification SPEC (documented, deliberately NOT implemented).

    `checkSwitch` certifies ONLY the symplectic coercion `f`.  A sound QStab verifier needs
    the witnesses below; `verifySwitchQStab` records the spec but ALWAYS defers (an empty
    artifact would verify only ideal env coercion — rejected). -/

/-- The witnesses a future `.switch` QStab verifier must check. -/
structure SwitchVerificationSpec where
  preEnv          : TypedEnv := ⟨[]⟩                -- the env BEFORE the switch (code C)
  postEnv         : TypedEnv := ⟨[]⟩                -- the env AFTER the switch (code D)
  preLayout       : PhysLayout := { placements := [] }   -- C-patch physical layout
  postLayout      : PhysLayout := { placements := [] }   -- D-patch physical layout (the C→D transition)
  cert?           : Option SwitchCert := none      -- the symplectic coercion f (checkSwitch-validated)
  bridgeIncidence : ChainQ.GF2.BoolMat := []       -- homomorphic-CNOT bridge (C-patch ↔ D-patch)
  switchMeas      : StabilizerProg := []           -- teleportation / gauge-fix measurements
  frameCorr       : StabilizerProg := []           -- outcome-driven frame corrections
  mergedStab      : List QStab.PauliString := []   -- intermediate / merged stabilizers measured

/-- Code-switch QStab verification — DEFERRED.  Always returns `unsupportedMixed` (the
    symplectic coercion is the only checkable part today, via `checkSwitch`).  An empty
    artifact would verify ONLY ideal env coercion, so it is rejected here too. -/
def verifySwitchQStab (_spec : SwitchVerificationSpec) (_artifact : StabilizerProg) :
    Except VerificationError Unit :=
  .error (.unsupportedMixed
    "code-switch QStab verification is NOT implemented: a sound verifier must check the homomorphic-CNOT bridge incidence, the teleportation/gauge-fix measurement artifact, the outcome-driven frame corrections, the C→D layout transition + post-switch env/layout, and the intermediate/merged stabilizer witness against the SwitchVerificationSpec (checkSwitch certifies ONLY the symplectic coercion f); an empty artifact would verify only ideal env coercion")

/-! ## §V. Coverage / status of MixedIR → QStab verification.

    THREE verifier families (all phase-quotient / stabilizer-level):
      * STRUCTURAL (`verifyDirectMixedInstrQStab` / `verifyDirectMixedProgQStab`, status =
        `mixedInstrStatus`): artifact = a CANONICAL expected QStab program (`exactVerified`,
        no Pauli-frame slack).  Program-composable.
      * SEMANTIC induced-map (`verifyAutomorphismQStab` / `verifyTransversalMapQStab` via
        `qstabCliffordMap?`, status = `mixedInstrSemanticStatus mode`): compares the
        artifact's induced `2n×2n` map.  Mode `CliffordCheck` selects the strength —
        `exact` (no `.X`/`.Z`) ⇒ `exactVerified`; `symplectic` (`.X`/`.Z` ignored) ⇒
        `symplecticVerified`; `logicalModStab` (action on `lx`/`lz` mod stabilizers) ⇒
        `logicalModuloStabilizerVerified` (the QEC-correct, most permissive level).
      * CHUNKED (`verifyChunkedMixedProgQStab`): makes the SEMANTIC family
        program-composable via explicit `MixedQStabChunk` slice witnesses.

    | `MixedInstr`                | family            | strongest status (mode)            |
    |-----------------------------|-------------------|------------------------------------|
    | `.transversal b (H/S)`      | structural        | exactVerified                      |
    | `.transversal b (any g)`    | semantic/chunked  | exact / symplectic / logicalModStab|
    | `.transversalCNOT`/`Batch`  | structural        | exactVerified                      |
    | `.pauli q p`                | structural        | exactVerified                      |
    | `.ppm` (straight-line)      | structural        | partiallyVerified                  |
    | `.ppm` (frame/discard/ctrl) | —                 | deferred                           |
    | `.automorphism b M`         | semantic/chunked  | exact / symplectic / logicalModStab|
    | `.switch`                   | spec only         | structurallyCheckedOnly            |
    | `.magic`                    | —                 | deferred                           |

    HONEST scope: every concrete claim is at the SYMPLECTIC (Heisenberg, phase-ignored)
    level — exactly the level `checkLogicalAutomorphism`/`checkTransversal`/`checkPPM`
    certify.  A trailing Pauli `.X`/`.Z` is a harmless frame correction.  Physical channel
    / fault tolerance remain the deferred boundary (CONTRACT §3).

    NOT a `MixedInstr` (deferred at the MixPrim/protocol layer, structurally-checked only):
    parallel-PPM / QGPU (parallel product surgery), batched code-switch (transpose
    routing), GPPM / external chain certs — `checkQGPURound?` / `checkBatchedCodeSwitch?` /
    `ExternalClaim` validate addressing/routing/cert shape but NEVER a QStab artifact.

    ### §V·F. `.switch` verification — DESIGN (deliberately NOT implemented).

    `checkSwitch` verifies ONLY the symplectic coercion `f` (f(S_C) ⊆ S_D and f preserves
    the logicals mod S_D).  A sound QStab artifact verifier for `.switch` needs witnesses
    we do not yet have, so `.switch` returns an explicit `unsupportedMixed` naming them:
      * an EMPTY artifact would verify ONLY the ideal ENV COERCION (the typed env changes
        C→D), NOT any physical code-switch — accepting `[]` would be a cheat;
      * a NONEMPTY artifact needs (1) the homomorphic-CNOT BRIDGE incidence between the
        C-patch and D-patch (a `transversalCNOT`-style certificate), (2) the
        teleportation / gauge-fixing MEASUREMENTS (a QStab `.prop` list), (3) the
        outcome-driven FRAME corrections, (4) the LAYOUT TRANSITION (C→D physical-qubit
        remap) + post-switch env/layout, and (5) the intermediate/merged stabilizers
        measured during the switch.
    None of these are accepted by erasing the channel. -/

-- (`VStatus` and `CliffordCheck` are defined above, before the verifiers that return them.)

/-- Status in the STRUCTURAL (canonical-artifact, program-composable) verifier.  PRECISE:
    only H/S transversals have a canonical structural lowering, so other `g` is `deferred`
    here (and concretely verified instead by the SEMANTIC verifier — see
    `mixedInstrSemanticStatus`). -/
def mixedInstrStatus : MixedInstr → VStatus
  | .transversal _ g =>
      if decide (g = hGate2x2) || decide (g = sGate2x2) then .exactVerified
      else .deferred
  | .transversalCNOT _      => .exactVerified
  | .transversalCNOTBatch _ => .exactVerified
  | .pauli _ _              => .exactVerified
  | .ppm stmt               => match straightLineMeas? stmt with
                               | some _ => .partiallyVerified
                               | none   => .deferred
  | .automorphism _ _       => .deferred             -- no canonical structural artifact (see SEMANTIC verifier)
  | .switch _ _ _           => .structurallyCheckedOnly  -- checkSwitch is symplectic-only
  | .magic _                => .deferred

/-- Status in the SEMANTIC verifier (`verifyCliffordMapQStab`, also via the chunked program
    verifier): a pure-Clifford `.automorphism` or ANY valid-symplectic `.transversal` is
    verified by comparing induced maps.  The achieved status is the chosen `mode`'s status
    (`cliffordCheckStatus`) — context-aware, so we never claim a mode that was not run. -/
def mixedInstrSemanticStatus (mode : CliffordCheck) : MixedInstr → VStatus
  | .transversal _ _  => cliffordCheckStatus mode
  | .automorphism _ _ => cliffordCheckStatus mode
  | _                 => .deferred

/-! ### Examples / regression tests for the direct MixedIR→QStab verifier. -/

/-- A two-bare-qubit env (blocks 0 and 1) for the inter-block CNOT examples. -/
def tenv2Q : TypedEnv := ⟨[⟨q0, by decide⟩, ⟨q0, by decide⟩]⟩

def bareLayout1 : PhysLayout := { placements := [(0, 0, 1)] }                  -- block 0 → phys 0
def repLayout   : PhysLayout := { placements := [(0, 0, 3)] }                  -- block 0 → phys 0,1,2
def twoLayout   : PhysLayout := { placements := [(0, 0, 1), (1, 1, 1)] }       -- block 0 → 0, block 1 → 1
def qrLayout    : PhysLayout := { placements := [(0, 0, 1), (1, 1, 3)] }       -- block 0 → 0, block 1 → 1,2,3

-- (1) bare-qubit transversal H accepts exactly `[.H 0]`:
example : ok? (verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.transversal 0 hGate2x2) [.H 0]) = true := by decide
-- (2) it rejects the EMPTY artifact and a wrong-gate `[.S 0]`:
example : ok? (verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.transversal 0 hGate2x2) []) = false := by decide
example : ok? (verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.transversal 0 hGate2x2) [.S 0]) = false := by decide
-- transversal S accepts `[.S 0]` (the S lowering):
example : ok? (verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.transversal 0 sGate2x2) [.S 0]) = true := by decide

-- (3) repetition-code transversal H is rejected by the TYPE CHECKER (H maps the Z-type
-- stabilizers to X-type, outside the code), so even an artifact full of physical H gates
-- is rejected — the type system gates it, not the artifact comparison:
example : ok? (checkTransversal tenvR 0 hGate2x2) = false := by decide
example : ok? (verifyDirectMixedInstrQStab tenvR [] repLayout (.transversal 0 hGate2x2) [.H 0, .H 1, .H 2]) = false := by decide

-- (4) bare two-block logical CNOT accepts exactly `[.CNOT 0 1]`:
def cnotSpec2 : TransversalCNOTSpec := { control := ⟨0, 0⟩, target := ⟨1, 0⟩, incidence := [[true]] }
example : ok? (verifyDirectMixedInstrQStab tenv2Q [] twoLayout (.transversalCNOT cnotSpec2) [.CNOT 0 1]) = true := by decide
-- (5) it rejects a REVERSED, a MISSING, and an EXTRA physical CNOT:
example : ok? (verifyDirectMixedInstrQStab tenv2Q [] twoLayout (.transversalCNOT cnotSpec2) [.CNOT 1 0]) = false := by decide
example : ok? (verifyDirectMixedInstrQStab tenv2Q [] twoLayout (.transversalCNOT cnotSpec2) []) = false := by decide
example : ok? (verifyDirectMixedInstrQStab tenv2Q [] twoLayout (.transversalCNOT cnotSpec2) [.CNOT 0 1, .CNOT 0 1]) = false := by decide

-- the batched form lowers the same incidence:
def batchSpec2 : TransversalCNOTBatchSpec :=
  { controlBlock := 0, targetBlock := 1, incidence := [[true]], logicalIncidence := [[true]] }
example : ok? (verifyDirectMixedInstrQStab tenv2Q [] twoLayout (.transversalCNOTBatch batchSpec2) [.CNOT 0 1]) = true := by decide

-- (6) a BAD / FAN-OUT incidence (one control physical qubit driving two targets) is
-- rejected by the type checker's physical-transversality condition, NOT silently
-- accepted by artifact comparison — even when the supplied artifact is the naive
-- (wrong) lowering of that fan-out:
def fanoutSpec : TransversalCNOTSpec := { control := ⟨0, 0⟩, target := ⟨1, 0⟩, incidence := [[true, true, false]] }
example : ok? (checkTransversalCNOT tenvQR fanoutSpec) = false := by decide
example : ok? (verifyDirectMixedInstrQStab tenvQR [] qrLayout (.transversalCNOT fanoutSpec) [.CNOT 0 1, .CNOT 0 2]) = false := by decide

-- unsupported Mixed instructions return an EXPLICIT `unsupportedMixed` (no silent accept):
example : (match verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.magic { kind := .tGate, target := ⟨0, 0⟩ }) [] with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide
-- a straight-line PPM `.meas` is now CONCRETELY lowered (see verifyPPMFragmentQStab), so
-- the empty artifact is rejected (certFailed, not a silent accept):
example : ok? (verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.ppm (.meas 0 [(⟨0, 0⟩, PLetter.Z)])) []) = false := by decide
-- a NON-straight-line PPM fragment (frame/discard/control flow) stays explicit unsupported:
example : (match expectedPPMFragmentQStab tenvQ [] bareLayout1 (.frame ⟨0, 0⟩ .X) with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide

-- a MALFORMED layout (two blocks mapped to the same physical destination) is rejected:
def badLayout : PhysLayout := { placements := [(0, 0, 1), (1, 0, 1)] }
example : PhysLayout.wf badLayout = false := by decide
example : (match verifyDirectMixedInstrQStab tenv2Q [] badLayout (.transversalCNOT cnotSpec2) [.CNOT 0 1] with
           | .error (.layoutError _) => true | _ => false) = true := by decide
-- an out-of-range local qubit / unknown block has no layout destination:
example : (bareLayout1.qubit? 0 5) = none := by decide
example : (bareLayout1.qubit? 9 0) = none := by decide

/-! ### Regression: the CNOT path requires FULL layout coverage of BOTH blocks (P1 fix).

    Previously a partial layout that mapped only the incidence-touched physical qubits
    passed; now both involved blocks must be COMPLETELY covered (count = block `n`). -/

/-- A valid `n = 2`, `k = 2` block (two bare logical qubits in one block). -/
def vBare2 : Block :=
  { n := 2, stab := [],
    lx := [[true, false, false, false], [false, true, false, false]],
    lz := [[false, false, true, false], [false, false, false, true]] }

/-- A two-block env, each block `n = 2`. -/
def vEnv22 : TypedEnv := ⟨[⟨vBare2, by decide⟩, ⟨vBare2, by decide⟩]⟩

/-- One logical CNOT (logical 0 of block 0 → logical 0 of block 1) via the physical CNOT
    on physical qubit 0 of each block; the incidence is `2×2` but touches only `(0,0)`. -/
def cnotSparseSpec : TransversalCNOTSpec :=
  { control := ⟨0, 0⟩, target := ⟨1, 0⟩, incidence := [[true, false], [false, false]] }

/-- A PARTIAL layout: maps only ONE of each block's TWO physical qubits.  Structurally
    well-formed (distinct ids, distinct destinations) — but it does NOT cover the blocks. -/
def partialLayout22 : PhysLayout := { placements := [(0, 0, 1), (1, 1, 1)] }
/-- The FULL layout: block 0 → phys 0,1; block 1 → phys 2,3. -/
def fullLayout22 : PhysLayout := { placements := [(0, 0, 2), (1, 2, 2)] }

-- the type checker ACCEPTS this sparse logical CNOT on the n=2 blocks …
example : ok? (checkTransversalCNOT vEnv22 cnotSparseSpec) = true := by decide
-- … the partial layout is structurally well-formed (it would pass `wf`) …
example : PhysLayout.wf partialLayout22 = true := by decide
-- … and it maps the single touched qubit, so the naive lowering would be `[.CNOT 0 1]` —
-- yet the verifier now REJECTS it, because block 0 (n=2) is only 1-qubit covered:
example : ok? (verifyDirectMixedInstrQStab vEnv22 [] partialLayout22 (.transversalCNOT cnotSparseSpec) [.CNOT 0 1]) = false := by decide
example : (match verifyDirectMixedInstrQStab vEnv22 [] partialLayout22 (.transversalCNOT cnotSparseSpec) [.CNOT 0 1] with
           | .error (.layoutError _) => true | _ => false) = true := by decide
-- the coverage helper itself reports the gap on block 0 (covers 1, needs 2):
example : (match requireLayoutCoversBlock vEnv22 partialLayout22 0 with
           | .error (.layoutError _) => true | _ => false) = true := by decide
-- with FULL coverage the SAME instruction + its correct artifact is ACCEPTED:
example : ok? (verifyDirectMixedInstrQStab vEnv22 [] fullLayout22 (.transversalCNOT cnotSparseSpec) [.CNOT 0 2]) = true := by decide

/-! ### Program-level verifier: concatenated artifacts checked instruction by instruction. -/

-- an empty program accepts the empty artifact:
example : ok? (verifyDirectMixedProgQStab tenvQ [] bareLayout1 [] []) = true := by decide
-- H then S on the bare qubit concatenate to `[.H 0, .S 0]`:
example : ok? (verifyDirectMixedProgQStab tenvQ [] bareLayout1
    [.transversal 0 hGate2x2, .transversal 0 sGate2x2] [.H 0, .S 0]) = true := by decide
-- CONCATENATION ORDER matters: `[.S 0, .H 0]` is rejected:
example : ok? (verifyDirectMixedProgQStab tenvQ [] bareLayout1
    [.transversal 0 hGate2x2, .transversal 0 sGate2x2] [.S 0, .H 0]) = false := by decide
-- a transversal then an inter-block CNOT concatenate to `[.H 0, .CNOT 0 1]`:
example : ok? (verifyDirectMixedProgQStab tenv2Q [] twoLayout
    [.transversal 0 hGate2x2, .transversalCNOT cnotSpec2] [.H 0, .CNOT 0 1]) = true := by decide
-- an unsupported instruction ANYWHERE in the program is an explicit `unsupportedMixed`:
example : (match verifyDirectMixedProgQStab tenvQ [] bareLayout1
            [.transversal 0 hGate2x2, .magic { kind := .tGate, target := ⟨0, 0⟩ }] [.H 0] with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide
-- the program verifier ALSO inherits the full-coverage requirement:
example : ok? (verifyDirectMixedProgQStab vEnv22 [] partialLayout22 [.transversalCNOT cnotSparseSpec] [.CNOT 0 1]) = false := by decide

/-! ### Logical Pauli `.pauli q p` → QStab (layout-aware representative). -/

-- bare logical X / Z accepted (one physical `.X`/`.Z` on the layout qubit):
example : ok? (verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.pauli ⟨0, 0⟩ .X) [.X 0]) = true := by decide
example : ok? (verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.pauli ⟨0, 0⟩ .Z) [.Z 0]) = true := by decide
-- bare logical Y lowers to the honest `.X; .Z` convention (phase ignored):
example : ok? (verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.pauli ⟨0, 0⟩ .Y) [.X 0, .Z 0]) = true := by decide

-- repetition-code logical X̄ = XXX requires the FULL physical support, NOT one physical X:
example : (layoutPauliRep? tenvR repLayout [(⟨0, 0⟩, PLetter.X)]).toOption = some (Physical.ofString "XXX") := by decide
example : ok? (verifyDirectMixedInstrQStab tenvR [] repLayout (.pauli ⟨0, 0⟩ .X) [.X 0, .X 1, .X 2]) = true := by decide
example : ok? (verifyDirectMixedInstrQStab tenvR [] repLayout (.pauli ⟨0, 0⟩ .X) [.X 0]) = false := by decide

-- wrong logical index / wrong block — rejected by the TYPE CHECKER (checkInstr `.pauli`):
example : ok? (verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.pauli ⟨0, 5⟩ .X) [.X 0]) = false := by decide
example : ok? (verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.pauli ⟨9, 0⟩ .X) [.X 0]) = false := by decide
-- wrong Pauli / missing / extra / reordered gates — rejected by artifact comparison:
example : ok? (verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.pauli ⟨0, 0⟩ .X) [.Z 0]) = false := by decide
example : ok? (verifyDirectMixedInstrQStab tenvR [] repLayout (.pauli ⟨0, 0⟩ .X) [.X 0, .X 1]) = false := by decide
example : ok? (verifyDirectMixedInstrQStab tenvR [] repLayout (.pauli ⟨0, 0⟩ .X) [.X 0, .X 1, .X 2, .X 2]) = false := by decide
example : ok? (verifyDirectMixedInstrQStab tenvR [] repLayout (.pauli ⟨0, 0⟩ .X) [.X 2, .X 1, .X 0]) = false := by decide

-- wrong LAYOUT: placing block 0 at GLOBAL qubit 5 moves the gate (qubit 5, not 0):
def offsetLayout1 : PhysLayout := { placements := [(0, 5, 1)] }
example : ok? (verifyDirectMixedInstrQStab tenvQ [] offsetLayout1 (.pauli ⟨0, 0⟩ .X) [.X 0]) = false := by decide
example : ok? (verifyDirectMixedInstrQStab tenvQ [] offsetLayout1 (.pauli ⟨0, 0⟩ .X) [.X 5]) = true := by decide

/-! ### Layout-aware PPM measurement: global indices vs the compact ordering. -/

-- measuring logical Z on BLOCK 1: the COMPACT representative places it at index 0 …
example : targetPauliRep? tenv2Q [(⟨1, 0⟩, PLetter.Z)] = some (Physical.ofString "Z") := by decide
-- … but the LAYOUT places block 1 at GLOBAL qubit 1, so the layout-aware rep is "IZ":
example : (layoutPauliRep? tenv2Q twoLayout [(⟨1, 0⟩, PLetter.Z)]).toOption = some (Physical.ofString "IZ") := by decide
-- the layout-aware verifier ACCEPTS the global artifact (measures qubit 1 = "IZ") …
example : ok? (verifyPPMMeasurementQStabLayout tenv2Q [] twoLayout (some ⟨0, 0⟩) [(⟨1, 0⟩, PLetter.Z)]
    [.bind (.prop (some ⟨0, 0⟩) (Physical.ofString "IZ")), .bind (.parity [0])]) = true := by decide
-- … and REJECTS the COMPACT-ordered artifact (measures qubit 0 = "Z"), which the old
-- compact `verifyPPMMeasurementQStab` would have accepted — closing the global-index gap:
example : ok? (verifyPPMMeasurementQStabLayout tenv2Q [] twoLayout (some ⟨0, 0⟩) [(⟨1, 0⟩, PLetter.Z)]
    [.bind (.prop (some ⟨0, 0⟩) (Physical.ofString "Z")), .bind (.parity [0])]) = false := by decide
-- a joint Z⊗Z over blocks 0,1 maps to "ZZ" globally (both bare qubits) — X+Z combine per qubit:
example : (layoutPauliRep? tenv2Q twoLayout [(⟨0, 0⟩, PLetter.Z), (⟨1, 0⟩, PLetter.Z)]).toOption
    = some (Physical.ofString "ZZ") := by decide

/-! ### Straight-line PPM fragment → QStab measurements (item 4). -/

-- a single `.meas` lowers to one layout-aware physical `.prop`:
example : ok? (verifyPPMFragmentQStab tenvQ [] bareLayout1 (.meas 0 [(⟨0, 0⟩, PLetter.Z)])
    [.bind (.prop none (Physical.ofString "Z"))]) = true := by decide
-- the wrong measured Pauli is rejected:
example : ok? (verifyPPMFragmentQStab tenvQ [] bareLayout1 (.meas 0 [(⟨0, 0⟩, PLetter.Z)])
    [.bind (.prop none (Physical.ofString "X"))]) = false := by decide
-- a straight-line `seq` of two measurements concatenates in order:
example : ok? (verifyPPMFragmentQStab tenvQ [] bareLayout1
    (.seq (.meas 0 [(⟨0, 0⟩, PLetter.Z)]) (.meas 1 [(⟨0, 0⟩, PLetter.X)]))
    [.bind (.prop none (Physical.ofString "Z")), .bind (.prop none (Physical.ofString "X"))]) = true := by decide
-- `skip` lowers to the empty program:
example : ok? (verifyPPMFragmentQStab tenvQ [] bareLayout1 .skip []) = true := by decide
-- a fragment carrying a `.frame` effect is explicitly UNSUPPORTED (NOT silently erased):
example : (match expectedPPMFragmentQStab tenvQ [] bareLayout1
            (.seq (.meas 0 [(⟨0, 0⟩, PLetter.Z)]) (.frame ⟨0, 0⟩ .X)) with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide

/-! ### Program-level verifier over the EXTENDED supported set. -/

-- a transversal then a straight-line PPM measurement concatenate:
example : ok? (verifyDirectMixedProgQStab tenvQ [] bareLayout1
    [.transversal 0 hGate2x2, .ppm (.meas 0 [(⟨0, 0⟩, PLetter.Z)])]
    [.H 0, .bind (.prop none (Physical.ofString "Z"))]) = true := by decide
-- two logical Paulis in a program concatenate to `[.X 0, .Z 0]`:
example : ok? (verifyDirectMixedProgQStab tenvQ [] bareLayout1
    [.pauli ⟨0, 0⟩ .X, .pauli ⟨0, 0⟩ .Z] [.X 0, .Z 0]) = true := by decide

/-! ### Coverage status (machine-checked, matching the §V table). -/

example : mixedInstrStatus (.transversal 0 hGate2x2) = .exactVerified := by decide
example : mixedInstrStatus (.transversalCNOT cnotSpec2) = .exactVerified := by decide
example : mixedInstrStatus (.pauli ⟨0, 0⟩ .X) = .exactVerified := by decide
example : mixedInstrStatus (.ppm .skip) = .partiallyVerified := by decide
example : mixedInstrStatus (.automorphism 0 []) = .deferred := by decide
example : mixedInstrStatus (.magic { kind := .tGate, target := ⟨0, 0⟩ }) = .deferred := by decide

/-! ### Milestone B — the Clifford simulator induces the right symplectic map. -/

-- the empty artifact induces the identity; `[.H 0]` induces the Hadamard symplectic J:
example : (qstabCliffordMap? tenvQ bareLayout1 0 []).toOption = some [[true, false], [false, true]] := by decide
example : (qstabCliffordMap? tenvQ bareLayout1 0 [.H 0]).toOption = some [[false, true], [true, false]] := by decide
example : (qstabCliffordMap? tenvQ bareLayout1 0 [.S 0]).toOption = some [[true, true], [false, true]] := by decide
-- a measurement / prep / out-of-block gate has NO induced Clifford map (explicit error):
example : (qstabCliffordMap? tenvQ bareLayout1 0 [.bind (.prop none (Physical.ofString "Z"))]).toOption = none := by decide
example : (qstabCliffordMap? tenvQ bareLayout1 0 [.H 5]).toOption = none := by decide

/-! ### Milestone C — `.automorphism` via the SEMANTIC induced-map verifier. -/

-- identity automorphism (M = I₂) accepts the EMPTY artifact:
example : ok? (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[true, false], [false, true]] []) = true := by decide
-- Hadamard automorphism (M = J) accepts `[.H 0]`:
example : ok? (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[false, true], [true, false]] [.H 0]) = true := by decide
-- S automorphism accepts `[.S 0]`:
example : ok? (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[true, true], [false, true]] [.S 0]) = true := by decide
-- WRONG gate: an S artifact does NOT induce the Hadamard map:
example : ok? (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[false, true], [true, false]] [.S 0]) = false := by decide
-- gate on the WRONG physical qubit (5 ∉ block-0 layout) is rejected:
example : ok? (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[false, true], [true, false]] [.H 5]) = false := by decide
-- a measurement / prep artifact is rejected (not a Clifford-automorphism gate):
example : ok? (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[false, true], [true, false]]
    [.bind (.prop none (Physical.ofString "Z"))]) = false := by decide
example : ok? (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[true, false], [false, true]] [.prepZero 0]) = false := by decide
-- a SHAPE-INVALID automorphism (M not 2n×2n) is rejected by the CHECKER, not rescued by the artifact:
example : ok? (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[true]] []) = false := by decide
-- a trailing Pauli `.X` is a frame correction: ACCEPTED in symplectic mode (default) with
-- status `symplecticVerified` — NOT `exactVerified` (see the strict examples in Milestone 1):
example : (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[false, true], [true, false]] [.H 0, .X 0]).toOption
    = some .symplecticVerified := by decide

/-! ### Milestone D — GENERAL (non-H/S) `.transversal` via the semantic map verifier. -/

-- the IDENTITY transversal (g = I₂) accepts the EMPTY artifact semantically …
example : ok? (verifyTransversalMapQStab tenvQ [] bareLayout1 0 [[true, false], [false, true]] []) = true := by decide
-- … while the STRUCTURAL verifier explicitly defers it (only H/S have a canonical lowering):
example : (match verifyDirectMixedInstrQStab tenvQ [] bareLayout1 (.transversal 0 [[true, false], [false, true]]) [] with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide
-- a non-H/S Clifford `g = [[F,T],[T,T]]` (= HS) is verified by the artifact `[.H 0, .S 0]`:
example : ok? (verifyTransversalMapQStab tenvQ [] bareLayout1 0 [[false, true], [true, true]] [.H 0, .S 0]) = true := by decide
-- … and a WRONG artifact for it (just `[.H 0]`) is rejected:
example : ok? (verifyTransversalMapQStab tenvQ [] bareLayout1 0 [[false, true], [true, true]] [.H 0]) = false := by decide

/-! ### Milestone 1 — strict (exact) vs symplectic mode for Pauli-frame gates. -/

-- strict (exact) mode REJECTS a trailing `.X` frame gate (the audit's concern) …
example : ok? (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[false, true], [true, false]] [.H 0, .X 0] (mode := .exact)) = false := by decide
-- … while symplectic mode ACCEPTS it with the explicit WEAKER status `symplecticVerified`:
example : (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[false, true], [true, false]] [.H 0, .X 0] (mode := .symplectic)).toOption
    = some .symplecticVerified := by decide
-- a frame-free `[.H 0]` IS `exactVerified` in exact mode:
example : (verifyAutomorphismQStab tenvQ [] bareLayout1 0 [[false, true], [true, false]] [.H 0] (mode := .exact)).toOption
    = some .exactVerified := by decide

/-! ### Milestone 2 — logical action MODULO stabilizers (the QEC-correct wall). -/

/-- The [[2,1]] code with stabilizer `XX`: `X̄ = X₀ ≡ X₁ mod stab`, so a physical SWAP acts
    as the IDENTITY logical automorphism — though its physical map ≠ identity. -/
def xxCode : Block :=
  { n := 2, stab := [[true, true, false, false]],
    lx := [[true, false, false, false]],
    lz := [[false, false, true, true]] }
def xxEnv : TypedEnv := ⟨[⟨xxCode, by decide⟩]⟩
def xxLayout : PhysLayout := { placements := [(0, 0, 2)] }
def idMat4 : ChainQ.GF2.BoolMat :=
  [[true, false, false, false], [false, true, false, false],
   [false, false, true, false], [false, false, false, true]]
/-- A physical SWAP(0,1) = three CNOTs. -/
def xxSwap : StabilizerProg := [.CNOT 0 1, .CNOT 1 0, .CNOT 0 1]

-- the SWAP realises the IDENTITY logical automorphism MODULO stabilizers (ACCEPTED) …
example : ok? (verifyAutomorphismQStab xxEnv [] xxLayout 0 idMat4 xxSwap (mode := .logicalModStab)) = true := by decide
-- … but its physical map ≠ identity, so exact/symplectic modes REJECT it (stricter than needed):
example : ok? (verifyAutomorphismQStab xxEnv [] xxLayout 0 idMat4 xxSwap (mode := .symplectic)) = false := by decide
example : ok? (verifyAutomorphismQStab xxEnv [] xxLayout 0 idMat4 xxSwap (mode := .exact)) = false := by decide
-- a genuinely WRONG artifact (an `.H`) is rejected even modulo stabilizers:
example : ok? (verifyAutomorphismQStab xxEnv [] xxLayout 0 idMat4 [.H 0] (mode := .logicalModStab)) = false := by decide

-- P0 AUDIT FIX: a physical `.S` on the UNMEASURED qubit 1 fixes `lx`/`lz` mod stabilizers
-- BUT sends the stabilizer `XX` outside the code.  It WAS wrongly accepted; `logicalModStab`
-- now REJECTS it (codespace not preserved), in every mode:
example : ok? (verifyAutomorphismQStab xxEnv [] xxLayout 0 idMat4 [.S 1] (mode := .logicalModStab)) = false := by decide
example : ok? (verifyAutomorphismQStab xxEnv [] xxLayout 0 idMat4 [.S 1] (mode := .symplectic)) = false := by decide
example : ok? (verifyAutomorphismQStab xxEnv [] xxLayout 0 idMat4 [.S 1] (mode := .exact)) = false := by decide
-- the rejection is specifically the stabilizer-preservation gate (a `certFailed`):
example : (match verifyAutomorphismQStab xxEnv [] xxLayout 0 idMat4 [.S 1] (mode := .logicalModStab) with
           | .error (.certFailed _) => true | _ => false) = true := by decide
-- root cause, machine-checked: `[.S 1]`'s induced map does NOT preserve `XX`, but SWAP's DOES:
example : (qstabCliffordMap? xxEnv xxLayout 0 [.S 1]).toOption.map (preservesBlockStab xxCode) = some false := by decide
example : (qstabCliffordMap? xxEnv xxLayout 0 xxSwap).toOption.map (preservesBlockStab xxCode) = some true := by decide

/-! ### Milestone 3 — program-composable SEMANTIC verification via chunks. -/

def chunkAutoH  : MixedQStabChunk := { instr := .automorphism 0 [[false, true], [true, false]], artifact := [.H 0] }
def chunkPauliX : MixedQStabChunk := { instr := .pauli ⟨0, 0⟩ .X, artifact := [.X 0] }

-- a program `[automorphism H ; pauli X]` verifies via chunks (full artifact = [.H 0, .X 0]):
example : ok? (verifyChunkedMixedProgQStab tenvQ [] bareLayout1 [chunkAutoH, chunkPauliX] [.H 0, .X 0]) = true := by decide
-- WRONG full-artifact order rejected:
example : ok? (verifyChunkedMixedProgQStab tenvQ [] bareLayout1 [chunkAutoH, chunkPauliX] [.X 0, .H 0]) = false := by decide
-- the SAME program is NOT verifiable WITHOUT chunks (automorphism has no structural lowering):
example : (match verifyDirectMixedProgQStab tenvQ [] bareLayout1
            [.automorphism 0 [[false, true], [true, false]], .pauli ⟨0, 0⟩ .X] [.H 0, .X 0] with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide
-- a chunk whose artifact does NOT implement its instruction is rejected:
example : ok? (verifyChunkedMixedProgQStab tenvQ [] bareLayout1
    [{ instr := .automorphism 0 [[false, true], [true, false]], artifact := [.S 0] }, chunkPauliX] [.S 0, .X 0]) = false := by decide
-- switch / magic chunks stay explicit unsupported (via the public chunked entry point):
example : (match verifyChunkedMixedProgQStab tenvQ [] bareLayout1
            [{ instr := .magic { kind := .tGate, target := ⟨0, 0⟩ }, artifact := [] }] [] with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide

/-! ### Milestone 5 — `.switch` verification spec (deferred; empty artifact rejected). -/

-- the switch QStab verifier ALWAYS defers (never accepts an empty — or any — artifact):
example : ok? (verifySwitchQStab {} []) = false := by decide
example : (match verifySwitchQStab {} [.H 0] with | .error (.unsupportedMixed _) => true | _ => false) = true := by decide

/-! ### Milestone 4 — refined status accounting (machine-checked). -/

example : mixedInstrStatus (.transversal 0 hGate2x2) = .exactVerified := by decide
example : mixedInstrStatus (.transversal 0 sGate2x2) = .exactVerified := by decide
example : mixedInstrStatus (.transversal 0 [[true, false], [false, true]]) = .deferred := by decide
example : mixedInstrStatus (.ppm (.meas 0 [(⟨0, 0⟩, PLetter.Z)])) = .partiallyVerified := by decide
example : mixedInstrStatus (.ppm (.frame ⟨0, 0⟩ .X)) = .deferred := by decide
example : mixedInstrStatus (.switch 0 vBare2 { kind := .teleport, f := [] }) = .structurallyCheckedOnly := by decide
-- semantic status is MODE-aware (context-aware — never claims a mode that was not run):
example : mixedInstrSemanticStatus .exact (.automorphism 0 idMat4) = .exactVerified := by decide
example : mixedInstrSemanticStatus .symplectic (.transversal 0 hGate2x2) = .symplecticVerified := by decide
example : mixedInstrSemanticStatus .logicalModStab (.automorphism 0 idMat4) = .logicalModuloStabilizerVerified := by decide
example : mixedInstrSemanticStatus .exact (.magic { kind := .tGate, target := ⟨0, 0⟩ }) = .deferred := by decide

end Compiler.Verification
