/-
  Compiler.QASM.Physical -- QASM front-end through the first checked physical slice.

  This module wires the existing QASM allocation/MixedIR front-end into the checked
  MixedIR -> QStab structural compiler and then into QClifford extraction circuits.

  HONEST SCOPE.  This is a real end-to-end path for the currently verified structural
  stabilizer fragment: logical Paulis, transversal H/S, verified transversal CNOTs, and
  straight-line logical Pauli measurements.  It intentionally rejects `.magic`,
  `.switch`, scheduled/controlled PPM, automorphisms without chunks, and parallel PPM
  instead of fabricating a physical circuit.
-/
import Compiler.QASM.Parse
import Compiler.Verification.Compile

namespace Compiler.QASM

open Compiler Compiler.ChainQ2Mixed Compiler.Verification TypeChecker PPM QStab
open Compiler.CodeSwitch

/-! ## MixedIR bridge. -/

/-- Errors from the physical QASM pipeline, phase-separated enough for tests/audits. -/
inductive PhysicalCompileError where
  | parse        (e : ParseError)
  | qasm         (e : QASMError)
  | unsupported  (note : String)
  | verification (e : VerificationError)
  | qclifford    (e : Compiler.QStab2QClifford.CompileError)
  deriving Repr

def liftQASMPhysical {α : Type} : Except QASMError α -> Except PhysicalCompileError α
  | .ok a => .ok a
  | .error e => .error (.qasm e)

def liftVerificationPhysical {α : Type} :
    Except VerificationError α -> Except PhysicalCompileError α
  | .ok a => .ok a
  | .error e => .error (.verification e)

def liftQCliffordPhysical {α : Type} :
    Except Compiler.QStab2QClifford.CompileError α -> Except PhysicalCompileError α
  | .ok a => .ok a
  | .error e => .error (.qclifford e)

/-- Forget the checked-primitive wrapper into the executable MixedIR surface. -/
def mixPrimToMixedInstr? : MixPrim -> Except PhysicalCompileError MixedInstr
  | .ppm r P              => .ok (.ppm (.meas r P))
  | .ppmFragment s        => .ok (.ppm s)
  | .parallelPPM _ _      =>
      .error (.unsupported "parallel PPM has no direct QStab structural lowering yet")
  | .transversal b g      => .ok (.transversal b g)
  | .transversalCNOT s    => .ok (.transversalCNOT s)
  | .transversalBatch s   => .ok (.transversalCNOTBatch s)
  | .automorphism b M     => .ok (.automorphism b M)
  | .codeSwitch b D cert  => .ok (.switch b D cert)
  | .pauli q p            => .ok (.pauli q p)
  | .magic ob             => .ok (.magic ob)

/-- The checked MixedIR program contained in a QASM compilation artifact. -/
def QASMArtifact.logicalExec? {ws : List CapabilityWitness} (a : QASMArtifact ws) :
    Except PhysicalCompileError LogicalExec :=
  a.compiled.steps.mapM (fun s => mixPrimToMixedInstr? s.prim)

/-! ## Automatic contiguous physical layout. -/

/-- One contiguous QStab physical range per typed logical block. -/
def contiguousPlacementsFrom : Nat -> Nat -> List TypedBlock -> List (Nat × Nat × Nat)
  | _, _, [] => []
  | b, base, tb :: rest =>
      (b, base, tb.block.n) :: contiguousPlacementsFrom (b + 1) (base + tb.block.n) rest

/-- The default logical-block layout used by the QASM physical compiler. -/
def contiguousLayoutOfEnv (Γ : TypedEnv) : PhysLayout :=
  { placements := contiguousPlacementsFrom 0 0 Γ.blocks }

/-! ## QStab stabilizer program -> QClifford circuit. -/

def propPaulis : QStab.Prog -> List QStab.PauliString
  | [] => []
  | .prop _ P :: rest => P :: propPaulis rest
  | .parity _ :: rest => propPaulis rest

def firstHelper (P : QStab.PauliString) (i : Nat) : Nat := P.length + i

/-- Default extraction schedule: destructive for weight-one X/Z, standard for heavier X/Z.
    Mixed/Y checks are rejected explicitly. -/
def defaultExtractionSpecForProp? (i : Nat) (P : QStab.PauliString) :
    Except PhysicalCompileError Compiler.QStab2QClifford.ExtractionSpec :=
  let supp := Compiler.QStab2QClifford.supportOf P
  match supp with
  | [] => .error (.unsupported "cannot extract an identity QStab Prop")
  | q :: [] =>
      if Compiler.QStab2QClifford.extractionSpecOk P
          (Compiler.QStab2QClifford.ExtractionSpec.destructiveZ q) then
        .ok (Compiler.QStab2QClifford.ExtractionSpec.destructiveZ q)
      else if Compiler.QStab2QClifford.extractionSpecOk P
          (Compiler.QStab2QClifford.ExtractionSpec.destructiveX q) then
        .ok (Compiler.QStab2QClifford.ExtractionSpec.destructiveX q)
      else
        .error (.unsupported "default extraction supports only uniform X/Z QStab Props")
  | _ =>
      let h := firstHelper P i
      if Compiler.QStab2QClifford.extractionSpecOk P
          (Compiler.QStab2QClifford.ExtractionSpec.standardZ supp h) then
        .ok (Compiler.QStab2QClifford.ExtractionSpec.standardZ supp h)
      else if Compiler.QStab2QClifford.extractionSpecOk P
          (Compiler.QStab2QClifford.ExtractionSpec.standardX supp h) then
        .ok (Compiler.QStab2QClifford.ExtractionSpec.standardX supp h)
      else
        .error (.unsupported "default extraction supports only uniform X/Z QStab Props")

def defaultExtractionSpecsFrom : Nat -> List QStab.PauliString ->
    Except PhysicalCompileError (List Compiler.QStab2QClifford.ExtractionSpec)
  | _, [] => .ok []
  | i, P :: rest => do
      let s <- defaultExtractionSpecForProp? i P
      let ss <- defaultExtractionSpecsFrom (i + 1) rest
      return s :: ss

def defaultExtractionConfig? (p : QStab.StabilizerProg) :
    Except PhysicalCompileError Compiler.QStab2QClifford.CompileConfig := do
  let specs <- defaultExtractionSpecsFrom 0 (propPaulis p.dataflow)
  return { specOf := fun i => specs.getD i default }

def stabilizerInstrToQClifford :
    QStab.StabilizerInstr -> Nat -> Nat -> Nat ->
      Compiler.QStab2QClifford.CompileConfig -> QClifford.Circuit
  | .bind (.prop _ _), v, a, i, cfg =>
      Compiler.QStab2QClifford.compileProp (cfg.specOf i) v a
  | .bind (.parity srcs), v, _, _, _ => [QClifford.Gate.parity v srcs]
  | .prepZero q, _, _, _, _ => [QClifford.Gate.prepZero q]
  | .prepPlus q, _, _, _, _ => [QClifford.Gate.prepPlus q]
  | .H q, _, _, _, _ => [QClifford.Gate.H q]
  | .S q, _, _, _, _ => [QClifford.Gate.S q]
  | .X q, _, _, _, _ => [QClifford.Gate.X q]
  | .Z q, _, _, _, _ => [QClifford.Gate.Z q]
  | .CNOT c t, _, _, _, _ => [QClifford.Gate.CNOT c t]
  | .CZ a b, _, _, _, _ => [QClifford.Gate.CZ a b]
  | .ifPauli src p q, _, _, _, _ => [QClifford.Gate.ifPauli src p q]

/-- Lower a richer QStab stabilizer program, preserving Clifford gates and compiling only
    the bound `Prop`/`Parity` dataflow nodes through the existing QStab2QClifford schemes. -/
def compileStabilizerFrom (cfg : Compiler.QStab2QClifford.CompileConfig) :
    QStab.StabilizerProg -> Nat -> Nat -> Nat -> QClifford.Circuit
  | [], _, _, _ => []
  | instr :: rest, v, a, i =>
      let here := stabilizerInstrToQClifford instr v a i cfg
      match instr with
      | .bind (.prop _ _) =>
          let spec := cfg.specOf i
          here ++ compileStabilizerFrom cfg rest (v + 1)
            (a + Compiler.QStab2QClifford.auxCount spec) (i + 1)
      | .bind (.parity _) => here ++ compileStabilizerFrom cfg rest (v + 1) a i
      | _ => here ++ compileStabilizerFrom cfg rest v a i

def compileStabilizerToQClifford (cfg : Compiler.QStab2QClifford.CompileConfig)
    (p : QStab.StabilizerProg) : QClifford.Circuit :=
  compileStabilizerFrom cfg p 0 p.dataflow.length 0

def compileStabilizerToQClifford? (cfg : Compiler.QStab2QClifford.CompileConfig)
    (p : QStab.StabilizerProg) :
    Except Compiler.QStab2QClifford.CompileError QClifford.Circuit :=
  if p.wf then
    if Compiler.QStab2QClifford.specsOk cfg p.dataflow then
      .ok (compileStabilizerToQClifford cfg p)
    else
      .error .badExtractionSchedule
  else
    .error .sourceMalformed

/-! ## Public physical entry points. -/

structure QASMPhysicalArtifact (ws : List CapabilityWitness) where
  qasm      : QASMArtifact ws
  mixed     : LogicalExec
  layout    : PhysLayout
  qstab     : QStab.StabilizerProg
  extractionConfig : Compiler.QStab2QClifford.CompileConfig
  qclifford : QClifford.Circuit

def compileQASMToQClifford? (ws : List CapabilityWitness) (prog : QASMProgram)
    (req : AllocationRequest) : Except PhysicalCompileError (QASMPhysicalArtifact ws) := do
  let qasm <- liftQASMPhysical (compileQASMToMixIR? ws prog req)
  let mixed <- qasm.logicalExec?
  let layout := contiguousLayoutOfEnv qasm.compiled.ctxIn.env
  let caps := ws.map CapabilityWitness.toCapability
  let qstab <- liftVerificationPhysical
    (compileAndVerifyDirectMixedProgQStab qasm.compiled.ctxIn.env caps layout mixed)
  let cfg <- defaultExtractionConfig? qstab
  let qclifford <- liftQCliffordPhysical (compileStabilizerToQClifford? cfg qstab)
  return {
    qasm := qasm,
    mixed := mixed,
    layout := layout,
    qstab := qstab,
    extractionConfig := cfg,
    qclifford := qclifford }

def compileOpenQASM2ToQClifford? (ws : List CapabilityWitness) (src : String)
    (req : AllocationRequest) : Except PhysicalCompileError (QASMPhysicalArtifact ws) :=
  match parseOpenQASM2? src with
  | .error e => .error (.parse e)
  | .ok prog => compileQASMToQClifford? ws prog req

/-! ## Decide-level smoke tests for the supported/unsupported boundary. -/

def physOneDecl : ChainQ.NamedCodeDecl := { ChainQ.indexedBareDecl with name := "q0" }

def physOneReq : AllocationRequest :=
  { decls := [physOneDecl],
    dataLogicals := [⟨"q0", "data"⟩],
    ancillas := [],
    cnotMode := .strictTransversal,
    cnotIncidence := some [[true]] }

def physOneSrc : String :=
  "qreg q[1]; creg c[1]; h q[0]; s q[0]; x q[0]; z q[0]; measure q[0] -> c[0];"

def physOneExpected : QClifford.Circuit :=
  [.H 0, .S 0, .X 0, .Z 0, .meas 0 0]

example :
    (match compileOpenQASM2ToQClifford? [] physOneSrc physOneReq with
     | .ok a => a.qclifford = physOneExpected
     | .error _ => false) = true := by decide

def physCtrlDecl : ChainQ.NamedCodeDecl := { ChainQ.indexedBareDecl with name := "ctrl" }
def physTgtDecl  : ChainQ.NamedCodeDecl := { ChainQ.indexedBareDecl with name := "tgt" }

def physCXReq : AllocationRequest :=
  { decls := [physCtrlDecl, physTgtDecl],
    dataLogicals := [⟨"ctrl", "data"⟩, ⟨"tgt", "data"⟩],
    ancillas := [],
    cnotMode := .strictTransversal,
    cnotIncidence := some [[true]] }

def physCXSrc : String :=
  "qreg q[2]; creg c[2]; cx q[0],q[1]; measure q[0] -> c[0]; measure q[1] -> c[1];"

example :
    (match compileOpenQASM2ToQClifford? [] physCXSrc physCXReq with
     | .ok a => a.qclifford = [.CNOT 0 1, .meas 0 0, .meas 1 1]
     | .error _ => false) = true := by decide

-- T/magic is typed at MixedIR but still has no physical gate-injection lowering.
example :
    (match compileOpenQASM2ToQClifford? [] "qreg q[1]; t q[0];" physOneReq with
     | .error (.verification (.unsupportedMixed _)) => true
     | _ => false) = true := by decide

-- Surface-code logical X/readout compiles through multi-qubit standard extraction.
example : ok? (compileQASMToQClifford? [] progPauliReadout reqSurface2) = true := by decide

end Compiler.QASM
