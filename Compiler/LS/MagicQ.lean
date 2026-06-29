/-
  Compiler.LS.MagicQ — a SCAFFOLD lowering from MagicQ cultivation to the LS layer.

  This maps each MagicQ cultivation `ProtocolOp` to LS STAGE MARKERS and DEFERRED LS
  CONTRACTS (the surgery chunks this pass does not build), plus the postselection
  metadata.  It is HONEST about what it is NOT: a stage scaffold, not a lowered
  measurement circuit.  In particular:
    * `assumeLogicalCheck` with the H_XY axis becomes a DEFERRED `hxyDoubleCheck`
      contract — NEVER a fake Pauli `meas` (the audit's standing rule);
    * `graft` / `transitionToMatchable` become the `escapeGraft` / `escapeTransition`
      contracts;
    * `postselect` becomes LS postselection metadata over detectors/tags;
    * `inject`/`grow`/`stabilize` become stage chunks.

  The scaffold program carries no physical qubits and is NOT submitted to `LS.check`;
  the real circuit is the deferred chunk obligations.  Mathlib-free.
-/
import Compiler.LS.Check
import Compiler.LS.ChunkCompose
import Compiler.LS.SyndromeRounds
import Compiler.LS.Gidney.Cultivation
import MagicQ.Library.Cultivation
import MagicQ.Library.ReedMuller15

namespace Compiler.LS
open QStab Physical

-- the `by decide` scaffold tests reduce `checkProtocol`/`cultivationScaffoldToLS` over the
-- accumulated obligation list, which exceeds the default elaborator recursion depth (512).
set_option maxRecDepth 4000

/-- Lower a MagicQ postselection PREDICATE to an `LS.PostPred` (1:1 over the Boolean
    structure).  MagicQ v1 has ONLY detector/syndrome-NAME atoms, so this only ever emits LS
    `.detector` atoms.  In fact the LS `.tag` atom is never produced by ANY MagicQ lowering:
    `magicPostToLS` maps `PostselectCond.taggedDetectors` to `PostPolicy.byDetector` (a
    detector-NAME policy resolved against `detNames`), NOT `.byTag` — so a MagicQ-sourced
    postselect can never become a later LS `unknownTag`/`unknownDetector`. -/
def magicPredToLS : MagicQ.PostPred → PostPred
  | .detector name => .detector name        -- MagicQ detector/syndrome NAME → LS detector-name atom
  | .and p q       => .and (magicPredToLS p) (magicPredToLS q)
  | .or p q        => .or (magicPredToLS p) (magicPredToLS q)
  | .not p         => .not (magicPredToLS p)

/-- Map a MagicQ postselection condition to LS postselection metadata. -/
def magicPostToLS : MagicQ.PostselectCond → List LSOp
  | .fullDetectors          => [.postselect .full]
  | .syndromeEq name value  => [.postselect (.byDetectorValue name value)]  -- PRESERVE the expected Bool
  | .taggedDetectors name   => [.postselect (.byDetector name)]             -- v1: a detector-NAME alias (MagicQ has no real tags), NOT a true LS tag — so it can never become a later LS `unknownTag`
  | .predicate p            => [.postselect (.byPred (magicPredToLS p))]
  | .decoderGap thr         => [.deferred ⟨.custom "decoder-gap", thr⟩]

/-- Map ONE MagicQ cultivation op to LS stage markers + deferred contracts. -/
def magicOpToLS : MagicQ.ProtocolOp → List LSOp
  | .inject _ _ _ _ _ _ =>
      [ .stage "inject" "encode |T⟩ in a distance-3 color code"
      , .deferred ⟨.stageChunk "inject", "injection chunk (Gidney-style) deferred"⟩ ]
  | .checkLogical _ _ det =>
      [ .stage "check" det
      , .deferred ⟨.custom "logical-check", "Pauli logical check — deferred to an LS measurement"⟩ ]
  | .assumeLogicalCheck _ obs det just =>
      match obs.axis with
      | .hxy     => [ .stage "check" det, .deferred ⟨.hxyDoubleCheck, just⟩ ]
      | .pauli _ => [ .stage "check" det, .deferred ⟨.custom "assumed-logical-check", just⟩ ]
  | .grow _ _ d det =>
      [ .stage "grow" det, .deferred ⟨.stageChunk "grow", s!"grow to color-code fault distance {d}"⟩ ]
  | .stabilize _ r det =>
      [ .stage "stabilize" det, .deferred ⟨.stageChunk "stabilize", s!"{r} superdense / idling rounds"⟩ ]
  | .graft _ _ d det =>
      [ .stage "escape.graft" det, .deferred ⟨.escapeGraft, s!"graft into the grafted code, distance {d}"⟩ ]
  | .transitionToMatchable _ _ d det =>
      [ .stage "escape.transition" det
      , .deferred ⟨.escapeTransition, s!"transition into the final matchable code, distance {d}"⟩ ]
  | .switchBlock _ _ det =>
      -- the switch ALGEBRA is checked by `TypeChecker.checkSwitch` at the MagicQ level; the
      -- executable LS surgery CHUNK that realises the switch is deferred.
      [ .stage "switch" det
      , .deferred ⟨.custom "checked-block-switch", "v2 ChainQ-checked code switch; executable LS surgery chunk deferred"⟩ ]
  | .postselect cond => magicPostToLS cond
  | .measureSyndrome _ _ _ _ _ _ =>
      [ .deferred ⟨.custom "measure-syndrome", "syndrome-measure / distillation chunk deferred"⟩ ]
  | .discard _ => [ .stage "discard" "disposable failure branch" ]
  | .output _  => [ .stage "output" "return the cultivated T on the matchable carrier" ]

/-- **The MagicQ cultivation → LS SCAFFOLD.**  A stage-marker / deferred-contract LS
    program (no physical qubits; NOT a lowered measurement circuit — the name says so).
    The real circuit is the deferred chunk obligations. -/
def cultivationScaffoldToLS (p : MagicQ.Protocol) : Program :=
  { numQubits := 0, ops := (p.ops.map magicOpToLS).flatten, flows := [] }

/-- The deferred LS obligations the scaffold records (the chunk/H_XY/escape contracts). -/
def cultivationObligations (p : MagicQ.Protocol) : List Obligation :=
  (cultivationScaffoldToLS p).contracts.map Obligation.contract

/-! ## §0b. The SUPPORTED executable subset (a SINGLE d3 double-cat H_XY check), GATED by
       the MagicQ checker. -/

/-- Is this op a non-Pauli `H_XY` `assumeLogicalCheck` (the d3 double-cat check stage)? -/
def isHxyAssumeCheck : MagicQ.ProtocolOp → Bool
  | .assumeLogicalCheck _ obs _ _ => match obs.axis with | .hxy => true | _ => false
  | _                             => false

/-- SYNTACTIC subset filter: does this protocol's ONLY executable stage consist of EXACTLY
    ONE non-Pauli `H_XY` double-check (realised by `Gidney.d3DoubleCatCheck`)?
    `inject`/`postselect`/`output`/`discard` are allowed (their physical chunks stay
    DEFERRED); a Pauli `checkLogical`, `grow`, `graft`, `stabilize`, `transitionToMatchable`,
    `switchBlock`, `measureSyndrome`, or a SECOND H_XY check makes it UNSUPPORTED — we refuse to
    erase multiplicity by collapsing several checks into one chunk.  This is SYNTACTIC ONLY;
    SEMANTIC validity (carrier/resource/scope/liveness/linearity) is enforced separately by
    `MagicQ.checkProtocol` in `executableSubsetGate?`. -/
def onlyExecutableStageIsHxyCheck (p : MagicQ.Protocol) : Bool :=
  p.ops.all (fun op => match op with
    | .inject _ _ _ _ _ _           => true
    | .assumeLogicalCheck _ obs _ _ => match obs.axis with | .hxy => true | _ => false
    | .postselect _                 => true
    | .output _                     => true
    | .discard _                    => true
    | _                             => false)
  && (p.ops.filter isHxyAssumeCheck).length == 1     -- EXACTLY ONE H_XY check (no multiplicity erasure)

/-- **The executable-lowering GATE.**  A protocol may be executably lowered ONLY if BOTH
    hold: (1) it is in the supported single-H_XY-check subset (`onlyExecutableStageIsHxyCheck`),
    AND (2) it PASSES its high-level `MagicQ.checkProtocol Γ` (carrier/resource/scope/liveness/
    linearity) — so an INVALID MagicQ protocol can NEVER lower.  Returns a structured
    `LSError`: `chunkNotImplemented` for an unsupported/multi-stage protocol, `magicCheckFailed`
    (carrying the MagicQ error) for a protocol that fails its high-level check. -/
def executableSubsetGate? (Γ : TypeChecker.TypedEnv) (p : MagicQ.Protocol) : Except LSError Unit :=
  if onlyExecutableStageIsHxyCheck p then
    match MagicQ.checkProtocol Γ p with
    | .error e => .error (.magicCheckFailed s!"MagicQ protocol high-level check failed: {repr e}")
    | .ok _    => .ok ()
  else
    .error (.chunkNotImplemented
      "executable lowering supports only a SINGLE d3 double-cat H_XY-check stage; this protocol has unsupported / multiple executable stages (extra H_XY / grow / graft / stabilize / transition / switch / distill)")

/-! ## §0c. The LOGICAL-MEASUREMENT WITNESS / certificate (ties a MagicQ obs to a chunk). -/

/-- An executable LOGICAL-MEASUREMENT WITNESS connecting a MagicQ `assumeLogicalCheck carrier
    obs` to a concrete LS chunk that REALISES it.  It is the certificate data tying the
    logical observable to the chunk's BOUNDARY FLOWS (and thence to the lowered QStab vars):
    the expected observable index/axis, the carrier code FAMILY (so the chunk is NOT applied
    to the wrong code), the chunk name/provenance, the logical operator's physical support,
    the outgoing observable key, the in/out boundary-flow tags, and the body measurement vars
    that realise the logical readout. -/
structure LogicalMeasWitness where
  obsIdx             : Nat       -- the LogicalObs.idx this realises
  axisIsHxy          : Bool      -- the axis (this pass only certifies the non-Pauli H_XY)
  codeFamily         : String    -- the EXPECTED carrier code identity/family (e.g. "ColorCode(3)")
  chunkName          : String    -- the LS chunk name/provenance
  logicalSupport     : SPauli    -- the logical operator's physical support (the boundary Y-parity)
  obsKey             : Int       -- the expected observable key on the OUT-flow
  inFlowTag          : String    -- the incoming boundary flow tag
  outFlowTag         : String    -- the outgoing boundary flow (observable) tag
  logicalReadoutVars : List QVar -- the body measurement vars realising the logical readout
  deriving Repr, DecidableEq

/-- The carrier code FAMILY string of a `CarrierRef`. -/
def codeFamilyOf : MagicQ.CarrierRef → String
  | .external name => name
  | .block id      => s!"block:{id}"

/-- The `(carrier, obsIdx, codeFamily)` of a protocol's SINGLE H_XY check (the carrier's code
    family is read from its `inject`). -/
def protocolHxyTarget? (p : MagicQ.Protocol) : Option (Nat × Nat × String) :=
  match p.ops.find? isHxyAssumeCheck with
  | some (.assumeLogicalCheck carrier obs _ _) =>
      let fam := p.ops.findSome? (fun op => match op with
        | .inject _ _ c code _ _ => if c == carrier then some (codeFamilyOf code) else none
        | _ => none)
      some (carrier, obs.idx, fam.getD "<no-inject>")
  | _ => none

/-- The DETECTOR NAME the protocol's H_XY check emits (the abstract logical-check detector,
    used to wire postselection to the concrete logical readout). -/
def protocolCheckDetector? (p : MagicQ.Protocol) : Option String :=
  p.ops.findSome? (fun op => match op with
    | .assumeLogicalCheck _ obs detector _ => match obs.axis with | .hxy => some detector | _ => none
    | _ => none)

/-- Does the witness MATCH the protocol's H_XY check — same axis (H_XY), observable index,
    AND carrier code family?  An `external "SomeOtherCode"` carrier therefore does NOT match
    the `ColorCode(3)` witness. -/
def witnessMatchesProtocol (w : LogicalMeasWitness) (p : MagicQ.Protocol) : Bool :=
  match protocolHxyTarget? p with
  | some (_carrier, obsIdx, fam) => w.axisIsHxy && decide (w.obsIdx = obsIdx) && decide (w.codeFamily = fam)
  | none => false

/-- **STRUCTURAL certificate check**: chunk `c` realises witness `w` iff it is the named
    chunk and it has (a) an INCOMING boundary flow `w.inFlowTag` whose input support = the
    logical operator (empty output), and (b) an OUTGOING boundary flow `w.outFlowTag` carrying
    observable key `w.obsKey`, empty input, output support = the logical operator, and
    measurement vars = `w.logicalReadoutVars`, all IN RANGE of the chunk's lowered dataflow.
    This ties the MagicQ observable → the boundary flows → the QStab measurement vars.  It is
    STRUCTURAL ONLY — full stabilizer-flow soundness stays the deferred `flowSemantics`. -/
def witnessCertifiesChunk (w : LogicalMeasWitness) (c : LSChunk) : Bool :=
  w.axisIsHxy &&
  decide (c.name = w.chunkName) &&
  c.program.flows.any (fun f =>
    decide (f.tag = w.inFlowTag) && sameSupport f.input w.logicalSupport && f.output.isEmpty) &&
  c.program.flows.any (fun f =>
    decide (f.tag = w.outFlowTag) && f.input.isEmpty && sameSupport f.output w.logicalSupport
      && (f.obsKey == some w.obsKey) && (f.vars == w.logicalReadoutVars)) &&
  w.logicalReadoutVars.all (fun v => decide (v < c.program.dataflow.length))

/-- The witness for the Gidney d=3 double-cat H_XY check on the distance-3 color code. -/
def d3HxyWitness : LogicalMeasWitness :=
  { obsIdx := 0, axisIsHxy := true, codeFamily := "ColorCode(3)", chunkName := "d3-double-cat-check"
    logicalSupport := Gidney.yParity, obsKey := 0
    inFlowTag := "in:Y-parity", outFlowTag := "out:Y-parity", logicalReadoutVars := [1, 2, 5, 6] }

/-- The registry of executable logical-measurement witnesses (witness ⊕ realising chunk). -/
def executableWitnesses : List (LogicalMeasWitness × LSChunk) := [(d3HxyWitness, Gidney.d3DoubleCatCheck)]

/-- Find a witness that BOTH matches the protocol's carrier/observable AND structurally
    certifies its chunk. -/
def findExecutableWitness? (p : MagicQ.Protocol) : Option (LogicalMeasWitness × LSChunk) :=
  executableWitnesses.find? (fun wc => witnessMatchesProtocol wc.1 p && witnessCertifiesChunk wc.1 wc.2)

/-! ## §0d. The gated, witnessed, postselection-preserving executable lowering. -/

/-- The concrete logical-readout DETECTOR over the witness's readout vars, named with the
    protocol's H_XY check detector so MagicQ postselection on that check resolves. -/
def logicalReadoutDetector (name : String) (w : LogicalMeasWitness) : LSOp :=
  .detector { name := name, srcs := w.logicalReadoutVars, tags := ["logical", "hxy"] }

/-- The protocol's MagicQ postselection conditions lowered to LS ops (via `magicPostToLS`). -/
def mappedPostselectOps (p : MagicQ.Protocol) : List LSOp :=
  (p.ops.filterMap (fun op => match op with | .postselect c => some c | _ => none)).flatMap magicPostToLS

/-- Gate (`executableSubsetGate?`) + find a matching/ certifying witness + BUILD the executable
    program: the realising chunk's body, PLUS a concrete logical-readout detector (over the
    witness vars, named with the protocol's check detector), PLUS the protocol's MagicQ
    postselection mapped to LS (so postselection is PRESERVED, not dropped — an unmappable
    postselect makes the subsequent `LS.check` fail with `unknownDetector`).  Refuses
    (`chunkNotImplemented`) if no witness matches the carrier's code/observable. -/
def buildExecutable? (Γ : TypeChecker.TypedEnv) (p : MagicQ.Protocol) :
    Except LSError (LogicalMeasWitness × LSChunk × Program) := do
  executableSubsetGate? Γ p
  match findExecutableWitness? p with
  | none => .error (.chunkNotImplemented
      "no executable logical-measurement WITNESS matches this protocol's carrier code / observable (the carrier code family is not realised by any built chunk — e.g. an external code that is not ColorCode(3)); refusing rather than lowering the wrong chunk")
  | some (w, chunk) =>
      let checkDetName := (protocolCheckDetector? p).getD chunk.name
      let execProg : Program :=
        { chunk.program with ops := chunk.program.ops ++ [logicalReadoutDetector checkDetName w] ++ mappedPostselectOps p }
      .ok (w, chunk, execProg)

/-- **CANONICAL executable lowering (explicit Γ).**  Gated + WITNESSED (so an invalid /
    out-of-subset / wrong-code protocol CANNOT lower), it lowers the witnessed executable
    program — the d3 chunk body + a concrete logical-readout detector + the PRESERVED MagicQ
    postselection — to QStab, and returns the RICH `LoweredChunk` (QStab + sidecar + geometry
    + obligations) including a POSITIVE `structuralLogicalMeasCertified` certificate.  The
    `inject`/`output` stages and the full stabilizer-flow soundness remain DEFERRED. -/
def cultivationToExecutableLSInΓ? (Γ : TypeChecker.TypedEnv) (p : MagicQ.Protocol) :
    Except LSError LoweredChunk := do
  let (w, chunk, execProg) ← buildExecutable? Γ p
  let (qstab, sidecar) ← lowerCheckedWithExtract execProg
  -- STRUCTURAL OBSERVABLE-REALISATION BRIDGE: the witness's readout vars must index real
  -- QStab `prop` measurements in the lowered dataflow (else the "logical readout" is fiction).
  if !readoutVarsAreProps qstab w.logicalReadoutVars then
    .error (.other s!"logical readout vars {w.logicalReadoutVars} do not all realise QStab prop measurements")
  else
    -- the MACHINE-READABLE structural certificate (NOT a stabilizer-flow proof):
    let certData : LogicalMeasCertData :=
      { codeFamily := w.codeFamily, obsIdx := w.obsIdx, axisIsHxy := w.axisIsHxy, chunkName := w.chunkName
        inFlowTag := w.inFlowTag, outFlowTag := w.outFlowTag, logicalSupport := w.logicalSupport
        obsKey := w.obsKey, readoutVars := w.logicalReadoutVars }
    let merged := (sidecar.obligations ++ chunk.obligations ++
      [ Obligation.structuralLogicalMeasCertified certData
      , Obligation.contract ⟨.stageChunk "inject", "injection chunk deferred (the subset lowers only the single d3 H_XY check)"⟩
      , Obligation.contract ⟨.custom "magicq-subset", "only the single H_XY double-check stage is lowered; growth / escape / output remain deferred"⟩ ]).eraseDups
    return { qstab := qstab, sidecar := sidecar, geometry := chunk.geometry, obligations := merged }

/-- **CANONICAL executable lowering** (against the empty environment) → the rich
    `LoweredChunk` (QStab + sidecar + obligations + geometry), NEVER a bare program and NEVER
    a zero-qubit scaffold.  Refuses (`magicCheckFailed` / `chunkNotImplemented`) for any
    invalid / out-of-subset / wrong-code protocol — including full default cultivation and 15-to-1. -/
def cultivationToExecutableLS? (p : MagicQ.Protocol) : Except LSError LoweredChunk :=
  cultivationToExecutableLSInΓ? ⟨[]⟩ p

/-- Back-compat alias for the canonical lowering (returns the rich `LoweredChunk`). -/
def cultivationToExecutableLSSubset? (p : MagicQ.Protocol) : Except LSError LoweredChunk :=
  cultivationToExecutableLS? p

/-- **LOW-LEVEL / INTERNAL**: the bare CHECKED executable LS `Program` (the witnessed d3 body
    + logical-readout detector + postselection), gated/witnessed identically.  Drops the
    sidecar / obligations / geometry, so it must NOT be used as the "compiler success" surface
    — prefer `cultivationToExecutableLS?` (the rich `LoweredChunk`). -/
def cultivationToExecutableLSProgramInternal? (Γ : TypeChecker.TypedEnv) (p : MagicQ.Protocol) :
    Except LSError Program := do
  let (_w, _chunk, execProg) ← buildExecutable? Γ p
  let _ ← Compiler.LS.check execProg
  return execProg

/-! ## §0e. The generic STABILIZE subset (syndrome rounds), witnessed by code family. -/

/-- A SYNDROME-ROUND WITNESS for a `stabilize` stage (analogous to `LogicalMeasWitness`): the
    carrier CODE FAMILY plus the concrete stabilizer supports / patch size / detector-name
    prefix that realise repeated syndrome extraction for that code.  The number of ROUNDS
    comes from the protocol's `stabilize` op. -/
structure SyndromeRoundWitness where
  codeFamily  : String
  numQubits   : Nat
  stabilizers : List SPauli
  namePrefix  : String := "synd"
  deriving Repr, DecidableEq

/-- A toy GENERIC example: a distance-3 repetition-style code with two `ZZ` checks on 3
    qubits.  This is NOT Gidney's growth/escape layout (those supports are not yet sourced) —
    it exists to exercise the witnessed stabilize-lowering PATH generically. -/
def repCode3SyndromeWitness : SyndromeRoundWitness :=
  { codeFamily := "RepCode(3)", numQubits := 3
    stabilizers := [[(0, .Z), (1, .Z)], [(1, .Z), (2, .Z)]], namePrefix := "rep3" }

def syndromeRoundWitnesses : List SyndromeRoundWitness := [repCode3SyndromeWitness]

/-- Find a syndrome-round witness for a carrier code family. -/
def findSyndromeRoundWitness? (codeFamily : String) : Option SyndromeRoundWitness :=
  syndromeRoundWitnesses.find? (fun w => decide (w.codeFamily = codeFamily))

/-- Is this op a `stabilize` stage? -/
def isStabilizeOp : MagicQ.ProtocolOp → Bool
  | .stabilize _ _ _ => true | _ => false

/-- SYNTACTIC subset filter: the protocol's ONLY executable stage is EXACTLY ONE `stabilize`
    (inject/postselect/output/discard allowed; an H_XY check, grow, graft, transition, switch,
    or distill makes it unsupported). -/
def onlyExecutableStageIsStabilizeRounds (p : MagicQ.Protocol) : Bool :=
  p.ops.all (fun op => match op with
    | .inject _ _ _ _ _ _ => true
    | .stabilize _ _ _    => true
    | .postselect _       => true
    | .output _           => true
    | .discard _          => true
    | _                   => false)
  && (p.ops.filter isStabilizeOp).length == 1

/-- The `(carrier, rounds, codeFamily)` of the protocol's single `stabilize` stage. -/
def protocolStabilizeTarget? (p : MagicQ.Protocol) : Option (Nat × Nat × String) :=
  match p.ops.find? isStabilizeOp with
  | some (.stabilize carrier rounds _) =>
      let fam := p.ops.findSome? (fun op => match op with
        | .inject _ _ c code _ _ => if c == carrier then some (codeFamilyOf code) else none
        | _ => none)
      some (carrier, rounds, fam.getD "<no-inject>")
  | _ => none

/-- The DETECTOR NAME the protocol's `stabilize` stage emits (the abstract syndrome detector,
    used to wire postselection to a concrete syndrome-record detector). -/
def protocolStabilizeDetector? (p : MagicQ.Protocol) : Option String :=
  p.ops.findSome? (fun op => match op with | .stabilize _ _ detector => some detector | _ => none)

/-- **Executable lowering of the generic STABILIZE subset** to REAL syndrome-round QStab
    `prop`s.  Gated by `MagicQ.checkProtocol` + the stabilize-subset filter + a matching
    `SyndromeRoundWitness` for the carrier's code family — so it lowers ONLY when a witness
    exists (an unknown code REFUSES).  Rounds come from the protocol; supports from the
    witness.  POSTSELECTION is PRESERVED (same standard as the H_XY subset): when the protocol
    postselects, a concrete syndrome-record detector named with the `stabilize` detector (over
    ALL round measurement vars) is appended, then the mapped `mappedPostselectOps` — so a
    postselect resolves against a real detector (or the prior `MagicQ.checkProtocol` / `LS.check`
    rejects it).  An UN-postselected protocol lowers the bare syndrome-round chunk UNCHANGED.
    SEPARATE from the H_XY path, so full cultivation is NOT made to succeed. -/
def cultivationToExecutableStabilizeLSInΓ? (Γ : TypeChecker.TypedEnv) (p : MagicQ.Protocol) :
    Except LSError LoweredChunk := do
  if !onlyExecutableStageIsStabilizeRounds p then
    .error (.chunkNotImplemented
      "executable stabilize lowering supports only a SINGLE stabilize stage; this protocol has other / multiple executable stages")
  else
    match MagicQ.checkProtocol Γ p with
    | .error e => .error (.magicCheckFailed s!"MagicQ protocol high-level check failed: {repr e}")
    | .ok _ =>
        match protocolStabilizeTarget? p with
        | none => .error (.chunkNotImplemented "no stabilize stage found")
        | some (_carrier, rounds, fam) =>
            match findSyndromeRoundWitness? fam with
            | none => .error (.chunkNotImplemented
                s!"no syndrome-round witness for code family '{fam}'; cannot lower stabilize rounds (e.g. Gidney growth/escape supports are not sourced)")
            | some w =>
                let chunk := syndromeRoundsChunk { numQubits := w.numQubits, stabilizers := w.stabilizers
                                                   rounds := rounds, namePrefix := w.namePrefix }
                let postOps := mappedPostselectOps p
                let execProg : Program :=
                  if postOps.isEmpty then chunk.program   -- un-postselected: bare chunk, UNCHANGED
                  else
                    let stabDet  := (protocolStabilizeDetector? p).getD chunk.name
                    let nSynd    := rounds * w.stabilizers.length
                    -- a concrete SYNDROME-RECORD detector over all round measurement vars, named
                    -- with the MagicQ stabilize detector so its postselect resolves:
                    let syndromeDet : LSOp := .detector { name := stabDet, srcs := List.range nSynd, tags := ["syndrome"] }
                    { chunk.program with ops := chunk.program.ops ++ [syndromeDet] ++ postOps }
                let (qstab, sidecar) ← lowerCheckedWithExtract execProg
                return { qstab := qstab, sidecar := sidecar, geometry := chunk.geometry
                         obligations := (sidecar.obligations ++ chunk.obligations).eraseDups }

/-- **Executable stabilize lowering** (empty environment) → real syndrome-round QStab props,
    only when a `SyndromeRoundWitness` matches the carrier code family. -/
def cultivationToExecutableStabilizeLS? (p : MagicQ.Protocol) : Except LSError LoweredChunk :=
  cultivationToExecutableStabilizeLSInΓ? ⟨[]⟩ p

/-! ## §1. Checked examples (visible, honest recording). -/

/-- The default cultivation scaffold. -/
def cultLS : Program := cultivationScaffoldToLS MagicQ.Cultivation.defaultT

-- the H_XY double-check is recorded as a DEFERRED contract…
example : cultLS.contracts.any (fun c => decide (c.kind = .hxyDoubleCheck)) = true := by decide
-- …and the escape graft + transition contracts are recorded…
example : cultLS.contracts.any (fun c => decide (c.kind = .escapeGraft)) = true := by decide
example : cultLS.contracts.any (fun c => decide (c.kind = .escapeTransition)) = true := by decide
-- …and the early FULL postselection is carried as LS metadata:
example : cultLS.postselects.contains .full = true := by decide

-- CRUCIAL: the H_XY double-check is NOT silently represented as a Pauli measurement —
-- the scaffold emits NO `meas` op at all (every logical step is a stage/contract):
example : cultLS.ops.all (fun op => match op with | .meas _ _ _ => false | _ => true) = true := by decide

-- the stage markers read like the cultivation flow (inject … grow … escape … output):
example : cultLS.stages.map Prod.fst =
    ["inject", "check", "grow", "stabilize", "escape.graft", "stabilize",
     "escape.transition", "stabilize", "output"] := by decide

-- FIX 5: the SCAFFOLD has zero physical qubits and no measurements (it is not a circuit)…
example : cultLS.numQubits = 0 := by decide
example : (cultLS.ops.filterMap (fun op => match op with | .meas _ p _ => some p | _ => none)) = [] := by decide
-- …and the FULL default cultivation's executable lowering HONESTLY REFUSES — it is NOT in
-- the supported subset (it has growth/escape), so it never reaches the MagicQ gate:
example : onlyExecutableStageIsHxyCheck MagicQ.Cultivation.defaultT = false := by decide
example : (cultivationToExecutableLS? MagicQ.Cultivation.defaultT).toOption.isSome = false := by decide
example : (match cultivationToExecutableLS? MagicQ.Cultivation.defaultT with
            | .error (.chunkNotImplemented _) => true | _ => false) = true := by decide

/-! ## §2. The SUPPORTED executable SUBSET genuinely lowers (the d3 H_XY check). -/

/-- A minimal protocol in the supported subset: inject `|T⟩`, the H_XY double-check
    (the executable stage), output.  Its only EXECUTABLE stage is the d3 double-cat check. -/
def d3CheckProto : MagicQ.Protocol :=
  { name := "d3-check-only"
    ops := [ .inject .unitary .T 0 (.external "ColorCode(3)") 0 {}
           , .assumeLogicalCheck 0 { idx := 0, axis := .hxy } "cultivate.double-check"
               "transversal H_XY=(X+Y)/√2 double-check (realised by the d3 double-cat chunk)"
           , .output 0 ] }

-- the subset is RECOGNISED and the protocol PASSES MagicQ.checkProtocol, so lowering SUCCEEDS:
example : onlyExecutableStageIsHxyCheck d3CheckProto = true := by decide
example : MagicQ.checks? d3CheckProto = true := by decide
example : (cultivationToExecutableLS? d3CheckProto).toOption.isSome = true := by decide
-- the CANONICAL result is the RICH LoweredChunk — the real d3 circuit (13 qubits, 7 body
-- measurements), NOT a zero-qubit scaffold, with sidecar + obligations preserved:
example : (cultivationToExecutableLS? d3CheckProto).toOption.map (fun lc => lc.sidecar.numQubits) = some 13 := by decide
example : (cultivationToExecutableLS? d3CheckProto).toOption.map (fun lc => lc.sidecar.measKinds.length) = some 7 := by decide
example : (cultivationToExecutableLS? d3CheckProto).toOption.map (fun lc => lc.sidecar.countMeasKind .destructive) = some 7 := by decide
-- the returned obligations carry BOTH the d3 chunk's flow obligations AND the MagicQ-subset deferrals:
example : (cultivationToExecutableLS? d3CheckProto).toOption.map (fun lc =>
    lc.obligations.any (fun o => match o with | .contract c => decide (c.kind = .stageChunk "inject") | _ => false)) = some true := by decide
example : (cultivationToExecutableLS? d3CheckProto).toOption.map (fun lc =>
    lc.obligations.any (fun o => match o with | .flowSemantics _ => true | _ => false)) = some true := by decide
-- the LOW-LEVEL bare-program helper (internal) yields the genuinely-`LS.check`-ed 13-qubit program:
example : (cultivationToExecutableLSProgramInternal? ⟨[]⟩ d3CheckProto).toOption.map (·.numQubits) = some 13 := by decide
example : (cultivationToExecutableLSProgramInternal? ⟨[]⟩ d3CheckProto).toOption.map (fun pr => checks? pr) = some true := by decide

/-! ### Audit fixes — the gate ENFORCES validity and rejects multiplicity. -/

-- P0(#1): a SYNTACTICALLY-HXY protocol that FAILS MagicQ.checkProtocol (carrier 999 never
-- injected) is recognised by the syntactic filter, yet executable lowering REJECTS it
-- (magicCheckFailed) — invalid protocols cannot lower:
def bad999Proto : MagicQ.Protocol :=
  { name := "bad-999", ops := [ .assumeLogicalCheck 999 { idx := 0, axis := .hxy } "d" "j" ] }
example : onlyExecutableStageIsHxyCheck bad999Proto = true := by decide
example : MagicQ.checks? bad999Proto = false := by decide
example : (cultivationToExecutableLS? bad999Proto).toOption.isSome = false := by decide
example : (match cultivationToExecutableLS? bad999Proto with
            | .error (.magicCheckFailed _) => true | _ => false) = true := by decide

-- P0(#2): a VALID protocol with TWO H_XY checks must NOT silently lower to one d3 chunk —
-- multiplicity is rejected (NOT in the exact-single-HXY subset):
def twoHxyProto : MagicQ.Protocol :=
  { name := "two-hxy"
    ops := [ .inject .unitary .T 0 (.external "ColorCode(3)") 0 {}
           , .assumeLogicalCheck 0 { idx := 0, axis := .hxy } "d1" "check 1"
           , .assumeLogicalCheck 0 { idx := 0, axis := .hxy } "d2" "check 2"
           , .output 0 ] }
example : MagicQ.checks? twoHxyProto = true := by decide          -- it is a VALID protocol…
example : onlyExecutableStageIsHxyCheck twoHxyProto = false := by decide   -- …but NOT single-HXY…
example : (cultivationToExecutableLS? twoHxyProto).toOption.isSome = false := by decide  -- …so it does not lower
example : (match cultivationToExecutableLS? twoHxyProto with
            | .error (.chunkNotImplemented _) => true | _ => false) = true := by decide

-- a protocol with an UNSUPPORTED stage (a Pauli checkLogical) is NOT in the subset and refuses:
example : onlyExecutableStageIsHxyCheck
    { name := "x", ops := [ .checkLogical 0 { idx := 0, axis := .pauli (.Z) } "d" ] } = false := by decide

/-! ### Audit fixes — WITNESS/certificate, wrong-code refusal, postselection preservation. -/

-- P0(#1): a VALID, single-HXY protocol whose carrier code is NOT ColorCode(3) must NOT lower
-- to the Gidney d3 chunk — no witness matches its code family, so it REFUSES:
def d3CheckProtoOther : MagicQ.Protocol :=
  { name := "d3-check-othercode"
    ops := [ .inject .unitary .T 0 (.external "SomeOtherCode") 0 {}
           , .assumeLogicalCheck 0 { idx := 0, axis := .hxy } "cultivate.double-check" "double-check"
           , .output 0 ] }
example : MagicQ.checks? d3CheckProtoOther = true := by decide              -- valid protocol…
example : onlyExecutableStageIsHxyCheck d3CheckProtoOther = true := by decide  -- …syntactically single-HXY…
example : witnessMatchesProtocol d3HxyWitness d3CheckProtoOther = false := by decide  -- …but wrong code family…
example : (findExecutableWitness? d3CheckProtoOther).isSome = false := by decide
example : (cultivationToExecutableLS? d3CheckProtoOther).toOption.isSome = false := by decide  -- …so it does NOT lower
example : (match cultivationToExecutableLS? d3CheckProtoOther with
            | .error (.chunkNotImplemented _) => true | _ => false) = true := by decide

-- P0(#2): the d3 witness STRUCTURALLY CERTIFIES the d3 chunk — obs idx 0 ↔ the in/out
-- Y-parity boundary flows ↔ obsKey 0 ↔ readout vars [1,2,5,6] in the 7-var lowered dataflow:
example : witnessCertifiesChunk d3HxyWitness Gidney.d3DoubleCatCheck = true := by decide
example : witnessMatchesProtocol d3HxyWitness d3CheckProto = true := by decide
-- the certificate REJECTS a wrong chunk name / obsKey / logical support / out-of-range vars / wrong axis:
example : witnessCertifiesChunk { d3HxyWitness with chunkName := "nope" } Gidney.d3DoubleCatCheck = false := by decide
example : witnessCertifiesChunk { d3HxyWitness with obsKey := 7 } Gidney.d3DoubleCatCheck = false := by decide
example : witnessCertifiesChunk { d3HxyWitness with logicalSupport := [(0, .X)] } Gidney.d3DoubleCatCheck = false := by decide
example : witnessCertifiesChunk { d3HxyWitness with logicalReadoutVars := [99] } Gidney.d3DoubleCatCheck = false := by decide
example : witnessCertifiesChunk { d3HxyWitness with axisIsHxy := false } Gidney.d3DoubleCatCheck = false := by decide
-- the protocol matcher REJECTS a wrong observable idx / wrong axis / wrong code family:
example : witnessMatchesProtocol { d3HxyWitness with obsIdx := 1 } d3CheckProto = false := by decide
example : witnessMatchesProtocol { d3HxyWitness with axisIsHxy := false } d3CheckProto = false := by decide
example : witnessMatchesProtocol { d3HxyWitness with codeFamily := "OtherCode" } d3CheckProto = false := by decide
-- the successful lowering ATTACHES the positive structural certificate (flow soundness STILL deferred):
example : (cultivationToExecutableLS? d3CheckProto).toOption.map (fun lc =>
    lc.obligations.any (fun o => match o with | .structuralLogicalMeasCertified _ => true | _ => false)) = some true := by decide

-- P1(#3): MagicQ postselection is PRESERVED in executable lowering (NOT silently dropped),
-- AND P0/P1(#1): the syndromeEq Bool VALUE is preserved (`= false` and `= true` are DISTINCT).
def d3CheckProtoPS (v : Bool) : MagicQ.Protocol :=
  { name := "d3-check-postselected"
    ops := [ .inject .unitary .T 0 (.external "ColorCode(3)") 0 {}
           , .assumeLogicalCheck 0 { idx := 0, axis := .hxy } "cultivate.double-check" "double-check"
           , .postselect (.syndromeEq "cultivate.double-check" v)
           , .output 0 ] }
example : MagicQ.checks? (d3CheckProtoPS false) = true := by decide
example : (cultivationToExecutableLS? (d3CheckProtoPS false)).toOption.isSome = true := by decide
-- the postselect policy is carried into the sidecar WITH its Boolean value (not dropped):
example : (cultivationToExecutableLS? (d3CheckProtoPS false)).toOption.map (fun lc => lc.sidecar.postselects)
    = some [PostPolicy.byDetectorValue "cultivate.double-check" false] := by decide
example : (cultivationToExecutableLS? (d3CheckProtoPS true)).toOption.map (fun lc => lc.sidecar.postselects)
    = some [PostPolicy.byDetectorValue "cultivate.double-check" true] := by decide
-- the `= true` and `= false` postselections are DISTINCT sidecar values (the Bool is preserved):
example : (PostPolicy.byDetectorValue "d" false) ≠ (PostPolicy.byDetectorValue "d" true) := by decide
-- the un-postselected protocol genuinely has an EMPTY postselect sidecar (no fabrication):
example : (cultivationToExecutableLS? d3CheckProto).toOption.map (fun lc => lc.sidecar.postselects) = some [] := by decide

-- P1(#2): MagicQ `taggedDetectors` lowers as a detector-NAME postselect (NOT an LS tag), so a
-- valid single-HXY protocol with `taggedDetectors "cultivate.double-check"` lowers CONSISTENTLY
-- (it passes MagicQ AND LS — never a later LS `unknownTag`):
def d3CheckProtoTagged : MagicQ.Protocol :=
  { name := "d3-check-tagged"
    ops := [ .inject .unitary .T 0 (.external "ColorCode(3)") 0 {}
           , .assumeLogicalCheck 0 { idx := 0, axis := .hxy } "cultivate.double-check" "double-check"
           , .postselect (.taggedDetectors "cultivate.double-check")
           , .output 0 ] }
example : MagicQ.checks? d3CheckProtoTagged = true := by decide
example : (cultivationToExecutableLS? d3CheckProtoTagged).toOption.map (fun lc => lc.sidecar.postselects)
    = some [PostPolicy.byDetector "cultivate.double-check"] := by decide

-- P0(#3): the structural logical-measurement certificate is MACHINE-READABLE (not just text)
-- and the structural OBSERVABLE-REALISATION bridge holds (readout vars index real QStab props):
example : readoutVarsAreProps (lower Gidney.d3DoubleCatBodyProgram) [1, 2, 5, 6] = true := by decide
example : readoutVarsAreProps (lower Gidney.d3DoubleCatBodyProgram) [99] = false := by decide
example : (cultivationToExecutableLS? d3CheckProto).toOption.map (fun lc =>
    lc.obligations.any (fun o => match o with
      | .structuralLogicalMeasCertified d =>
          decide (d.codeFamily = "ColorCode(3)") && decide (d.obsIdx = 0) && d.axisIsHxy
            && decide (d.chunkName = "d3-double-cat-check") && (d.readoutVars == [1, 2, 5, 6]) && (d.obsKey == 0)
      | _ => false)) = some true := by decide

-- FIX 5: full cultivation's MISSING stages are EXPLICITLY recorded as deferred contracts,
-- so the refusal is honest about WHAT is unimplemented (grow / stabilize / graft / transition):
example : cultLS.contracts.any (fun c => decide (c.kind = .stageChunk "grow")) = true := by decide
example : cultLS.contracts.any (fun c => decide (c.kind = .stageChunk "stabilize")) = true := by decide

/-! ### P1(#4) — the generic STABILIZE subset lowers to REAL syndrome-round QStab props. -/

/-- A standalone stabilize-only protocol on a witnessed code (RepCode(3)). -/
def stabilizeProto (rounds : Nat) : MagicQ.Protocol :=
  { name := "stabilize-only"
    ops := [ .inject .unitary .T 0 (.external "RepCode(3)") 0 {}
           , .stabilize 0 rounds "stab.round"
           , .output 0 ] }
-- it is a valid, single-stabilize protocol with a matching syndrome-round witness, so it lowers…
example : MagicQ.checks? (stabilizeProto 2) = true := by decide
example : onlyExecutableStageIsStabilizeRounds (stabilizeProto 2) = true := by decide
example : (cultivationToExecutableStabilizeLS? (stabilizeProto 2)).toOption.isSome = true := by decide
-- …to REAL QStab props: 2 rounds × 2 stabilizers = 4 `.prop` measurements:
example : (cultivationToExecutableStabilizeLS? (stabilizeProto 2)).toOption.map (fun lc => lc.qstab.dataflow.length) = some 4 := by decide
example : (cultivationToExecutableStabilizeLS? (stabilizeProto 3)).toOption.map (fun lc => lc.qstab.dataflow.length) = some 6 := by decide
-- a stabilize protocol on an UNWITNESSED code REFUSES (no fake lowering):
def stabilizeProtoUnknown : MagicQ.Protocol :=
  { name := "stabilize-unknown"
    ops := [ .inject .unitary .T 0 (.external "UnknownCode") 0 {}, .stabilize 0 2 "s", .output 0 ] }
example : MagicQ.checks? stabilizeProtoUnknown = true := by decide
example : (cultivationToExecutableStabilizeLS? stabilizeProtoUnknown).toOption.isSome = false := by decide
example : (match cultivationToExecutableStabilizeLS? stabilizeProtoUnknown with
            | .error (.chunkNotImplemented _) => true | _ => false) = true := by decide
-- and FULL cultivation is NOT made to succeed via the stabilize path (it has growth/escape too):
example : onlyExecutableStageIsStabilizeRounds MagicQ.Cultivation.defaultT = false := by decide
example : (cultivationToExecutableStabilizeLS? MagicQ.Cultivation.defaultT).toOption.isSome = false := by decide

-- P1(#1): the STABILIZE subset PRESERVES MagicQ postselection (same standard as the H_XY subset),
-- including the syndromeEq Boolean VALUE — it is NOT silently dropped:
def stabilizeProtoPS (v : Bool) : MagicQ.Protocol :=
  { name := "stabilize-postselected"
    ops := [ .inject .unitary .T 0 (.external "RepCode(3)") 0 {}
           , .stabilize 0 2 "stab.round"
           , .postselect (.syndromeEq "stab.round" v)
           , .output 0 ] }
example : MagicQ.checks? (stabilizeProtoPS false) = true := by decide
example : (cultivationToExecutableStabilizeLS? (stabilizeProtoPS false)).toOption.isSome = true := by decide
-- the postselect (with its Bool value) is carried into the sidecar, mapped to the concrete syndrome detector:
example : (cultivationToExecutableStabilizeLS? (stabilizeProtoPS false)).toOption.map (fun lc => lc.sidecar.postselects)
    = some [PostPolicy.byDetectorValue "stab.round" false] := by decide
example : (cultivationToExecutableStabilizeLS? (stabilizeProtoPS true)).toOption.map (fun lc => lc.sidecar.postselects)
    = some [PostPolicy.byDetectorValue "stab.round" true] := by decide
-- the real syndrome rounds are still present (4 props), now plus the syndrome-record detector:
example : (cultivationToExecutableStabilizeLS? (stabilizeProtoPS false)).toOption.map (fun lc => lc.qstab.dataflow.length) = some 4 := by decide
-- an UN-postselected stabilize lowering is UNCHANGED (empty postselect sidecar):
example : (cultivationToExecutableStabilizeLS? (stabilizeProto 2)).toOption.map (fun lc => lc.sidecar.postselects) = some [] := by decide
-- a postselect on an UNKNOWN detector cannot silently succeed — it fails the MagicQ check, so lowering REFUSES:
def stabilizeProtoBadPS : MagicQ.Protocol :=
  { name := "stabilize-bad-ps"
    ops := [ .inject .unitary .T 0 (.external "RepCode(3)") 0 {}
           , .stabilize 0 2 "stab.round"
           , .postselect (.syndromeEq "nonexistent" false)
           , .output 0 ] }
example : MagicQ.checks? stabilizeProtoBadPS = false := by decide
example : (cultivationToExecutableStabilizeLS? stabilizeProtoBadPS).toOption.isSome = false := by decide
example : (match cultivationToExecutableStabilizeLS? stabilizeProtoBadPS with
            | .error (.magicCheckFailed _) => true | _ => false) = true := by decide

/-! ## §3. 15-to-1 distillation is HONEST: representable / high-level-checkable, but NOT
       yet LS/QStab-lowered (no fake distillation lowering). -/

-- MagicQ REPRESENTS and high-level-CHECKS the Bravyi–Kitaev 15-to-1 protocol…
example : MagicQ.checks? MagicQ.ReedMuller15.rm15To1 = true := by decide
-- …but distillation has NO executable LS chunk, so it is NOT in the supported subset and the
-- executable lowering REFUSES (no fake 15-to-1 LS/QStab lowering is ever returned):
example : onlyExecutableStageIsHxyCheck MagicQ.ReedMuller15.rm15To1 = false := by decide
example : (cultivationToExecutableLS? MagicQ.ReedMuller15.rm15To1).toOption.isSome = false := by decide
example : (cultivationToExecutableLSSubset? MagicQ.ReedMuller15.rm15To1).toOption.isSome = false := by decide
-- the scaffold records the syndrome-measure (15-to-1) chunk as an EXPLICIT deferred contract
-- (never silently lowered):
example : (cultivationScaffoldToLS MagicQ.ReedMuller15.rm15To1).contracts.any
    (fun c => decide (c.kind = .custom "measure-syndrome")) = true := by decide

end Compiler.LS
