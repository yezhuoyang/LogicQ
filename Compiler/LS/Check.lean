/-
  Compiler.LS.Check — the lattice-surgery IR checker.

  Structural / SSA validity of an LS program, plus an HONEST checked summary:
    * SSA order — every `parity`/`detector`/`observable`/postselect references only
      ALREADY-bound measurement vars (and `meas`/`parity` are the only binders);
    * sparse-Pauli support validity (no identity factor, no duplicate qubit, non-empty
      for a measurement, in range for the patch);
    * postselect references a KNOWN detector name / stage tag;
    * flow contracts are structurally well-formed;
    * detector determinism is reported ONLY as it follows from the QStab all-`+1`
      (noiseless) classical evaluation — never asserted;
    * deferred obligations (contracts, semantic flow soundness, fault/decoder) are
      collected EXPLICITLY — none silently "certified".

  No semantic surgery/flow/fault-distance soundness is claimed here.  Mathlib-free.
-/
import Compiler.LS.Syntax
import Compiler.LS.Cert

namespace Compiler.LS
open QStab Physical

/-! ## §1. Errors and deferred obligations. -/

/-- Failures an LS check can raise (all carry structured, machine-readable data). -/
inductive LSError
  | emptyMeasurement                                    -- a `meas` with no factors
  | identityFactor      (P : SPauli)                    -- a sparse Pauli with an `I` factor
  | duplicateQubit      (P : SPauli)                    -- a sparse Pauli touching a qubit twice
  | sparseOutOfRange    (P : SPauli) (bound : Nat)      -- a measured factor qubit ≥ numQubits
  | gateOutOfRange      (q : PQubit) (bound : Nat)      -- a prep/Clifford qubit ≥ numQubits
  | varOutOfScope       (v : QVar) (bound : Nat)        -- a parity/detector/observable reads an unbound var
  | unknownDetector     (name : String)                 -- postselect references an unproduced detector/tag
  | flowMalformed       (tag : String)                  -- a flow's input/output sparse Pauli is malformed
  | flowSparseOutOfRange (tag : String) (P : SPauli) (bound : Nat)  -- a flow's input/output touches a qubit ≥ numQubits
  | flowVarOutOfScope   (tag : String) (v : QVar) (bound : Nat)  -- a flow references an unbound var
  | deadQubit           (q : PQubit)                    -- a gate/measurement uses a qubit consumed by a prior destructive readout
  | destructiveNotSingleQubit (P : SPauli)              -- a destructive readout must measure exactly one qubit (no multi-qubit destructive model)
  | noPhysicalWitness                                   -- a logical PPM measurement lowered WITHOUT a physical Pauli witness
  | ppmNotNative        (factors : Nat)                 -- a PPM measurement that is not 1-/2-body (native surgery discipline)
  | certWitnessMismatch (witness : SPauli) (cert : QStab.PauliString)  -- the physical witness does not densify to the cert's measured parity
  | chunkNotImplemented (note : String)                 -- a real executable chunk lowering is NOT yet built (honest refusal, not a fake program)
  | magicCheckFailed    (reason : String)               -- the source MagicQ protocol FAILED its high-level `MagicQ.checkProtocol` (so it must not lower)
  | other               (msg : String)
  deriving Repr

/-- MACHINE-READABLE data of a STRUCTURAL logical-measurement bridge: a logical observable
    (`obsIdx`/`axisIsHxy`) on a carrier code (`codeFamily`) is tied to a chunk (`chunkName`)
    by its boundary flows (`inFlowTag`/`outFlowTag`, `obsKey`, `logicalSupport`) and the body
    measurement vars (`readoutVars`) realising it.  This is a STRUCTURAL match only — it is
    NOT a stabilizer-flow soundness proof (that stays the deferred `flowSemantics`). -/
structure LogicalMeasCertData where
  codeFamily     : String
  obsIdx         : Nat
  axisIsHxy      : Bool
  chunkName      : String
  inFlowTag      : String
  outFlowTag     : String
  logicalSupport : SPauli
  obsKey         : Int
  readoutVars    : List QVar
  deriving Repr, DecidableEq

/-- A DEFERRED LS obligation, surfaced in the checked summary — never discharged. -/
inductive Obligation
  | contract      (c : DeferredContract)     -- a deferred LS contract (H_XY double-check, escape graft/transition, stage chunk…)
  | flowSemantics (tag : String)             -- FULL stabilizer-flow soundness of a flow (only its structure is checked)
  | fault         (f : FaultObligations)     -- code distance / fault distance / decoder — all deferred (reused `LS.FaultObligations`)
  | notExtractable (P : QStab.PauliString) (reason : String)  -- this physical measurement is NOT lowerable by current QStab2QClifford schemes
  | gidneyFlowImportPending (source flag : String)  -- the gen-INFERRED stabilizer flows of a Gidney chunk are not imported (provenance + flow flag recorded)
  | flowCompositionDeferred (note : String)         -- composing chunks matched flow interfaces STRUCTURALLY only; semantic flow soundness across the seam is deferred
  | structuralLogicalMeasCertified (cert : LogicalMeasCertData)  -- POSITIVE, MACHINE-READABLE structural bridge: a logical observable tied to a chunk's boundary flows + lowered QStab readout vars (NOT a stabilizer-flow proof — `flowSemantics` stays deferred)
  deriving Repr, DecidableEq

/-! ## §2. The checked summary. -/

/-- The HONEST checked summary of an LS program: the sidecar annotations, the flow
    contracts, the deferred obligations, and the per-detector CLASSICAL determinism
    verdict (true ⇔ the detector's noiseless all-`+1` parity is `+1`, i.e. no event). -/
structure Checked where
  numQubits             : Nat
  vars                  : Nat                       -- number of bound QStab classical vars
  detectors             : List DetectorAnn          -- full tagged detector annotations (tags/coords preserved)
  observables           : List (String × List QVar)
  postselects           : List PostPolicy
  stages                : List (String × String)
  flows                 : List Flow
  obligations           : List Obligation
  detectorDeterministic : List (String × Bool)      -- (name, classical-noiseless-determinism); the FULL stabilizer determinism stays deferred
  measKinds             : List (QVar × MeasKind)     -- per measurement VAR: did it come from an MPP product or a destructive readout (preserved through lowering)
  deriving Repr

/-! ## §3. Per-op checks. -/

/-- Internal threaded state of the SSA / scope check. -/
structure CheckState where
  nVars       : Nat                       := 0
  detNames    : List String               := []
  detTags     : List String               := []   -- DETECTOR tags (NOT stage tags) — the tagged-postselection scope
  detectors   : List DetectorAnn          := []
  observables : List (String × List QVar) := []
  postselects : List PostPolicy           := []
  contracts   : List DeferredContract     := []
  measKinds   : List (QVar × MeasKind)    := []
  dead        : List PQubit               := []   -- qubits consumed by a destructive readout (until re-prepared)
  deriving Inhabited

/-- A prep/Clifford qubit must be in range. -/
def inRangeQ (n q : Nat) : Except LSError Unit :=
  if q < n then .ok () else .error (.gateOutOfRange q n)

/-- A qubit a GATE or MEASUREMENT touches must be in range AND LIVE (not consumed by a
    prior destructive readout). -/
def liveQ (n : Nat) (st : CheckState) (q : PQubit) : Except LSError Unit :=
  if q ≥ n then .error (.gateOutOfRange q n)
  else if st.dead.contains q then .error (.deadQubit q)
  else .ok ()

/-- Re-initialise a qubit (a `prep`): it becomes LIVE again. -/
def CheckState.revive (st : CheckState) (q : PQubit) : CheckState :=
  { st with dead := st.dead.filter (· != q) }

/-- Mark a qubit DEAD (a destructive readout consumes it). -/
def CheckState.kill (st : CheckState) (q : PQubit) : CheckState :=
  if st.dead.contains q then st else { st with dead := st.dead ++ [q] }

/-- Every qubit a measurement touches must be LIVE (range is checked by `checkSPauliMeas`). -/
def ensureLiveSPauli (st : CheckState) : SPauli → Except LSError Unit
  | []        => .ok ()
  | f :: rest => if st.dead.contains f.1 then .error (.deadQubit f.1) else ensureLiveSPauli st rest

/-- Every referenced var must already be bound (`< bound`). -/
def checkVars (bound : Nat) : List QVar → Except LSError Unit
  | []        => .ok ()
  | v :: rest => if v < bound then checkVars bound rest else .error (.varOutOfScope v bound)

/-- A measured sparse Pauli must be non-empty, identity-free, duplicate-free, in range. -/
def checkSPauliMeas (n : Nat) (P : SPauli) : Except LSError Unit :=
  if P.isEmpty then .error .emptyMeasurement
  else if !P.noIdentity then .error (.identityFactor P)
  else if !P.nodupQubits then .error (.duplicateQubit P)
  else if !(P.inRange n) then .error (.sparseOutOfRange P n)
  else .ok ()

/-- A postselection PREDICATE is in SCOPE iff every atom references a produced detector
    name / detector tag.  Only scope is checked — the predicate's Boolean VALUE (`and`/
    `or`/`not`) is a runtime/decoder fact, never evaluated here.  Structural recursion over
    the binary predicate tree. -/
def checkPred (st : CheckState) : PostPred → Except LSError Unit
  | .detector name => if st.detNames.contains name then .ok () else .error (.unknownDetector name)
  | .tag tag       => if st.detTags.contains tag then .ok () else .error (.unknownDetector tag)
  | .and p q       => do checkPred st p; checkPred st q
  | .or p q        => do checkPred st p; checkPred st q
  | .not p         => checkPred st p

/-- A postselection policy must reference a known DETECTOR name (`byDetector`) or a
    known DETECTOR tag (`byTag`); a `byPred` must reference only known atoms.  Stage tags
    do NOT satisfy detector-tag postselection. -/
def checkPost (st : CheckState) : PostPolicy → Except LSError Unit
  | .full            => .ok ()
  | .byDetector name        => if st.detNames.contains name then .ok () else .error (.unknownDetector name)
  | .byDetectorValue name _ => if st.detNames.contains name then .ok () else .error (.unknownDetector name)
  | .byTag tag              => if st.detTags.contains tag then .ok () else .error (.unknownDetector tag)
  | .byPred p               => checkPred st p

/-- Check one op, threading the SSA / annotation / qubit-LIVENESS state.  A `prep`
    re-initialises (revives) its qubit; a Clifford/measurement requires its qubits LIVE; a
    DESTRUCTIVE single-qubit readout consumes (kills) its qubit (an MPP product leaves its
    qubits live). -/
def checkOp (n : Nat) (st : CheckState) : LSOp → Except LSError CheckState
  | .prepZero q  => do inRangeQ n q; return st.revive q
  | .prepPlus q  => do inRangeQ n q; return st.revive q
  | .h q         => do liveQ n st q; return st
  | .s q         => do liveQ n st q; return st
  | .sDag q      => do liveQ n st q; return st
  | .x q         => do liveQ n st q; return st
  | .z q         => do liveQ n st q; return st
  | .cnot c t    => do liveQ n st c; liveQ n st t; return st
  | .cz a b      => do liveQ n st a; liveQ n st b; return st
  | .meas _ P k  => do
      checkSPauliMeas n P
      ensureLiveSPauli st P                          -- every measured qubit must be LIVE
      match k, P with
      | .destructive, [f] =>                          -- a destructive readout consumes its single qubit
          return { (st.kill f.1) with nVars := st.nVars + 1, measKinds := st.measKinds ++ [(st.nVars, k)] }
      | .destructive, _   => .error (.destructiveNotSingleQubit P)  -- no multi-qubit destructive model
      | .mpp, _           =>                          -- a product measurement is non-demolition (qubits survive)
          return { st with nVars := st.nVars + 1, measKinds := st.measKinds ++ [(st.nVars, k)] }
  | .parity srcs => do checkVars st.nVars srcs; return { st with nVars := st.nVars + 1 }
  | .detector ann => do
      checkVars st.nVars ann.srcs
      return { st with detectors := st.detectors ++ [ann], detNames := st.detNames ++ [ann.name], detTags := st.detTags ++ ann.tags }
  | .observable name srcs => do
      checkVars st.nVars srcs
      return { st with observables := st.observables ++ [(name, srcs)] }
  | .postselect pol => do
      checkPost st pol
      return { st with postselects := st.postselects ++ [pol] }
  | .stage _ _   => .ok st
  | .tick        => .ok st
  | .deferred c  => .ok { st with contracts := st.contracts ++ [c] }

/-- Every flow var must be in scope (`< bound`), reported with the flow's tag. -/
def checkFlowVars (tag : String) (bound : Nat) : List QVar → Except LSError Unit
  | []        => .ok ()
  | v :: rest => if v < bound then checkFlowVars tag bound rest else .error (.flowVarOutOfScope tag v bound)

/-- A flow contract is structurally well-formed: identity-free and duplicate-free
    input & output sparse Paulis, BOTH in range for the `numQubits`-qubit patch, and all
    carried vars in scope.  An EMPTY input or output is allowed (a boundary interface). -/
def checkFlow (numQubits bound : Nat) (fl : Flow) : Except LSError Unit :=
  if !fl.input.wf || !fl.output.wf then .error (.flowMalformed fl.tag)
  else if !(fl.input.inRange numQubits) then .error (.flowSparseOutOfRange fl.tag fl.input numQubits)
  else if !(fl.output.inRange numQubits) then .error (.flowSparseOutOfRange fl.tag fl.output numQubits)
  else checkFlowVars fl.tag bound fl.vars

/-! ## §4. Detector determinism via the QStab all-`+1` evaluation. -/

/-- The noiseless (all-`+1`) classical value of a detector's parity over the dataflow:
    `XOR` of its source vars under the all-`false` outcomes. -/
def detectorNoiselessXor (df : QStab.Prog) (srcs : List QVar) : Bool :=
  srcs.foldl (fun b i => xor b (QStab.evalVar df (fun _ => false) i)) false

/-- A detector is CLASSICALLY deterministic iff: the dataflow is WELL-FORMED, every
    referenced var is IN RANGE (`< df.length`), AND its noiseless parity is `+1`
    (false = no event).  The wf / in-range guards make this NON-VACUOUS: a malformed
    program or an out-of-range readout returns `false` (NOT "deterministic"), instead
    of silently reading `QStab.evalVar`'s default-`false` for missing vars.  This is
    the only determinism this layer genuinely checks — the full stabilizer-level
    determinism is a deferred semantic obligation. -/
def detectorDeterministic? (df : QStab.Prog) (srcs : List QVar) : Bool :=
  df.wf && srcs.all (fun v => decide (v < df.length)) && !detectorNoiselessXor df srcs

/-! ## §5. The whole-program checker. -/

/-- **Check an LS program.**  Threads `checkOp` (SSA + scope + sparse-Pauli), checks
    every flow's structure, and assembles the HONEST summary: sidecar annotations,
    flows, the per-detector classical-determinism verdict, and the explicitly-deferred
    obligations (contracts + per-flow semantic soundness + the always-deferred
    distance/fault-distance/decoder fault obligation). -/
def check (p : Program) : Except LSError Checked := do
  let st ← p.ops.foldlM (checkOp p.numQubits) ({} : CheckState)
  p.flows.forM (checkFlow p.numQubits st.nVars)
  let df := p.dataflow
  return {
    numQubits   := p.numQubits
    vars        := st.nVars
    detectors   := st.detectors
    observables := st.observables
    postselects := st.postselects
    stages      := p.stages
    flows       := p.flows
    obligations := st.contracts.map Obligation.contract
                ++ p.flows.map (fun fl => Obligation.flowSemantics fl.tag)
                ++ [Obligation.fault {}]
    detectorDeterministic := st.detectors.map (fun d => (d.name, detectorDeterministic? df d.srcs))
    measKinds   := st.measKinds }

/-- Convenience: does the LS program check? -/
def checks? (p : Program) : Bool := (check p).toOption.isSome

/-- How many of the checked measurements had the given `MeasKind` (MPP vs destructive)
    — the measurement-kind information PRESERVED through the lowering sidecar. -/
def Checked.countMeasKind (c : Checked) (k : MeasKind) : Nat :=
  (c.measKinds.filter (fun p => decide (p.2 = k))).length

/-! ## §6. Checked examples. -/

/-- A small valid surgery readout: two `ZZ` measurements, a TAGGED detector over both,
    an observable, and a postselect by detector name AND by detector tag. -/
def goodProg : Program :=
  { numQubits := 2
    ops := [ .meas (some ⟨0, 0⟩) [(0, .Z), (1, .Z)]                         -- c0
           , .meas (some ⟨1, 0⟩) [(0, .Z), (1, .Z)]                         -- c1
           , .detector { name := "d0", srcs := [0, 1], tags := ["color"] }   -- d0 = c0 ⊕ c1, tagged
           , .observable "o0" [0]
           , .postselect (.byDetector "d0")
           , .postselect (.byTag "color") ] }

-- it checks, and the detector is CLASSICALLY deterministic (noiseless ⇒ no event):
example : checks? goodProg = true := by decide
example : (check goodProg).toOption.map (·.detectorDeterministic) = some [("d0", true)] := by decide
-- detector TAGS are preserved in the sidecar:
example : (check goodProg).toOption.map (fun c => c.detectors.map (·.tags)) = some [["color"]] := by decide
-- the distance/fault-distance/decoder obligation is recorded (honestly deferred):
example : (check goodProg).toOption.map (fun c => c.obligations.any
            (fun o => match o with | .fault _ => true | _ => false)) = some true := by decide

/-! ### FIX 1 — detector tags are DETECTOR tags, not stage tags. -/

-- a postselect on a known DETECTOR tag is ACCEPTED:
example : checks? { numQubits := 1, ops :=
    [ .meas none [(0, .Z)], .detector { name := "d", srcs := [0], tags := ["t"] }, .postselect (.byTag "t") ] } = true := by decide
-- an UNKNOWN tag is rejected:
example : checks? { numQubits := 1, ops :=
    [ .meas none [(0, .Z)], .detector { name := "d", srcs := [0], tags := ["t"] }, .postselect (.byTag "nope") ] } = false := by decide
-- a STAGE tag does NOT satisfy detector-tag postselection (stage "t" then byTag "t" ⇒ REJECTED):
example : checks? { numQubits := 1, ops :=
    [ .meas none [(0, .Z)], .stage "t" "marker", .postselect (.byTag "t") ] } = false := by decide

/-! ### FIX 2 — detector determinism is NON-VACUOUS (wf + in-range guarded). -/

-- a well-formed in-range detector IS deterministic under noiseless:
example : detectorDeterministic? [.prop none (ofString "Z")] [0] = true := by decide
-- an OUT-OF-RANGE readout is NOT "deterministic" (no silent default-false):
example : detectorDeterministic? [.prop none (ofString "Z")] [5] = false := by decide
-- a MALFORMED (non-wf) dataflow is NOT "deterministic" (forward parity reference):
example : detectorDeterministic? [.parity [0]] [0] = false := by decide

/-! ### FIX 4 — a structurally-valid flow still emits a semantic-flow obligation. -/

def flowProg : Program :=
  { numQubits := 1
    ops := [ .meas none [(0, .Z)] ]
    flows := [ { tag := "f", input := [(0, .Z)], output := [(0, .Z)], vars := [0], status := .structural } ] }

example : checks? flowProg = true := by decide
-- even though the flow's `status` is `.structural`, the SEMANTIC soundness obligation is recorded:
example : (check flowProg).toOption.map (fun c => c.obligations.any
            (fun o => match o with | .flowSemantics t => t == "f" | _ => false)) = some true := by decide

/-! ### Standing rejection tests (updated for `DetectorAnn`). -/

-- detector referencing a FUTURE var is rejected:
example : checks? { numQubits := 1, ops := [ .meas none [(0, .Z)], .detector { name := "d", srcs := [5] } ] } = false := by decide
-- postselect on an UNKNOWN detector is rejected:
example : checks? { numQubits := 1, ops := [ .meas none [(0, .Z)], .postselect (.byDetector "nope") ] } = false := by decide
-- empty / identity-only measurement is rejected:
example : checks? { numQubits := 1, ops := [ .meas none [] ] } = false := by decide

/-! ### Task 2 — FLOW RANGE CHECKING (input/output qubits must be in the patch). -/

-- a flow touching qubit 999 in a 13-qubit program is REJECTED (out of range)…
example : checks? { numQubits := 13, ops := [ .meas none [(0, .Z)] ], flows := [ { tag := "oob", input := [(999, .Z)], output := [(0, .Z)], vars := [0] } ] } = false := by decide
-- …likewise an out-of-range OUTPUT…
example : checks? { numQubits := 13, ops := [ .meas none [(0, .Z)] ], flows := [ { tag := "oob", input := [(0, .Z)], output := [(999, .Z)], vars := [0] } ] } = false := by decide
-- …but an in-range flow is fine, and an EMPTY input/output (a boundary interface) is allowed:
example : checks? { numQubits := 13, ops := [ .meas none [(0, .Z)] ], flows := [ { tag := "in", input := [(0, .Z)], output := [], vars := [0] } ] } = true := by decide
example : checks? { numQubits := 13, ops := [ .meas none [(0, .Z)] ], flows := [ { tag := "out", input := [], output := [(0, .Z)], vars := [0] } ] } = true := by decide

/-! ### Task 3 — DESTRUCTIVE-MEASUREMENT QUBIT LIFECYCLE. -/

-- `MX q; H q` is REJECTED: the destructive readout consumed qubit 0, so the later H is dead-qubit use:
example : checks? { numQubits := 1, ops := [ .meas none [(0, .X)] .destructive, .h 0 ] } = false := by decide
-- `MX q; prepPlus q; H q` is ACCEPTED: re-preparation revives qubit 0:
example : checks? { numQubits := 1, ops := [ .meas none [(0, .X)] .destructive, .prepPlus 0, .h 0 ] } = true := by decide
-- a DESTRUCTIVE multi-qubit measurement is REJECTED (no multi-qubit destructive model):
example : checks? { numQubits := 2, ops := [ .meas none [(0, .X), (1, .X)] .destructive ] } = false := by decide
-- a destructive readout marks the qubit dead for a later GATE and a later MEASUREMENT alike:
example : checks? { numQubits := 1, ops := [ .meas none [(0, .X)] .destructive, .meas none [(0, .X)] ] } = false := by decide
-- an MPP product measurement is NON-demolition: its qubits stay live for reuse:
example : checks? { numQubits := 1, ops := [ .meas none [(0, .X)] .mpp, .h 0 ] } = true := by decide

/-! ### Task 4 — GENERAL postselection PREDICATES (Boolean over detector/tag atoms). -/

-- a predicate over KNOWN detector + tag atoms (with `and`/`or`/`not`) is ACCEPTED:
example : checks? { numQubits := 1, ops :=
    [ .meas none [(0, .Z)], .detector { name := "d", srcs := [0], tags := ["t"] }
    , .postselect (.byPred (.and (.detector "d") (.not (.tag "t")))) ] } = true := by decide
-- a predicate over an UNKNOWN detector atom is REJECTED (scope is enforced through the tree):
example : checks? { numQubits := 1, ops :=
    [ .meas none [(0, .Z)], .detector { name := "d", srcs := [0] }
    , .postselect (.byPred (.or (.detector "d") (.detector "nope"))) ] } = false := by decide
-- an UNKNOWN tag atom nested under a `not` is REJECTED:
example : checks? { numQubits := 1, ops :=
    [ .meas none [(0, .Z)], .detector { name := "d", srcs := [0], tags := ["t"] }
    , .postselect (.byPred (.not (.tag "nope"))) ] } = false := by decide
-- the n-ary `all`/`any` smart constructors fold into the same checked predicate:
example : ((PostPred.all [.detector "d", .tag "t"]).map (fun p => checks? { numQubits := 1, ops :=
    [ .meas none [(0, .Z)], .detector { name := "d", srcs := [0], tags := ["t"] }, .postselect (.byPred p) ] }))
    = some true := by decide
example : checks? { numQubits := 1, ops := [ .meas none [(0, .I)] ] } = false := by decide
-- duplicate qubit in a measurement is rejected:
example : checks? { numQubits := 2, ops := [ .meas none [(0, .Z), (0, .X)] ] } = false := by decide
-- an out-of-range factor / gate qubit is rejected:
example : checks? { numQubits := 1, ops := [ .meas none [(3, .Z)] ] } = false := by decide
example : checks? { numQubits := 1, ops := [ .h 3 ] } = false := by decide
-- a detector over PRIOR vars is accepted:
example : checks? { numQubits := 1, ops := [ .meas none [(0, .Z)], .detector { name := "d", srcs := [0] } ] } = true := by decide

end Compiler.LS
