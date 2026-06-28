/-
  Compiler.LS.Syntax — the lattice-surgery IR (LSIR) data layer.

  LSIR is the MISSING surgery-schedule / certificate layer that sits between the
  logical IRs (PPM, MagicQ) and the physical stabilizer-measurement IR (QStab):

      MagicQ / PPM  →  LS  →  QStab.StabilizerProg + detector/observable/postselect
                                sidecar  →  QStab2QClifford  →  physical execution

  LSIR is NOT another QStab.  QStab OWNS the physical Pauli measurements, the
  Clifford/prep/feed-forward stabilizer instructions, and the SSA classical parity
  dataflow.  LSIR OWNS the surgical/control structure QStab intentionally does not:
  patches/carriers, surgery rounds/slots, logical→physical measurement certificates,
  stabilizer-flow contracts, detector/observable annotations (parity expressions over
  measurement vars), postselection policy, and deferred fault/decoder/quality
  obligations.

  This is an EXPLICIT AST (data, no notation/macros).  It REUSES the existing
  vocabulary — `Physical.Pauli`/`PQubit`, `QStab.QVar`/`Sched`/`PauliString` — and
  defines only the genuinely new surgery-metadata structure.  Mathlib-free.

  HONESTY: nothing here claims Gidney exactness, detector/flow soundness, or
  fault-distance correctness.  Those are explicit deferred obligations (`Check.lean`).
-/
import QStab.Syntax

namespace Compiler.LS
open QStab Physical

/-! ## §1. Sparse Pauli products (LS-level), and their dense `QStab` form. -/

/-- A SPARSE physical Pauli product: a list of `(physical qubit, non-identity Pauli)`
    factors.  Sparse (unlike `QStab.PauliString`, which is dense over `0…n-1`) because
    surgery measurements touch few of the many patch qubits. -/
abbrev SPauli := List (PQubit × Pauli)

/-- A qubit list has no duplicate (Mathlib-free, `Bool`). -/
private def nodupB : List PQubit → Bool
  | []        => true
  | q :: rest => !rest.contains q && nodupB rest

/-- No identity factor (a sparse Pauli should list only non-`I` letters). -/
def SPauli.noIdentity (P : SPauli) : Bool := P.all (fun f => decide (f.2 ≠ Pauli.I))

/-- No duplicate qubit. -/
def SPauli.nodupQubits (P : SPauli) : Bool := nodupB (P.map Prod.fst)

/-- WELL-FORMED sparse Pauli: no identity factor, no duplicate qubit. -/
def SPauli.wf (P : SPauli) : Bool := P.noIdentity && P.nodupQubits

/-- A well-formed MEASUREMENT operator: `wf` AND non-empty (an empty/identity-only
    measurement is meaningless). -/
def SPauli.wfMeas (P : SPauli) : Bool := P.wf && !P.isEmpty

/-- Every factor addresses a physical qubit `< n` (in range for an `n`-qubit patch). -/
def SPauli.inRange (n : Nat) (P : SPauli) : Bool := P.all (fun f => decide (f.1 < n))

/-- Densify to a `QStab.PauliString` over physical qubits `0 … n-1` (absent qubit ⇒
    identity).  Out-of-range factors are dropped — `inRange` should gate first. -/
def SPauli.toDense (n : Nat) (P : SPauli) : PauliString :=
  (List.range n).map (fun q => ((P.find? (fun f => f.1 == q)).map Prod.snd).getD Pauli.I)

-- a 2-body `ZZ` is a well-formed measurement; its dense form on 3 qubits is `ZIZ`/`ZZI`:
example : SPauli.wfMeas [(0, .Z), (1, .Z)] = true := by decide
example : SPauli.toDense 3 [(0, .Z), (2, .Z)] = ofString "ZIZ" := by decide
-- an identity factor is rejected, a duplicate qubit is rejected, an empty measurement is rejected:
example : SPauli.wf [(0, .I)] = false := by decide
example : SPauli.wf [(0, .Z), (0, .X)] = false := by decide
example : SPauli.wfMeas ([] : SPauli) = false := by decide
-- an out-of-range factor is caught by `inRange`:
example : SPauli.inRange 2 [(0, .Z), (5, .Z)] = false := by decide

/-! ## §2. Postselection policy, stage/contract metadata, flow contracts. -/

/-- An EXACT rational coordinate value `num/den` (Mathlib-free; stored as written, not
    reduced).  Gidney flow centres and integration coordinates are half-integer /
    rational (e.g. `15/7`, `7/4`), so plain `Int` is too narrow.  Integer literals
    elaborate directly via `OfNat`. -/
structure Frac where
  num : Int
  den : Nat := 1
  deriving Repr, DecidableEq

instance : Inhabited Frac := ⟨⟨0, 1⟩⟩
instance (n : Nat) : OfNat Frac n := ⟨⟨Int.ofNat n, 1⟩⟩

/-- A half-integer `n/2` (the common integration coordinate). -/
def Frac.half (n : Int) : Frac := ⟨n, 2⟩

/-- A recursive POSTSELECTION PREDICATE: a Boolean composition (`and`/`or`/`not`) over
    DETECTOR-name and detector-TAG atoms.  This is the GENERAL postselection language —
    not Gidney-specific, not decoder-specific.  `and`/`or` are binary; n-ary `all`/`any`
    fold into them (see `PostPred.all`/`PostPred.any`).  HONESTY: only the SCOPE of the
    atoms is checked (every referenced detector/tag is produced); the predicate's Boolean
    VALUE is a runtime/decoder fact and is never evaluated or claimed here.  A decoder-gap
    acceptance is deliberately NOT an atom — it stays a deferred contract with an explicit
    threshold (`ContractKind`). -/
inductive PostPred
  | detector (name : String)   -- atom: a named detector fired
  | tag      (tag : String)    -- atom: some detector in a tagged group fired
  | and      (p q : PostPred)  -- conjunction
  | or       (p q : PostPred)  -- disjunction
  | not      (p : PostPred)    -- negation
  deriving Repr, DecidableEq

/-- n-ary conjunction: `all [a, b, c] = a ∧ (b ∧ c)`; `all [p] = p`; `all [] = true`
    (modelled as the trivially-satisfied `¬(a ∧ ¬a)` of its FIRST referenced atom is not
    available for `[]`, so empty folds to a neutral that references no detector). -/
def PostPred.all : List PostPred → Option PostPred
  | []      => none
  | [p]     => some p
  | p :: ps => (PostPred.all ps).map (PostPred.and p)

/-- n-ary disjunction (see `PostPred.all`). -/
def PostPred.any : List PostPred → Option PostPred
  | []      => none
  | [p]     => some p
  | p :: ps => (PostPred.any ps).map (PostPred.or p)

/-- A POSTSELECTION policy (LS-level metadata; checked against produced detectors).  The
    legacy `full`/`byDetector`/`byTag` forms are kept; `byDetectorValue` postselects a named
    detector/syndrome to a SPECIFIC Boolean value (so `= true` and `= false` are DISTINCT);
    `byPred` carries a general Boolean predicate over detector/tag atoms. -/
inductive PostPolicy
  | full                                       -- the FULL detector set: any detector event discards the shot
  | byDetector      (name : String)            -- postselect a named detector (discard if it fires)
  | byDetectorValue (name : String) (value : Bool)  -- postselect a named detector/syndrome EQUAL TO `value`
  | byTag           (tag : String)             -- postselect a TAGGED detector group (a genuine LS detector tag)
  | byPred          (p : PostPred)             -- postselect a Boolean predicate over detector/tag atoms
  deriving DecidableEq, Repr

/-- The kind of a DEFERRED LS contract — a surgical/logical step that this pass does
    NOT lower to a real QStab measurement (it is recorded honestly, never faked). -/
inductive ContractKind
  | hxyDoubleCheck                 -- the cultivation H_XY=(X+Y)/√2 logical double-check (NOT a Pauli measurement)
  | nonStdClifford (gate : String) -- a non-standard Clifford macro (H_XY/H_YZ/H_XZ) not implemented in QStab
  | escapeGraft                    -- the cultivation escape graft into the grafted code
  | escapeTransition               -- the cultivation escape transition into the final matchable code
  | stageChunk     (stage : String) -- a cultivation-stage chunk (Gidney `gen` chunk) not built here
  | custom         (tag : String)
  deriving DecidableEq, Repr

/-- A deferred LS contract: its kind plus a human note. -/
structure DeferredContract where
  kind : ContractKind
  note : String
  deriving DecidableEq, Repr

/-- The STRUCTURAL status of a flow contract.  `structural` means ONLY the structural
    checks passed (input/output wf, vars in scope) — it is NOT, and must not be read
    as, a claim of stabilizer-flow SEMANTIC soundness, which is ALWAYS a deferred
    obligation (`Obligation.flowSemantics`, emitted for every flow regardless). -/
inductive FlowStatus
  | structural
  | deferred
  deriving DecidableEq, Repr

/-- A STABILIZER-FLOW contract over an LS/QStab program — the `gen.Flow` concept
    (`gen/_chunk/_flow.py`), modelled structurally (NOT claimed stabilizer-sound).  The
    field correspondence to `gen.Flow` is: `input`=`start`, `output`=`end`,
    `vars`=`measurement_indices`, `flags`=`flags`, `obsKey`=`obs_key`, `center`=`center`
    (as `(re, im)` rationals), `sign`=`sign`.  A boundary interface has an empty `input`
    (an OUTGOING flow: ∅ → output) or an empty `output` (an INCOMING flow: input → ∅). -/
structure Flow where
  tag    : String
  input  : SPauli                       -- gen `start` (empty for an OUTGOING boundary)
  output : SPauli                       -- gen `end`   (empty for an INCOMING boundary)
  vars   : List QVar                    -- gen `measurement_indices` (body measurement vars)
  flags  : List String       := []      -- gen `flags`
  status : FlowStatus        := .deferred
  obsKey : Option Int        := none    -- gen `obs_key` (observable index, if a logical flow)
  center : Option (Frac × Frac) := none -- gen `center` (spatial centroid: re, im)
  sign   : Option Bool       := none    -- gen `sign`
  deriving Repr

/-- A DETECTOR annotation: a named parity expression over PRIOR measurement vars, with
    its detector `tags` (used by tagged postselection — these are DETECTOR tags, NOT
    stage tags) and spatial `coords` (preserved in the sidecar, à la Stim DETECTOR
    coordinates). -/
structure DetectorAnn where
  name   : String
  srcs   : List QVar
  tags   : List String := []
  coords : List Frac   := []   -- Stim DETECTOR coordinates (rational-capable for integration)
  deriving Repr, DecidableEq

/-! ## §3. LS operations and the LS program. -/

/-- The KIND of a physical measurement: a multi-Pauli PRODUCT measurement (`mpp`, Stim
    `MPP`) vs a single-qubit DESTRUCTIVE readout (`destructive`, e.g. Stim `MX`/`M` that
    consumes the qubit).  Sidecar metadata — it does NOT change the QStab dataflow. -/
inductive MeasKind
  | mpp
  | destructive
  deriving DecidableEq, Repr, Inhabited

/-- An LS operation.  EXECUTABLE ops (`prepZero`/`prepPlus`/`h`/`s`/`sDag`/`x`/`z`/`cnot`/
    `cz`/`meas`/`parity`) lower 1:1 to `QStab.StabilizerInstr`; `meas` and `parity` BIND
    the next QStab classical variable (SSA).  ANNOTATION ops (`detector`/`observable`/
    `postselect`/`stage`/`tick`) are sidecar metadata that bind nothing.  `deferred`
    records a contract this pass does not realise (e.g. the H_XY double-check). -/
inductive LSOp
  | prepZero   (q : PQubit)
  | prepPlus   (q : PQubit)
  | h          (q : PQubit)
  | s          (q : PQubit)
  | sDag       (q : PQubit)                               -- S† (lowers HONESTLY to three `S`, since S³ = S†)
  | x          (q : PQubit)
  | z          (q : PQubit)
  | cnot       (control target : PQubit)
  | cz         (a b : PQubit)
  | meas       (sched : Option Sched) (P : SPauli) (kind : MeasKind := .mpp)  -- BINDS the next QVar; `kind` = MPP product vs destructive readout
  | parity     (srcs : List QVar)                         -- BINDS the next QVar
  | detector   (ann : DetectorAnn)                        -- annotation: a tagged parity expr over prior vars
  | observable (name : String) (srcs : List QVar)         -- annotation: a logical observable readout
  | postselect (policy : PostPolicy)                      -- annotation: a postselection policy
  | stage      (tag note : String)                        -- a stage/comment marker (cultivation stages)
  | tick                                                  -- a Gidney `TICK` scheduling-layer boundary (sidecar; no QStab effect)
  | deferred   (contract : DeferredContract)              -- a deferred contract (NOT lowered; obligation)
  deriving Repr

/-- Does this op BIND the next QStab classical variable? -/
def LSOp.binds : LSOp → Bool
  | .meas _ _ _ => true
  | .parity _   => true
  | _           => false

/-- An LS PROGRAM: an `n`-physical-qubit patch worth of ops, plus flow contracts. -/
structure Program where
  numQubits : Nat
  ops       : List LSOp
  flows     : List Flow := []
  deriving Repr

/-- Sidecar view: the (full, tagged) detector annotations. -/
def Program.detectors (p : Program) : List DetectorAnn :=
  p.ops.filterMap (fun op => match op with | .detector a => some a | _ => none)

/-- Sidecar view: the observable annotations. -/
def Program.observables (p : Program) : List (String × List QVar) :=
  p.ops.filterMap (fun op => match op with | .observable n s => some (n, s) | _ => none)

/-- Sidecar view: the postselection policies. -/
def Program.postselects (p : Program) : List PostPolicy :=
  p.ops.filterMap (fun op => match op with | .postselect pol => some pol | _ => none)

/-- Sidecar view: the stage markers `(tag, note)`. -/
def Program.stages (p : Program) : List (String × String) :=
  p.ops.filterMap (fun op => match op with | .stage t n => some (t, n) | _ => none)

/-- Sidecar view: the deferred contracts. -/
def Program.contracts (p : Program) : List DeferredContract :=
  p.ops.filterMap (fun op => match op with | .deferred c => some c | _ => none)

/-- The names of the produced detectors (postselection scope). -/
def Program.detectorNames (p : Program) : List String := p.detectors.map (·.name)

/-- All DETECTOR tags carried by the produced detectors (tagged-postselection scope —
    these are detector tags, distinct from stage tags). -/
def Program.detectorTags (p : Program) : List String := (p.detectors.map (·.tags)).flatten

/-- The sparse Pauli measurements the program performs (its physical `meas` operators). -/
def Program.measurements (p : Program) : List SPauli :=
  p.ops.filterMap (fun op => match op with | .meas _ P _ => some P | _ => none)

/-- The number of Gidney `TICK` scheduling boundaries preserved in the program. -/
def Program.tickCount (p : Program) : Nat :=
  (p.ops.filter (fun op => match op with | .tick => true | _ => false)).length

/-- The number of QStab classical vars the program BINDS (every `meas`/`parity`).  This is
    the offset later-composed chunks must add to their var references (see `ChunkCompose`). -/
def Program.numBindingVars (p : Program) : Nat := (p.ops.filter LSOp.binds).length

/-! ## §4. The classical-dataflow projection (the `QStab.Prog` view). -/

/-- Project a BINDING op to its `QStab.Stmt` (a `meas` becomes a dense physical
    `prop`, a `parity` stays a `parity`).  Non-binding ops project to `none`. -/
def LSOp.toStmt? (n : Nat) : LSOp → Option QStab.Stmt
  | .meas sched P _ => some (.prop sched (SPauli.toDense n P))
  | .parity srcs    => some (.parity srcs)
  | _               => none

/-- The classical measurement/parity DATAFLOW of the program — the `QStab.Prog` whose
    variables the detectors/observables/postselection annotate.  (This is exactly the
    dataflow the lowered `QStab.StabilizerProg` contains; see `LowerQStab`.) -/
def Program.dataflow (p : Program) : QStab.Prog := p.ops.filterMap (LSOp.toStmt? p.numQubits)

end Compiler.LS
