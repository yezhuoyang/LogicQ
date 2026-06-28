/-
  MagicQ.Syntax — the magic-state protocol language (an explicit AST).

  MagicQ is a SOURCE LANGUAGE for magic-state protocols — producing, improving
  and consuming magic states while their QEC CARRIER changes over time.  It is a
  real abstract syntax (data, not Lean-embedded notation, not Lean-term-as-program):
  a `Protocol` is a named list of `ProtocolOp`s over LINEAR magic resources and
  LIVE QEC carriers.  See `MagicQ/DESIGN_PLAN.md` for the grounding in
  magic-state cultivation (Gidney–Shutty–Jones, 2409.17595) and standard 15-to-1
  distillation (Bravyi–Kitaev, quant-ph/0403025).

  REUSE over reinvention (owner directive): carriers reference the existing
  `TypeChecker.Block`/`BlockId`; logical observables reuse `PPM.PLetter`; a pending
  resource reuses `Compiler.MagicObligation`.  Only the genuinely new magic
  concepts are introduced here (magic bases, magic quality, cultivation carriers,
  postselection conditions, decoder/gap conditions, protocol ops).

  Mathlib-free (pure Bool/List/Nat/Option/String) — fast `decide` checking.
-/
import TypeChecker.Basic
import TypeChecker.Judgment.Switch.Cert
import PPM.Syntax
import Compiler.Mixed.Syntax

namespace MagicQ
open TypeChecker

/-! ## §1. Magic bases and quality. -/

/-- A magic-state BASIS.  `T`/`Tdg` are the π/8 (`T`) states, `Y` is the
    `S`/`Y`-type state, and `A0` is the Bravyi–Kitaev `|A₀⟩ = T|+⟩` (the canonical
    15-to-1 input, equal to `T|+⟩` up to a global phase / Clifford naming —
    quant-ph/0403025 Eq. for `|A₀⟩`).  The errata around `H_XY`/sign conventions
    (2409.17595) is the reason these are tracked explicitly rather than collapsed
    into "a `T`-like state". -/
inductive MagicBasis
  | T        -- the |T⟩ = T|+⟩ = (|0⟩ + √i|1⟩)/√2 state (≡ Bravyi–Kitaev |A₀⟩ up to phase/Clifford); the π/8 cultivation target
  | Tdg      -- π/8† : T† (the |T⟩ partner with conjugate phase)
  | Y        -- S/Y-type magic state
  | A0       -- Bravyi–Kitaev |A₀⟩ = T|+⟩ (the canonical RM-15 input; the SAME state as `T`)
  deriving DecidableEq, Repr, Inhabited

/-- Is this a π/8 (`T`)-type basis?  `T`, `Tdg`, `A0` are all Clifford-equivalent
    `T`-type states; `Y` is the distinct `S`-type. -/
def MagicBasis.tType : MagicBasis → Bool
  | .T | .Tdg | .A0 => true
  | .Y              => false

/-- The valid INPUT basis for standard Bravyi–Kitaev 15-to-1: the `|A₀⟩ = T|+⟩`
    state (the `A`-eigenbasis input), i.e. `T` or `A0`.  `Tdg` (the conjugate `T†`)
    is NOT a standard input — it would need an explicit conjugation/normalisation op
    and obligation, not a silent relabel to `T`.  `Y` is the wrong family. -/
def MagicBasis.aType : MagicBasis → Bool
  | .T | .A0 => true
  | .Tdg | .Y => false

/-- Two bases are COMPATIBLE as a distillation/measurement input iff they are the
    same basis, or both `T`-type (so a `T`-factory accepts `T`/`Tdg`/`A0`). -/
def MagicBasis.compatible (a b : MagicBasis) : Bool :=
  (a == b) || (a.tType && b.tType)

/-- The (claimed / symbolic) QUALITY of a magic resource.  V1 is Mathlib-free, so
    real-valued error/probability claims are carried SYMBOLICALLY as strings (they
    are deferred physical obligations in this pass, never proven here); only the
    integer code/fault distances are checked structurally. -/
structure MagicQuality where
  rawError      : Option String := none   -- input error ε (symbolic, e.g. "ε")
  outputError   : Option String := none   -- output-error bound (e.g. "35·ε³ + O(ε⁴)")
  successProb   : Option String := none   -- success probability (e.g. "(1 + 15(1-2ε)⁸)/16")
  codeDistance  : Option Nat    := none   -- code distance d of the carrier
  faultDistance : Option Nat    := none   -- fault distance (cultivation d1 target)
  deferred      : List String   := []     -- extra deferred quality claims
  deriving Repr, Inhabited

/-! ## §2. Carriers (reusing the typed-block representation). -/

/-- A CARRIER reference.  A `block` carrier is backed by a real `TypeChecker`
    typed block in the environment Γ (so it is genuinely checkable: liveness,
    ownership, logical arity).  An `external` carrier is an honest NAMED
    placeholder for a code family not yet materialised in ChainQ (e.g. the color
    code `ColorCode(3)` and the grafted matchable code `Matchable(d2)` — ChainQ
    has only a `ColorCode` README so far).  The checker records every `external`
    carrier as a DEFERRED obligation rather than pretending it is ChainQ-typed. -/
inductive CarrierRef
  | block    (id : TypeChecker.BlockId)
  | external (name : String)
  deriving Repr, DecidableEq, Inhabited

/-- A live QEC carrier: which code it currently is, how many logical qubits it
    exposes, an optional decoder tag, and its current quality.  Reuses
    `CarrierRef` (→ `TypeChecker.Block`) rather than inventing a parallel code
    representation. -/
structure Carrier where
  code         : CarrierRef
  logicalCount : Nat            := 1       -- exposed logical arity k
  decoderTag   : Option String  := none
  quality      : MagicQuality   := {}
  deriving Repr, Inhabited

/-- A carrier identifier (author-assigned in the AST). -/
abbrev CarrierId := Nat
/-- A linear magic-resource identifier (author-assigned in the AST). -/
abbrev ResourceId := Nat

/-! ## §3. Linear magic resources and the magic environment Σ. -/

/-- A magic STATE: a linear resource of a given basis, living on a carrier, with
    a claimed quality. -/
structure MagicState where
  basis   : MagicBasis
  carrier : CarrierId
  quality : MagicQuality := {}
  deriving Repr, Inhabited

/-- A linear MAGIC RESOURCE: either a produced/injected `MagicState`, or a PENDING
    obligation imported from the mixed compiler (`Compiler.MagicObligation`, e.g. a
    deferred `T`-gate).  Pending obligations are representable so MagicQ outputs can
    later be paired against the compiler's obligations (see `dischargesObligation`);
    their gate-teleportation discharge is out of scope for this pass. -/
inductive MagicResource
  | state   (s : MagicState)
  | pending (ob : Compiler.MagicObligation)
  deriving Repr

/-- A slot in the linear environment: an author-assigned id, the resource, and a
    `consumed` flag enforcing exactly-once use. -/
structure ResourceSlot where
  id       : ResourceId
  res      : MagicResource
  consumed : Bool := false
  deriving Repr

/-- The LINEAR magic-resource environment Σ. -/
structure MagicEnv where
  slots : List ResourceSlot := []
  deriving Repr

namespace MagicEnv

/-- Find a resource slot by id. -/
def slot? (menv : MagicEnv) (r : ResourceId) : Option ResourceSlot :=
  menv.slots.find? (fun s => s.id == r)

/-- Is `r` present in the environment (consumed or not)? -/
def has (menv : MagicEnv) (r : ResourceId) : Bool := (menv.slot? r).isSome

/-- Append a fresh slot. -/
def push (menv : MagicEnv) (s : ResourceSlot) : MagicEnv := ⟨menv.slots ++ [s]⟩

/-- Mark resource `r` consumed (linear use). -/
def consume (menv : MagicEnv) (r : ResourceId) : MagicEnv :=
  ⟨menv.slots.map (fun s => if s.id == r then { s with consumed := true } else s)⟩

/-- The ids of resources that were never consumed (linearity leaks). -/
def leaked (menv : MagicEnv) : List ResourceId :=
  (menv.slots.filter (fun s => !s.consumed)).map (·.id)

end MagicEnv

/-! ## §4. Logical observables and postselection conditions. -/

/-- A logical-observable AXIS.  Ordinary Pauli checks REUSE `PPM.PLetter`; `hxy` is
    the NON-Pauli cultivation check `H_XY = (X+Y)/√2`, whose +1 eigenstate is the
    logical `|T⟩ = T|+⟩` and whose −1 eigenstate is `Z|T⟩` (2409.17595: the color
    code's transversal `H_XY`, measured by a GHZ-controlled transversal-`H_XY`
    "double-check" that raises the T state's fault distance).  `hxy` is NOT a Pauli
    and must not be faked as a `PPM.PLetter`. -/
inductive LogicalAxis
  | pauli (letter : PPM.PLetter)   -- an ordinary logical Pauli check (reuses PPM.PLetter)
  | hxy                            -- the non-Pauli H_XY = (X+Y)/√2 T-basis check
  deriving Repr, DecidableEq

/-- A logical OBSERVABLE on a carrier: the `idx`-th logical qubit and its axis (an
    ordinary Pauli, or the non-Pauli `hxy` T-basis check).  Used by a logical
    check/measurement op. -/
structure LogicalObs where
  idx  : Nat
  axis : LogicalAxis
  deriving Repr, DecidableEq

/-- A recursive POSTSELECTION PREDICATE at the MagicQ level: a Boolean composition
    (`and`/`or`/`not`) over DETECTOR/SYNDROME-NAME atoms.  This is the GENERAL postselection
    language at the MagicQ level; it lowers to `LS.PostPolicy.byPred`.

    HONESTY: MagicQ v1 has a FLAT detector/syndrome namespace and NO detector TAGS (its ops
    emit detector NAMES, not tags), so there is deliberately NO `tag` atom here — true
    detector tags are an LS-only concept (`LS.PostPred.tag`) and exposing one in MagicQ would
    be a name-alias masquerading as a tag.  Only the atom SCOPE is checked (every atom
    references a detector/syndrome produced by a prior op); the predicate's Boolean VALUE is a
    runtime/decoder fact and is never evaluated here.  A decoder GAP is deliberately NOT an
    atom — it stays the separate deferred `decoderGap` obligation, so it can never look
    proven. -/
inductive PostPred
  | detector (name : String)   -- atom: a named detector/syndrome fired
  | and      (p q : PostPred)  -- conjunction
  | or       (p q : PostPred)  -- disjunction
  | not      (p : PostPred)    -- negation
  deriving Repr, DecidableEq

/-- A POSTSELECTION condition.  These refer to detectors/syndromes produced by
    PRIOR ops; the checker verifies that scope.

    * `fullDetectors`   — early FULL postselection: ANY detector event discards
      the attempt (cultivation's early stages, 2409.17595 §III).
    * `syndromeEq n v`  — a named syndrome equals a value (e.g. the RM-15 `η = 0`).
    * `taggedDetectors name` — COMPATIBILITY syntax for a detector-NAME subset/alias.  MagicQ
      v1 has NO true detector-tag production/tracking, so this is NOT an LS `.byTag`: it is
      scope-checked against produced detector NAMES and lowers to `LS.PostPolicy.byDetector`.
      True LS detector tags remain LS-only until MagicQ gains tag-producing ops.
    * `predicate p`     — a general Boolean predicate over detector/syndrome-NAME atoms
      (MagicQ v1 has no tag atom — see `PostPred`; scope-checked; lowers to
      `LS.PostPolicy.byPred`).
    * `decoderGap thr`  — keep/reject on a decoder GAP ≥ threshold: a DEFERRED
      decoder obligation, never discharged here. -/
inductive PostselectCond
  | fullDetectors
  | syndromeEq      (name : String) (value : Bool)
  | taggedDetectors (name : String)   -- detector-NAME alias (NOT a true LS tag); see the doc above
  | predicate       (p : PostPred)
  | decoderGap      (threshold : String)
  deriving Repr

/-! ## §5. Protocol operations and protocols. -/

/-- A CHECKED block-switch TARGET for a v2 grow/graft/switch op: the target code as a
    ChainQ `TypeChecker.Block`, a REUSED `TypeChecker.SwitchCert` (NO duplicate certificate
    algebra), and the required post-switch distance.  The checker validates it against the
    existing `TypeChecker.checkSwitchWithDistance` (see `MagicQ.checkBlockSwitch`). -/
structure SwitchTarget where
  target           : TypeChecker.Block
  cert             : TypeChecker.SwitchCert
  requiredDistance : Nat := 0
  deriving Repr

/-- The style of magic-state INJECTION (2409.17595 compares these; `unitary` is the
    source-code default path). -/
inductive InjectStyle
  | unitary
  | bellGrowth
  | teleport
  | degenerate
  | supplied      -- NOT an in-protocol injection: an externally-supplied (already-prepared) noisy input state
  deriving DecidableEq, Repr, Inhabited

/-- A protocol OPERATION.  Carrier/resource ids are author-assigned (no parser in
    this pass); the checker validates uniqueness, scope, liveness, arity and
    linearity.

    Carriers and resources are explicit so the AST is general enough for BOTH
    families: cultivation (`inject`→`checkLogical`→`grow`→`stabilize`→`graft`→
    `postselect`→`output`) and standard 15-to-1 (`inject`×15 → `distill15To1` →
    `postselect` → `output`). -/
inductive ProtocolOp
  /-- Create an injected magic resource `resource` of `basis` on a FRESH carrier
      `carrier` whose code is `code`, with claimed `quality`. -/
  | inject (style : InjectStyle) (basis : MagicBasis)
           (carrier : CarrierId) (code : CarrierRef)
           (resource : ResourceId) (quality : MagicQuality := {})
  /-- A logical CHECK / measurement of `obs` on `carrier` that the type system can
      VALIDATE NOW (an ordinary Pauli observable on an exposed logical), emitting
      detector `detector`.  A non-Pauli axis (`hxy`) is REJECTED here — route it
      through `assumeLogicalCheck`. -/
  | checkLogical (carrier : CarrierId) (obs : LogicalObs) (detector : String)
  /-- A DEFERRED-ASSUMPTION logical check: a logical observable whose legality the
      type system CANNOT yet prove (e.g. the non-Pauli `H_XY` T-basis check on a
      color code with no materialised transversal-`H_XY` evidence).  Accepts at the
      high level but records an EXPLICIT deferred obligation carrying `justification`;
      emits `detector`. -/
  | assumeLogicalCheck (carrier : CarrierId) (obs : LogicalObs) (detector justification : String)
  /-- GROW / switch `carrier` to code `to`, preserving logical arity, exposing the
      promised output and CLAIMING fault distance `faultDistance`; emits `detector`. -/
  | grow (carrier : CarrierId) (to : CarrierRef) (faultDistance : Nat) (detector : String)
  /-- STABILIZE `carrier` for `rounds` superdense cycles; emits `detector`. -/
  | stabilize (carrier : CarrierId) (rounds : Nat) (detector : String)
  /-- ESCAPE by GRAFTing `carrier` into an intermediate grafted code `into` of code
      distance `codeDistance`; emits `detector`. -/
  | graft (carrier : CarrierId) (into : CarrierRef) (codeDistance : Nat) (detector : String)
  /-- ESCAPE TRANSITION: switch `carrier` from the intermediate grafted code into the
      FINAL matchable code `to` of code distance `codeDistance` (run after the
      `r1` grafted-code idling rounds and before the `r2` final idling rounds).
      Distinct from `graft` — this is the explicit grafted→matchable transition. -/
  | transitionToMatchable (carrier : CarrierId) (to : CarrierRef) (codeDistance : Nat) (detector : String)
  /-- **v2 CHECKED code switch**: switch `carrier` (which must be a LIVE, OWNED `.block`
      carrier) to the `target.target` code via the certified `target.cert`, requiring
      post-switch distance `target.requiredDistance`.  Unlike `grow`/`graft` (whose v1
      `.block` targets are rejected for lack of a certificate), this op carries a real
      `SwitchTarget` and is validated by `TypeChecker.checkSwitchWithDistance`, threading
      the post-switch `TypedEnv`.  Emits `detector`. -/
  | switchBlock (carrier : CarrierId) (target : SwitchTarget) (detector : String)
  /-- POSTSELECT on `cond` (scope-checked against prior detectors/syndromes). -/
  | postselect (cond : PostselectCond)
  /-- 15-to-1 DISTILLATION: consume exactly the 15 input resources `inputs`,
      producing one output resource `output` of `quality` on fresh carrier
      `outCarrier` (code `outCode`).  `syndromes` NAMES the detectors/syndromes the
      distillation measures (e.g. the RM-15 `η`), which become postselectable. -/
  | distill15To1 (inputs : List ResourceId)
                 (output : ResourceId) (outCarrier : CarrierId) (outCode : CarrierRef)
                 (quality : MagicQuality := {}) (syndromes : List String := [])
  /-- DISCARD (consume) a resource — the disposable failure branch. -/
  | discard (resource : ResourceId)
  /-- OUTPUT (return) a magic resource — gated on its carrier being live and its
      declared quality/distance obligations having been ESTABLISHED. -/
  | output (resource : ResourceId)
  deriving Repr

/-- Standard protocol PARAMETERS (paper conventions, 2409.17595): `d1` end-of-
    cultivation fault distance, `d2` final code distance after escape, `r1` grafted-
    code rounds, `r2` final matchable-code rounds, plus the injection style. -/
structure ProtocolParams where
  d1          : Option Nat   := none
  d2          : Option Nat   := none
  r1          : Option Nat   := none
  r2          : Option Nat   := none
  injectStyle : InjectStyle  := .unitary
  notes       : List String  := []
  deriving Repr, Inhabited

/-- A MagicQ PROTOCOL: a named, parameterised list of operations plus symbolic
    spec metadata (success-probability / threshold / output-error equations carried
    as strings — deferred, not proven, in this pass). -/
structure Protocol where
  name   : String
  params : ProtocolParams := {}
  ops    : List ProtocolOp
  spec   : List String := []
  deriving Repr

/-- A produced magic state DISCHARGES a mixed-IR magic obligation iff the bases
    line up (`T`-type output discharges a `tGate` obligation).  Pure helper for the
    later resource/scheduling pass; not wired into the checker yet (the actual
    gate-teleportation discharge is out of scope for v1). -/
def dischargesObligation (s : MagicState) (ob : Compiler.MagicObligation) : Bool :=
  match ob.kind with
  | .tGate => s.basis.tType

end MagicQ
