/-
  MagicQ.Check — the high-level MagicQ checker.

  The judgement threads the ORDINARY typed environment Γ (`TypeChecker.TypedEnv`),
  the LINEAR magic-resource environment Σ (`MagicEnv`), and a magic-specific
  `CheckState` (live carriers, the detector/syndrome scope, and the accumulating
  deferred obligations / outputs / consumed resources):

      Γ ; Σ ; CheckState  ⊢  op  ⇒  Σ' ; CheckState'

  It validates the parts checkable at the HIGHEST logical/type level (owner brief):
  carrier existence + liveness, logical-observable well-formedness, code-growth
  arity preservation + exposed output, postselection SCOPE, exact 15-to-1 arity,
  and EXACT-ONCE linear consumption of magic resources.  It does NOT attempt to
  verify stochastic fault tolerance or decoder performance — those are recorded as
  explicit DEFERRED `Obligation`s (honest placeholders, never silently discharged).

  Reuses `TypeChecker.TypeError` (wrapped) and `TypeChecker.TypedEnv.block?` for the
  real block-backed carriers; adds a small `MagicError` only for the genuinely new
  magic-level failures.  Mathlib-free.
-/
import MagicQ.Syntax
import TypeChecker.Judgment.Switch.Check

namespace MagicQ
open TypeChecker

/-! ## §1. The MagicQ error vocabulary. -/

/-- Failures a MagicQ check can raise.  Block/typing failures of a real carrier are
    REUSED from `TypeChecker.TypeError` via `typeError`; the rest are magic-level. -/
inductive MagicError
  | typeError               (e : TypeChecker.TypeError)  -- a reused block/typing error (real carrier)
  | carrierIdReused         (c : CarrierId)              -- a fresh carrier id collides with a live one
  | carrierNotFound         (c : CarrierId)
  | carrierNotLive          (c : CarrierId)
  | carrierArityChanged     (c : CarrierId) (expected got : Nat)  -- grow/graft must preserve logical arity
  | resourceIdReused        (r : ResourceId)
  | resourceNotFound        (r : ResourceId)
  | resourceAlreadyConsumed (r : ResourceId)             -- linearity: consumed twice (or a duplicate input)
  | notAState               (r : ResourceId)             -- expected a magic state, found a pending obligation
  | basisIncompatible       (r : ResourceId) (got : MagicBasis)  -- a non-`T`-type input to a `T` factory
  | wrongInputArity         (expected got : Nat)         -- 15-to-1 needs EXACTLY 15 inputs
  | observableOutOfRange    (c : CarrierId) (idx count : Nat)     -- a check addresses a non-exposed logical
  | unknownDetector         (name : String)              -- postselection refers to an unproduced detector/syndrome
  | outputWithoutCarrier    (r : ResourceId)             -- output a state whose carrier is missing/dead
  | outputWithoutQuality    (r : ResourceId) (missing : String)  -- declared distance not yet established
  | resourceLeak            (leaked : List ResourceId)   -- a live magic state was never consumed (output/discard)
  | checkNotValidated       (c : CarrierId) (note : String)  -- a logical check the validated path can't prove (use assumeLogicalCheck)
  | blockSwitchUnsupported  (id : Nat)                   -- a grow/graft TARGET is a `.block` but the v1 AST carries no SwitchCert to validate it
  | other                   (msg : String)
  deriving Repr

/-- Did a MagicQ check succeed? -/
def mok? {α : Type} : Except MagicError α → Bool
  | .ok _ => true | .error _ => false

/-! ## §2. Deferred obligations and the check state. -/

/-- A DEFERRED physical/decoder/fault-distance obligation: recorded honestly, never
    discharged in this pass.  These are the "external obligations" the owner asked
    the checker to track rather than pretend to prove. -/
inductive Obligation
  | externalCarrier     (name : String) (reason : String)  -- a placeholder code not materialised in ChainQ
  | injection           (style : InjectStyle)              -- injection-correctness (state prep) deferred
  | growthFaultDistance (carrier : CarrierId) (claim : Nat) -- the claimed end-of-cultivation fault distance
  | stabilizationRounds (carrier : CarrierId) (rounds : Nat) -- superdense-cycle FT deferred
  | escapeGraft         (carrier : CarrierId) (codeDistance : Nat) -- the graft/escape construction (external cert)
  | escapeTransition    (carrier : CarrierId) (codeDistance : Nat) -- the escape TRANSITION into the final matchable code (after grafted-code idling)
  | decoderGap          (threshold : String)               -- the escape decoder-gap predicate
  | fullPostselection                                       -- early full postselection assumed correct
  | syndromeDecoding    (name : String)                    -- a deferred (possibly non-Pauli) syndrome-decoding obligation, e.g. the RM-15 A-type `η` (NOT captured by the binary CSS surrogate)
  | assumedLogicalCheck (carrier : CarrierId) (obs : LogicalObs) (detector justification : String)
                                                            -- a deferred-ASSUMPTION logical check (e.g. transversal H_XY) the type system can't yet prove (full data preserved)
  | qualityClaim        (claim : String)                   -- a surfaced `MagicQuality.deferred` claim
  | specClaim           (claim : String)                   -- a protocol-level symbolic spec claim
  deriving Repr, DecidableEq

/-- The current state of a live carrier in the check. -/
structure CarrierState where
  carrier   : Carrier
  live      : Bool       := true
  faultDist : Option Nat := none   -- established fault-distance claim (set by `grow`)
  codeDist  : Option Nat := none   -- established code-distance claim (set by `graft`; inject/distill leave it `none`)
  deriving Repr, Inhabited

/-- The MagicQ check state: live carriers, the detector/syndrome SCOPE, the
    accumulating deferred obligations, and the produced outputs / consumed ids. -/
structure CheckState where
  carriers    : List (CarrierId × CarrierState) := []
  detectors   : List String                     := []   -- postselectable detector/syndrome names produced so far
  obligations : List Obligation                 := []
  outputs     : List MagicState                 := []
  consumed    : List ResourceId                 := []
  deriving Repr, Inhabited

namespace CheckState

/-- Look up a live-carrier state. -/
def carrier? (st : CheckState) (c : CarrierId) : Option CarrierState :=
  (st.carriers.find? (fun p => p.1 == c)).map Prod.snd

/-- Insert or update a carrier. -/
def setCarrier (st : CheckState) (c : CarrierId) (cs : CarrierState) : CheckState :=
  if st.carriers.any (fun p => p.1 == c) then
    { st with carriers := st.carriers.map (fun p => if p.1 == c then (c, cs) else p) }
  else
    { st with carriers := st.carriers ++ [(c, cs)] }

/-- Is `name` a detector/syndrome produced by a PRIOR op (postselection scope)? -/
def knowsDetector (st : CheckState) (name : String) : Bool := st.detectors.contains name

/-- Record a produced detector/syndrome name (idempotent). -/
def addDetector (st : CheckState) (name : String) : CheckState :=
  if st.detectors.contains name then st else { st with detectors := st.detectors ++ [name] }

/-- Record a deferred obligation (idempotent). -/
def addObligation (st : CheckState) (o : Obligation) : CheckState :=
  if st.obligations.contains o then st else { st with obligations := st.obligations ++ [o] }

/-- Record a produced output magic state. -/
def addOutput (st : CheckState) (s : MagicState) : CheckState :=
  { st with outputs := st.outputs ++ [s] }

/-- Record a consumed resource id. -/
def addConsumed (st : CheckState) (r : ResourceId) : CheckState :=
  { st with consumed := st.consumed ++ [r] }

/-- RETIRE a carrier (mark it NOT live) — used once its magic state is `output`/
    `discard`-ed (or its input is consumed by distillation).  Later ops referencing
    it are then rejected with `carrierNotLive`, and it is no longer a live carrier. -/
def retireCarrier (st : CheckState) (c : CarrierId) : CheckState :=
  let carriers' := st.carriers.map (fun p => if p.1 == c then (c, { p.2 with live := false }) else p)
  { st with carriers := carriers' }

/-- Is the underlying ChainQ/TypeChecker `.block id` already held by a LIVE MagicQ
    carrier?  The reservation check preventing two live carriers from aliasing one
    real block — reusing block liveness rather than a parallel ownership model.
    (External carriers are independent abstract instances and are NOT reserved.) -/
def blockAliasLive? (st : CheckState) (id : TypeChecker.BlockId) : Bool :=
  st.carriers.any (fun p => p.2.live && decide (p.2.carrier.code = CarrierRef.block id))

/-- Surface a resource's `MagicQuality.deferred` strings as explicit `qualityClaim`
    obligations (so they appear in `CheckedProtocol.deferred`, not just on the value). -/
def addQualityClaims (st : CheckState) (q : MagicQuality) : CheckState :=
  q.deferred.foldl (fun s c => s.addObligation (.qualityClaim c)) st

end CheckState

/-- Reject claiming a `.block id` that is already held by a LIVE carrier (aliasing a
    real ChainQ/TypeChecker block).  Vacuous for `external` carriers. -/
def ensureNoBlockAlias (st : CheckState) (code : CarrierRef) : Except MagicError Unit :=
  match code with
  | .block id => if st.blockAliasLive? id then .error (.typeError (.clone id)) else .ok ()
  | .external _ => .ok ()

/-- Assert `cond`, raising `e` otherwise (a uniform early-guard for `Except`). -/
def ensure (cond : Bool) (e : MagicError) : Except MagicError Unit :=
  if cond then .ok () else .error e

/-- Scope-check a MagicQ postselection PREDICATE: every detector/syndrome/tag atom must
    reference a detector produced by a PRIOR op.  Only scope is checked — the predicate's
    Boolean value is a runtime/decoder fact, never evaluated.  Structural recursion. -/
def checkMagicPred (st : CheckState) : PostPred → Except MagicError Unit
  | .detector name => if st.knowsDetector name then .ok () else .error (.unknownDetector name)
  | .and p q       => do checkMagicPred st p; checkMagicPred st q
  | .or p q        => do checkMagicPred st p; checkMagicPred st q
  | .not p         => checkMagicPred st p

/-! ## §3. The per-op checker. -/

/-- Resolve a carrier code to a checkable target, returning the obligation incurred.
    A `block` carrier is validated against Γ (must exist + be live, and — when
    `requireOwned` — OWNED, reusing the `TypeChecker.checkSwitch` ownership discipline
    via `TypeError.notOwned`); an `external` carrier produces an honest deferred
    obligation.  `requireOwned := true` for a code that a magic state is CLAIMED on
    (inject / distillation output); `false` for a grow/graft TARGET (a valid
    destination code that inherits the source's ownership).  Returns the carrier's
    logical arity `k` (from the block, or `1` for an external placeholder). -/
def resolveCode (Γ : TypedEnv) (requireOwned : Bool) (code : CarrierRef) (reason : String) :
    Except MagicError (Nat × Option Obligation) :=
  match code with
  | .block id =>
      match Γ.block? id with
      | none    => .error (.typeError (.badBlock id))
      | some tb =>
          if !tb.block.live then .error (.typeError .notLive)
          else if requireOwned && !(decide (tb.block.own = Owned.owned)) then .error (.typeError .notOwned)
          else .ok (tb.block.lx.length, none)
  | .external name => .ok (1, some (.externalCarrier name reason))

/-- A block-backed carrier may be TRANSFORMED (grown/grafted) only if its block is
    LIVE and OWNED — exactly the discipline `TypeChecker.checkSwitch` enforces on a
    switch SOURCE (a borrowed code cannot be consumed).  Vacuous for `external`
    carriers (their deferral is recorded separately). -/
def requireOwnedLive (Γ : TypedEnv) (code : CarrierRef) : Except MagicError Unit :=
  match code with
  | .block id =>
      match Γ.block? id with
      | none    => .error (.typeError (.badBlock id))
      | some tb =>
          if !tb.block.live then .error (.typeError .notLive)
          else if !(decide (tb.block.own = Owned.owned)) then .error (.typeError .notOwned)
          else .ok ()
  | .external _ => .ok ()

/-- Resolve a grow/graft/transition TARGET code IN THE v1 AST.  The v1 `ProtocolOp`s
    carry NO switch certificate, so a real block-backed switch CANNOT be validated against
    `TypeChecker.checkSwitch` here — a `.block` target is REJECTED rather than silently
    accepted (which would conflate a live block carrier with a code template and bypass the
    ownership/alias/cert checks).  An `external` target is a code family the carrier
    switches into, recorded as a deferred obligation.

    The REAL checked block-switch path now EXISTS — `MagicQ.checkBlockSwitch` (below), which
    reuses `TypeChecker.checkSwitchWithDistance`.  To wire it into grow/graft/transition, a
    v2 op must carry a `MagicQ.SwitchTarget` `(target Block, TypeChecker.SwitchCert,
    requiredDistance)`, and `checkOp` must thread a MUTABLE `TypedEnv` (the fold currently
    keeps Γ read-only) so the post-switch env from `checkBlockSwitch` replaces Γ for later
    ops.  Until that AST change lands, `.block` targets stay rejected — honestly. -/
def resolveSwitchTarget (code : CarrierRef) (reason : String) :
    Except MagicError (Option Obligation) :=
  match code with
  | .block id      => .error (.blockSwitchUnsupported id)
  | .external name => .ok (some (.externalCarrier name reason))

/-- **Real ChainQ-backed block switch** — REUSES `TypeChecker.checkSwitchWithDistance` (NO
    fake acceptance, NO duplicate algebra).  Given the typed env Γ, the SOURCE block carrier
    id, and a `MagicQ.SwitchTarget` (defined in `MagicQ.Syntax`), it validates the target
    code, the symplectic certificate (stabilizer + logical preservation, ownership/liveness
    of the source), and the required post-switch distance, returning the post-switch typed
    env + switch + distance evidence (TypeChecker errors wrapped as `MagicError.typeError`).
    This is the path the v2 `switchBlock` op takes (see `checkSwitchBlockOp`). -/
def checkBlockSwitch (Γ : TypeChecker.TypedEnv) (src : TypeChecker.BlockId) (tgt : SwitchTarget) :
    Except MagicError (TypeChecker.TypedEnv × TypeChecker.TypedSwitch × TypeChecker.TypedDistanceEvidence) :=
  match TypeChecker.toTargetBlock? tgt.target with
  | .error e => .error (.typeError e)
  | .ok tD   =>
      match TypeChecker.checkSwitchWithDistance Γ src tD tgt.cert tgt.requiredDistance with
      | .ok r    => .ok r
      | .error e => .error (.typeError e)

/-- **The v2 `switchBlock` op handler** — the only op that UPDATES Γ.  The carrier must be
    a LIVE `.block` carrier; its block is switched by `checkBlockSwitch` (reusing the real
    `TypeChecker.checkSwitchWithDistance`), the carrier's logical arity is refreshed from the
    target, the switch's deferred FT obligations are recorded, the detector is registered,
    and the POST-SWITCH `TypedEnv` is returned for later ops.  An `external` carrier has no
    block to switch and is rejected (use the deferred `grow`/`graft` path). -/
def checkSwitchBlockOp (Γ : TypedEnv) (menv : MagicEnv) (st : CheckState)
    (carrier : CarrierId) (tgt : SwitchTarget) (detector : String) :
    Except MagicError (TypedEnv × MagicEnv × CheckState) := do
  match st.carrier? carrier with
  | none    => .error (.carrierNotFound carrier)
  | some cs =>
      ensure cs.live (.carrierNotLive carrier)
      match cs.carrier.code with
      | .external name => .error (.other s!"switchBlock requires a .block carrier; carrier {carrier} is external ({name})")
      | .block id =>
          let (Γ', _switch, _dist) ← checkBlockSwitch Γ id tgt
          -- the carrier stays on the SAME block id, now retyped as the target code; refresh
          -- its exposed logical arity and record the switch's deferred FT obligations.
          let cs' : CarrierState := { cs with carrier := { cs.carrier with logicalCount := tgt.target.lx.length } }
          let st1 := ((st.setCarrier carrier cs').addObligation
                       (.specClaim s!"checked code switch on block {id} (required distance {tgt.requiredDistance})")).addDetector detector
          .ok (Γ', menv, st1)

/-- **The MagicQ per-op judgement.**  `Γ ; Σ ; st ⊢ op ⇒ Σ' ; st'`. -/
def checkOp (Γ : TypedEnv) (menv : MagicEnv) (st : CheckState) :
    ProtocolOp → Except MagicError (MagicEnv × CheckState)
  | .inject style basis carrier code resource quality => do
      ensure (st.carrier? carrier).isNone (.carrierIdReused carrier)
      ensure (!menv.has resource) (.resourceIdReused resource)
      -- a block-backed injection CLAIMS the block to hold a new magic state → live + owned,
      -- and that real block may not already be ALIASED by another live MagicQ carrier.
      ensureNoBlockAlias st code
      let (k, ob?) ← resolveCode Γ true code "injection carrier not materialised in ChainQ"
      let st1 := match ob? with | some o => st.addObligation o | none => st
      -- injection makes a small (distance-3) code; the carrier's FINAL fault/code
      -- distances are only ESTABLISHED later (by `grow`/`graft`), so output gating
      -- against the resource's PROMISED quality stays meaningful.
      let cs : CarrierState :=
        { carrier := { code := code, logicalCount := k, quality := quality },
          live := true, faultDist := none, codeDist := none }
      let st2 := ((st1.setCarrier carrier cs).addObligation (.injection style)).addQualityClaims quality
      let menv' := menv.push { id := resource, res := .state { basis := basis, carrier := carrier, quality := quality } }
      .ok (menv', st2)
  | .checkLogical carrier obs detector => do
      match st.carrier? carrier with
      | none    => .error (.carrierNotFound carrier)
      | some cs =>
          ensure cs.live (.carrierNotLive carrier)
          -- the observable must address an EXPOSED logical of the carrier.
          ensure (obs.idx < cs.carrier.logicalCount) (.observableOutOfRange carrier obs.idx cs.carrier.logicalCount)
          -- for a REAL (block-backed) carrier, re-confirm the logical is exposed in Γ.
          let _ ← match cs.carrier.code with
            | .block id =>
                match Γ.block? id with
                | none    => .error (.typeError (.badBlock id))
                | some tb => ensure (obs.idx < tb.block.lx.length)
                               (.typeError (.badLogicalIndex id obs.idx))
            | .external _ => .ok ()
          -- `checkLogical` is the VALIDATED path: ONLY an ordinary Pauli observable
          -- (reusing `PPM.PLetter`, justified by the carrier's exposed logical basis)
          -- is accepted.  A non-Pauli axis (`hxy`) the type system cannot prove is
          -- REJECTED — route it through `assumeLogicalCheck` (the deferred path).
          match obs.axis with
          | .pauli _ => .ok (menv, st.addDetector detector)
          | .hxy     => .error (.checkNotValidated carrier
                          "non-Pauli H_XY check is not validatable by checkLogical; use assumeLogicalCheck")
  | .assumeLogicalCheck carrier obs detector justification => do
      match st.carrier? carrier with
      | none    => .error (.carrierNotFound carrier)
      | some cs =>
          ensure cs.live (.carrierNotLive carrier)
          ensure (obs.idx < cs.carrier.logicalCount) (.observableOutOfRange carrier obs.idx cs.carrier.logicalCount)
          -- the check's LEGALITY is ASSUMED (deferred), recorded EXPLICITLY with its
          -- FULL machine-readable data (carrier, observable, detector, justification):
          -- ChainQ cannot yet prove the carrier admits this (e.g. transversal-H_XY) check.
          .ok (menv, (st.addObligation (.assumedLogicalCheck carrier obs detector justification)).addDetector detector)
  | .grow carrier to faultDistance detector => do
      match st.carrier? carrier with
      | none    => .error (.carrierNotFound carrier)
      | some cs =>
          ensure cs.live (.carrierNotLive carrier)
          -- the block-backed SOURCE being transformed must be live + owned (checkSwitch
          -- discipline; a borrowed code cannot be consumed).
          requireOwnedLive Γ cs.carrier.code
          -- the TARGET must be `external` (a `.block` target needs a real switch
          -- certificate the v1 AST does not carry — it is REJECTED, not aliased in).
          let ob? ← resolveSwitchTarget to "grow target not materialised in ChainQ"
          let st1 := match ob? with | some o => st.addObligation o | none => st
          let cs' : CarrierState :=
            { cs with carrier := { cs.carrier with code := to }, faultDist := some faultDistance }
          let st2 := ((st1.setCarrier carrier cs').addObligation
                       (.growthFaultDistance carrier faultDistance)).addDetector detector
          .ok (menv, st2)
  | .stabilize carrier rounds detector => do
      match st.carrier? carrier with
      | none    => .error (.carrierNotFound carrier)
      | some cs =>
          ensure cs.live (.carrierNotLive carrier)
          let st1 := (st.addObligation (.stabilizationRounds carrier rounds)).addDetector detector
          .ok (menv, st1)
  | .graft carrier into codeDistance detector => do
      match st.carrier? carrier with
      | none    => .error (.carrierNotFound carrier)
      | some cs =>
          ensure cs.live (.carrierNotLive carrier)
          -- the block-backed SOURCE being grafted must be live + owned (checkSwitch discipline).
          requireOwnedLive Γ cs.carrier.code
          -- the TARGET must be `external` (a `.block` graft target needs a real switch
          -- certificate the v1 AST does not carry — REJECTED, not aliased in).
          let ob? ← resolveSwitchTarget into "escape/graft target not materialised in ChainQ"
          let st1 := match ob? with | some o => st.addObligation o | none => st
          let cs' : CarrierState :=
            { cs with carrier := { cs.carrier with code := into }, codeDist := some codeDistance }
          let st2 := ((st1.setCarrier carrier cs').addObligation
                       (.escapeGraft carrier codeDistance)).addDetector detector
          .ok (menv, st2)
  | .transitionToMatchable carrier to codeDistance detector => do
      match st.carrier? carrier with
      | none    => .error (.carrierNotFound carrier)
      | some cs =>
          ensure cs.live (.carrierNotLive carrier)
          -- the grafted-code SOURCE must be live + owned (checkSwitch discipline).
          requireOwnedLive Γ cs.carrier.code
          -- the FINAL matchable TARGET must be `external` (same SwitchCert caveat).
          let ob? ← resolveSwitchTarget to "escape-transition target not materialised in ChainQ"
          let st1 := match ob? with | some o => st.addObligation o | none => st
          let cs' : CarrierState :=
            { cs with carrier := { cs.carrier with code := to }, codeDist := some codeDistance }
          let st2 := ((st1.setCarrier carrier cs').addObligation
                       (.escapeTransition carrier codeDistance)).addDetector detector
          .ok (menv, st2)
  | .switchBlock _ _ _ =>
      -- routed by `checkProtocol` to `checkSwitchBlockOp` (the only Γ-UPDATING path); a
      -- direct `checkOp` call cannot thread the post-switch TypedEnv, so it is rejected here.
      .error (.other "switchBlock must be checked via checkProtocol (it updates Γ); see checkSwitchBlockOp")
  | .postselect cond => do
      match cond with
      | .fullDetectors        => .ok (menv, st.addObligation .fullPostselection)
      | .syndromeEq name _    =>
          ensure (st.knowsDetector name) (.unknownDetector name)
          .ok (menv, st)
      | .taggedDetectors name =>
          -- MagicQ v1 has no real detector TAGS: `taggedDetectors` is a detector-NAME alias,
          -- scope-checked against produced detector names (it lowers to LS `.byDetector`, not `.byTag`).
          ensure (st.knowsDetector name) (.unknownDetector name)
          .ok (menv, st)
      | .predicate p          => do
          checkMagicPred st p           -- scope only; the Boolean value stays deferred
          .ok (menv, st)
      | .decoderGap threshold => .ok (menv, st.addObligation (.decoderGap threshold))
  | .measureSyndrome inputs output outCarrier outCode quality syndromes => do
      -- consume the input magic states.  Standard `|A₀⟩ = T|+⟩` (`.T`/`.A0`) only; duplicates ⇒
      -- already-consumed.  `.Tdg` (the conjugate) and `.Y` are REJECTED — the projected output
      -- is always `.T`, so silently accepting `.Tdg` would mis-relabel the conjugate state.
      -- GENERIC ARITY: the "exactly 15" of Bravyi–Kitaev 15-to-1 is a property of the
      -- `rm15_to_1` LIBRARY protocol, NOT enforced by this primitive.
      let menv1 ← inputs.foldlM (fun (m : MagicEnv) (rid : ResourceId) =>
        match m.slot? rid with
        | none      => .error (.resourceNotFound rid)
        | some slot =>
            if slot.consumed then .error (.resourceAlreadyConsumed rid)
            else match slot.res with
              | .pending _ => .error (.notAState rid)
              | .state s   =>
                  if s.basis.aType then .ok (m.consume rid)
                  else .error (.basisIncompatible rid s.basis)) menv
      ensure (!menv1.has output) (.resourceIdReused output)
      ensure (st.carrier? outCarrier).isNone (.carrierIdReused outCarrier)
      ensureNoBlockAlias st outCode
      -- the output carrier CLAIMS the (block) code to hold the projected state → live + owned.
      let (_, ob?) ← resolveCode Γ true outCode "syndrome-measure output carrier not materialised in ChainQ"
      let st0 := match ob? with | some o => st.addObligation o | none => st
      -- The projected output lands on the result code, whose distance is a STRUCTURAL fact
      -- this pass does not prove.  We deliberately do NOT self-stamp the carrier's `codeDist`
      -- from the SAME `quality` record carried by the output (that would make the output
      -- codeDistance gate a tautology `d ≤ d`).  This op establishes NO gated protocol-op
      -- distance, so the carrier's distances stay `none`: any GATED fault/code-distance promise
      -- on the output is then correctly REJECTED at `output` (no op established it), and an
      -- honest factory leaves those `none`, recording its real distance/threshold as deferred.
      let cs : CarrierState :=
        { carrier := { code := outCode, logicalCount := 1, quality := quality },
          live := true, faultDist := none, codeDist := none }
      -- RETIRE the input carriers: their magic states are now consumed, so they
      -- must NOT be left live in `finalCarriers`.
      let stR := inputs.foldl (fun s rid =>
        match menv1.slot? rid with
        | some slot => match slot.res with | .state inp => s.retireCarrier inp.carrier | .pending _ => s
        | none      => s) st0
      -- surface the output quality's deferred claims (success probability / threshold / output error).
      let st1 := (stR.setCarrier outCarrier cs).addQualityClaims quality
      -- each measured syndrome becomes a postselectable detector AND a deferred decoding
      -- obligation (e.g. the non-Pauli RM-15 `η`, which the binary CSS surrogate does not prove).
      let st1b := syndromes.foldl (fun s name => (s.addDetector name).addObligation (.syndromeDecoding name)) st1
      -- mark the inputs consumed in the summary.
      let st2 := inputs.foldl (fun s rid => s.addConsumed rid) st1b
      let menv2 := menv1.push { id := output, res := .state { basis := .T, carrier := outCarrier, quality := quality } }
      .ok (menv2, st2)
  | .discard resource => do
      match menv.slot? resource with
      | none      => .error (.resourceNotFound resource)
      | some slot =>
          ensure (!slot.consumed) (.resourceAlreadyConsumed resource)
          -- discarding RETIRES the resource's carrier (it is no longer usable by later ops).
          let st1 := match slot.res with | .state s => st.retireCarrier s.carrier | .pending _ => st
          .ok (menv.consume resource, st1.addConsumed resource)
  | .output resource => do
      match menv.slot? resource with
      | none      => .error (.resourceNotFound resource)
      | some slot =>
          ensure (!slot.consumed) (.resourceAlreadyConsumed resource)
          match slot.res with
          | .pending _ => .error (.notAState resource)
          | .state s   =>
              match st.carrier? s.carrier with
              | none    => .error (.outputWithoutCarrier resource)
              | some cs =>
                  ensure cs.live (.outputWithoutCarrier resource)
                  -- the protocol does NOT return a magic state unless its declared
                  -- fault/code-distance promises have been ESTABLISHED by a prior op:
                  -- `grow` sets faultDist, `graft` sets codeDist.  Distillation
                  -- establishes neither (its output distance is a deferred STRUCTURAL
                  -- obligation), so an honest distill output declares no gated distance
                  -- — and any inflated distance claim on it is rejected right here.
                  let _ ← match s.quality.faultDistance with
                    | none   => .ok ()
                    | some d => match cs.faultDist with
                        | some d' => ensure (d ≤ d') (.outputWithoutQuality resource "faultDistance")
                        | none    => .error (.outputWithoutQuality resource "faultDistance")
                  let _ ← match s.quality.codeDistance with
                    | none   => .ok ()
                    | some d => match cs.codeDist with
                        | some d' => ensure (d ≤ d') (.outputWithoutQuality resource "codeDistance")
                        | none    => .error (.outputWithoutQuality resource "codeDistance")
                  -- returning the state RETIRES its carrier (no later op may use it).
                  .ok (menv.consume resource,
                       ((st.addOutput s).addConsumed resource).retireCarrier s.carrier)

/-! ## §4. The whole-protocol checker and its summary. -/

/-- A CHECKED protocol summary: the output magic resources, the consumed resource
    ids, the final carrier states, and the explicit DEFERRED obligations (external
    carriers, switch certificates, decoder gaps, distillation thresholds, …).  On a
    successful check `leaked` is always `[]` — a nonempty leak is an ERROR (see
    `checkProtocol`), so it is reported there, not here. -/
structure CheckedProtocol where
  name          : String
  outputs       : List MagicState
  consumed      : List ResourceId
  finalCarriers : List (CarrierId × CarrierState)
  deferred      : List Obligation
  leaked        : List ResourceId
  deriving Repr

/-- **Check a whole protocol.**  Folds `checkOp` through the op list, then packages
    the summary (outputs / consumed / final carriers / deferred obligations).
    Protocol-level symbolic spec lines are surfaced as `specClaim` obligations.
    LINEARITY by default: any magic state never consumed (by `output`/`discard`) is a
    `resourceLeak` ERROR — protocol authors must explicitly dispose of every live state. -/
def checkProtocol (Γ0 : TypedEnv) (p : Protocol) : Except MagicError CheckedProtocol := do
  -- thread (Γ, Σ, st): `switchBlock` UPDATES Γ via `checkSwitchBlockOp`; every other op
  -- leaves Γ unchanged.  The final Γ is internal (the summary does not expose it).
  let (_Γ, menv, st) ← p.ops.foldlM
    (fun (acc : TypedEnv × MagicEnv × CheckState) op =>
      match op with
      | .switchBlock carrier tgt detector => checkSwitchBlockOp acc.1 acc.2.1 acc.2.2 carrier tgt detector
      | _ => do
          let (menv', st') ← checkOp acc.1 acc.2.1 acc.2.2 op
          .ok (acc.1, menv', st'))
    ((Γ0, ({} : MagicEnv), ({} : CheckState)))
  let leaks := menv.leaked
  if !leaks.isEmpty then
    .error (.resourceLeak leaks)
  else
    .ok {
      name          := p.name,
      outputs       := st.outputs,
      consumed      := st.consumed,
      finalCarriers := st.carriers,
      deferred      := st.obligations ++ p.spec.map Obligation.specClaim,
      leaked        := leaks }

/-- Convenience: does the protocol check (against an empty environment)? -/
def checks? (p : Protocol) : Bool := mok? (checkProtocol ⟨[]⟩ p)

/-- Convenience: check the protocol against an explicit Γ. -/
def checksIn? (Γ : TypedEnv) (p : Protocol) : Bool := mok? (checkProtocol Γ p)

/-! ## §5. The REAL ChainQ-backed block switch (reuses `TypeChecker.checkSwitch`). -/

-- a legal one-qubit teleport switch with an ESTABLISHED distance ≥ 1 is ACCEPTED, via the
-- EXISTING TypeChecker checker — no duplicate algebra, no fake acceptance:
example : mok? (checkBlockSwitch TypeChecker.oneQDistanceEnv 0
    ⟨TypeChecker.oneQWithDistance, TypeChecker.oneQDistanceSwitchCert, 1⟩) = true := by decide
-- the SAME switch REJECTS when a HIGHER distance (2) than is established is required:
example : mok? (checkBlockSwitch TypeChecker.oneQDistanceEnv 0
    ⟨TypeChecker.oneQWithDistance, TypeChecker.oneQDistanceSwitchCert, 2⟩) = false := by decide
-- the v1 protocol path still REJECTS a `.block` grow/graft target (it carries no cert)…
example : (resolveSwitchTarget (.block 0) "x").toOption.isSome = false := by decide
-- …while an `external` target is recorded as a deferred obligation:
example : (resolveSwitchTarget (.external "color-d5") "x").toOption.isSome = true := by decide

/-- A v2 protocol that injects on a real block carrier, then performs a CHECKED code switch
    (threading Γ via `checkSwitchBlockOp`), requiring post-switch distance `d`. -/
def switchProto (d : Nat) : Protocol :=
  { name := "v2-switch"
    ops := [ .inject .unitary .T 0 (.block 0) 0 {}
           , .switchBlock 0 ⟨TypeChecker.oneQWithDistance, TypeChecker.oneQDistanceSwitchCert, d⟩ "switch.detector"
           , .output 0 ] }

-- the v2 checked switch with an established distance (1) ACCEPTS, threading the post-switch Γ…
example : checksIn? TypeChecker.oneQDistanceEnv (switchProto 1) = true := by decide
-- …and the SAME switch requiring a higher distance (2) than is established REJECTS:
example : checksIn? TypeChecker.oneQDistanceEnv (switchProto 2) = false := by decide

/-! ## §6. General Boolean POSTSELECTION predicates at the MagicQ level (scope-checked). -/

/-- A protocol postselecting a NESTED Boolean predicate over a produced detector. -/
def predProtoOk : Protocol :=
  { name := "pred-ok"
    ops := [ .inject .unitary .T 0 (.external "c") 0 {}
           , .assumeLogicalCheck 0 { idx := 0, axis := .hxy } "d1" "test double-check"
           , .postselect (.predicate (.and (.detector "d1") (.not (.detector "d1"))))
           , .output 0 ] }
/-- The same protocol, but the predicate references an UNPRODUCED detector. -/
def predProtoBad : Protocol :=
  { name := "pred-bad"
    ops := [ .inject .unitary .T 0 (.external "c") 0 {}
           , .assumeLogicalCheck 0 { idx := 0, axis := .hxy } "d1" "test double-check"
           , .postselect (.predicate (.or (.detector "d1") (.detector "nope")))
           , .output 0 ] }

-- a nested Boolean predicate over KNOWN detector/tag atoms is ACCEPTED…
example : checks? predProtoOk = true := by decide
-- …and an UNKNOWN atom anywhere in the predicate is REJECTED (scope enforced through the tree)…
example : checks? predProtoBad = false := by decide
-- …for the RIGHT reason (the unproduced detector), not some unrelated failure:
example : (match checkProtocol ⟨[]⟩ predProtoBad with | .error (.unknownDetector "nope") => true | _ => false) = true := by decide

end MagicQ
