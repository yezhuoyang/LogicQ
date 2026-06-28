/-
  Compiler.ChainQ2Mixed.Primitive — the SOUND, CHECKED primitive layer over the Mixed IR.

  `MixPrim` is a single expression-level surface for the core logical QEC primitives
  ChainQ needs, and `checkPrim?` checks one is ALLOWED on the addressed logical
  blocks/qubits/codes by ROUTING it through the EXISTING checked kernel — it does not
  re-implement checker logic.  Every `MixPrim` arm is a GENUINELY-checked operation
  (`checkInstr` / `compileScheduled?`); there is no weak arm.

  WHAT IS A PRIMITIVE (vs. sugar/realization).  A `MixPrim` is something that must
  survive as first-class Mixed-IR structure with a real legality check: PPM, parallel
  PPM, block-wide transversal, transversal CNOT (single + batched), automorphism, code
  switch, and the deferred magic obligation.  Two things are DELIBERATELY NOT base
  primitives:
    * the VERIFIED homomorphic CNOT is exactly `transversalCNOT` / `transversalBatch`
      (the physical incidence induces the requested logical CNOT, checked by
      `checkTransversalCNOT(Batch)` — which REJECTS a degenerate/zero map because it
      then fails to induce the requested action).  There is no separate "homomorphic
      CNOT primitive".
    * GPPM is NOT a base primitive AND NOT a (verified) compilation rule: `measure`
      compiles to NATIVE one- or two-body PPM only (`Compile.lean`).  The chain-level
      homomorphic-CNOT / GPPM protocols live ONLY in the `ExternalClaim` layer below
      (Γ-bound but NOT `WellTyped`-verified — induced action is `externalProtocolCert`).

  EXTERNAL CLAIMS (NOT verified legality).  The `CodeSwitch.QLDPCPapers` chain-level
  protocol certificates (`HomomorphicCNOTProtocol` / `GPPMProtocol`) cannot have their
  induced LOGICAL action checked at this layer: their `PhysMap` is over physical qubits
  (width `n`) while a `Block`'s stabilizers/logicals are symplectic (width `2n`) — a
  representation gap.  So they are exposed ONLY as `ExternalClaim`s: `externalClaimCheck?`
  binds them to the addressed `TypedEnv` blocks (existence/liveness, dims = actual code
  sizes, physical sparsity, NON-DEGENERACY/rank, frame qubits valid) and returns an
  OBLIGATION-carrying `ExternalClaimArtifact` that is explicitly NOT a `CheckedPrimitive`
  and carries NO `WellTyped` legality — the induced-action correctness stays an
  `externalProtocolCert` obligation.  A dimension-correct ZERO map is REJECTED (rank 0).
-/
import Compiler.ChainQ2Mixed.Schedule
import Compiler.CodeSwitch.QLDPCPapers
import TypeChecker.Soundness

namespace Compiler.ChainQ2Mixed

open Compiler TypeChecker PPM ChainQ.GF2 Logical Compiler.CodeSwitch

/-! ## §P.1. Deferred obligations. -/

/-- The physical/fault-tolerance details a checked primitive does NOT discharge — each
    recorded EXPLICITLY so nothing is silently assumed. -/
inductive PrimitiveObligation
  | qstabLoweringDeferred        -- no detailed QStab program emitted
  | syndromeExtractionDeferred   -- no syndrome-extraction circuit
  | decoderDeferred              -- no decoder / threshold behavior
  | ftBoundaryDeferred           -- distance / fault-distance / circuit FT not proven
  | logicalAncillaDeferred       -- requires (unprepared) logical ancilla states
  | twistFreeSurgeryDeferred     -- requires twist-free surgery machinery (not emitted)
  | externalProtocolCert         -- an external protocol whose induced LOGICAL action is NOT verified here
  | magicStateDeferred           -- a magic-state factory must discharge this (no Step)
  deriving DecidableEq, BEq, Repr

/-! ## §P.2. The verified primitive surface. -/

/-- A MixIR primitive request — a single logical QEC operation, each arm GENUINELY
    checked by an existing kernel.  (Homomorphic CNOT = `transversalCNOT`/`transversalBatch`;
    GPPM is NOT a primitive and NOT a verified rule — it is only an `ExternalClaim`.) -/
inductive MixPrim
  | ppm              (r : CVar) (P : MTarget)                      -- CONVENIENCE form of `ppmFragment (.meas r P)` (a single native measurement)
  | ppmFragment      (s : PPM.Stmt)                                -- the general PPM fragment (e.g. a teleportation gadget); `ppm` is its single-`meas` specialization
  | parallelPPM      (mode : ScheduleMode) (sched : Schedule)
  | transversal      (block : Nat) (g : BoolMat)                  -- a BLOCK-WIDE transversal gate
  | transversalCNOT  (spec : TransversalCNOTSpec)                  -- the verified (homomorphic) logical CNOT
  | transversalBatch (spec : TransversalCNOTBatchSpec)             -- the verified high-rate (homomorphic) batch CNOT
  | automorphism     (block : Nat) (M : BoolMat)
  | codeSwitch       (block : Nat) (target : Block) (cert : SwitchCert)
  | pauli            (q : LQubit) (p : PLetter)                    -- a logical Pauli applied to the carrier
  | magic            (ob : MagicObligation)                        -- deferred, TYPED magic obligation (e.g. T)

/-! ## §P.3. The unified checker — routes each primitive to the EXISTING kernel. -/

/-- Legality of a primitive, returning the post-op typed env + resource state.  EVERY
    arm reuses an existing checked kernel: `checkInstr` (ppm / transversal / CNOT /
    automorphism / switch / magic) or `compileScheduled?` (parallel PPM, with its
    stratified paper-accurate certificate). -/
def primCheck (caps : List Capability) (Γ : TypedEnv) (R : PPMState) :
    MixPrim → Except TypeError (TypedEnv × PPMState)
  | .ppm r P              => checkInstr caps Γ R (.ppm (.meas r P))
  | .ppmFragment s        => checkInstr caps Γ R (.ppm s)
  | .parallelPPM mode S   => (compileScheduled? mode caps Γ R S).map (fun c => (c.envOut, c.resOut))
  | .transversal b g      => checkInstr caps Γ R (.transversal b g)
  | .transversalCNOT spec => checkInstr caps Γ R (.transversalCNOT spec)
  | .transversalBatch spec => checkInstr caps Γ R (.transversalCNOTBatch spec)
  | .automorphism b M     => checkInstr caps Γ R (.automorphism b M)
  | .codeSwitch b D cert  => checkInstr caps Γ R (.switch b D cert)
  | .pauli q p            => checkInstr caps Γ R (.pauli q p)
  | .magic ob             => checkInstr caps Γ R (.magic ob)

/-- The deferred obligations each primitive carries (the physical detail NOT discharged
    here). -/
def primObligations : MixPrim → List PrimitiveObligation
  | .ppm _ _ =>
      [.qstabLoweringDeferred, .syndromeExtractionDeferred, .decoderDeferred, .ftBoundaryDeferred]
  | .ppmFragment _ =>
      [.qstabLoweringDeferred, .syndromeExtractionDeferred, .decoderDeferred, .ftBoundaryDeferred]
  | .parallelPPM mode _ =>
      [.qstabLoweringDeferred, .syndromeExtractionDeferred, .decoderDeferred, .ftBoundaryDeferred]
        ++ (match mode with
            | .commutingWithAncilla => [.logicalAncillaDeferred, .twistFreeSurgeryDeferred]
            | _                     => [])
  | .transversal _ _      => [.ftBoundaryDeferred]
  | .transversalCNOT _    => [.qstabLoweringDeferred, .ftBoundaryDeferred]
  | .transversalBatch _   => [.qstabLoweringDeferred, .ftBoundaryDeferred]
  | .automorphism _ _     => [.ftBoundaryDeferred]
  | .codeSwitch _ _ _     => [.decoderDeferred, .ftBoundaryDeferred]
  | .pauli _ _            => [.ftBoundaryDeferred]
  | .magic _              => [.magicStateDeferred, .ftBoundaryDeferred]

/-! ## §P.4. The proof-carrying checked primitive + soundness. -/

/-- A CHECKED primitive: the request, the post-op env/resource state, and the PROOF
    that the case-appropriate kernel ACCEPTED it.  Obligations are DERIVED from the
    request (so they cannot drift from it). -/
structure CheckedPrimitive (caps : List Capability) (Γ₀ : TypedEnv) (R₀ : PPMState) where
  prim    : MixPrim
  envOut  : TypedEnv
  resOut  : PPMState
  checked : primCheck caps Γ₀ R₀ prim = .ok (envOut, resOut)

/-- The deferred obligations of a checked primitive (derived from its request). -/
def CheckedPrimitive.obligations {caps : List Capability} {Γ₀ : TypedEnv} {R₀ : PPMState}
    (cp : CheckedPrimitive caps Γ₀ R₀) : List PrimitiveObligation :=
  primObligations cp.prim

/-- `WellTyped`: the case-appropriate kernel accepted this primitive with the recorded
    output env/resources.  (Carried evidence — NOT a semantic-correctness / FT claim.) -/
def CheckedPrimitive.WellTyped {caps : List Capability} {Γ₀ : TypedEnv} {R₀ : PPMState}
    (cp : CheckedPrimitive caps Γ₀ R₀) : Prop :=
  primCheck caps Γ₀ R₀ cp.prim = .ok (cp.envOut, cp.resOut)

theorem CheckedPrimitive.wellTyped {caps : List Capability} {Γ₀ : TypedEnv} {R₀ : PPMState}
    (cp : CheckedPrimitive caps Γ₀ R₀) : cp.WellTyped := cp.checked

/-- **The primitive checker.** -/
def checkPrim? (caps : List Capability) (Γ : TypedEnv) (R : PPMState) (p : MixPrim) :
    Except TypeError (CheckedPrimitive caps Γ R) :=
  match h : primCheck caps Γ R p with
  | .ok (Γ', R') => .ok { prim := p, envOut := Γ', resOut := R', checked := h }
  | .error e     => .error e

/-- **Soundness (modest, honest).**  A successfully-checked primitive is `WellTyped`
    (the appropriate existing kernel accepted it with the recorded output) and records
    exactly its deferred obligations.  NOT a claim of physical fault tolerance,
    operational equivalence, completed QStab lowering, or completeness. -/
theorem checkPrim?_sound (caps : List Capability) (Γ : TypedEnv) (R : PPMState) (p : MixPrim)
    {cp : CheckedPrimitive caps Γ R} (_h : checkPrim? caps Γ R p = .ok cp) :
    cp.WellTyped ∧ cp.obligations = primObligations cp.prim :=
  ⟨cp.wellTyped, rfl⟩

/-! ## §P.5. EXTERNAL CLAIMS — chain-level protocol certs (NOT verified legality). -/

/-- A chain-level protocol claim from `CodeSwitch.QLDPCPapers`.  These are NOT base
    primitives and NOT verified-legal: their induced LOGICAL action cannot be checked
    here (the chain-map / symplectic representation gap). -/
inductive ExternalClaim
  | homCNOT (protocol : HomomorphicCNOTProtocol)
  | gppm    (protocol : GPPMProtocol)

/-- Structural Γ-binding of a homomorphic-CNOT chain cert: the addressed blocks EXIST,
    are LIVE, DISTINCT, the chain map's dims MATCH the actual code sizes, it is physically
    sparse, it is NON-DEGENERATE (full column rank — so a ZERO map is rejected), and the
    byproduct-frame qubits are valid logical qubits.  This is STRUCTURAL binding only —
    it does NOT verify the induced logical CNOT action (that is `externalProtocolCert`). -/
def homCNOTBoundOk (Γ : TypedEnv) (p : HomomorphicCNOTProtocol) : Bool :=
  match Γ.block? p.control, Γ.block? p.target with
  | some cTB, some tTB =>
      cTB.block.live && tTB.block.live &&
      ! (p.control == p.target) &&
      p.cert.matchesDirection p.control p.target &&
      p.cert.structuralCheck &&
      decide (p.cert.chain.map.srcN = cTB.block.n) &&
      decide (p.cert.chain.map.tgtN = tTB.block.n) &&
      p.cert.chain.map.physicallyTransversal &&
      decide (rank p.cert.chain.map.matrix = p.cert.chain.map.srcN) &&   -- NON-DEGENERATE: rejects the zero map
      p.cert.byproductFrame.all (fun fr => validLQubit Γ fr.1)
  | _, _ => false

/-- **Structural well-formedness of an EXTERNAL GPPM target** (option B — generalized PPM):
    nonempty, no duplicate logical qubit, every factor a valid logical OF THE DATA BLOCK.
    Deliberately does NOT use `MTarget.wf` (which caps weight at 1–2 for a NATIVE PPM): a
    GENERALIZED PPM may be HIGH-WEIGHT (>2-body), so rejecting it solely because the native
    checker rejects it would be wrong.  This is STRUCTURAL binding only — the induced logical
    action remains an `externalProtocolCert` obligation (and the result is an
    `ExternalClaimArtifact`, never a `CheckedPrimitive`/`WellTyped`). -/
def gppmTargetWf (Γ : TypedEnv) (dataBlock : Nat) (P : PPM.MTarget) : Bool :=
  ! P.isEmpty &&
  targetOnBlock P dataBlock &&
  (P.map Prod.fst).all (fun q => validLQubit Γ q) &&
  (P.map Prod.fst).Nodup

/-- Structural Γ-binding of a GPPM chain cert: its inner homomorphic CNOT is bound, the
    data/ancilla blocks agree, and the measured logical Pauli is a well-formed GENERALIZED
    (possibly high-weight) target on the named DATA block (`gppmTargetWf`). -/
def gppmBoundOk (Γ : TypedEnv) (p : GPPMProtocol) : Bool :=
  homCNOTBoundOk Γ p.homCNOT &&
  p.homCNOT.control == p.dataBlock &&
  p.homCNOT.target == p.ancillaBlock &&
  gppmTargetWf Γ p.dataBlock p.target &&
  p.ancillaPrepared && p.ancillaMeasured && p.frameTracked

/-- An EXTERNAL-claim artifact: the claim is STRUCTURALLY bound to the env, but its
    induced logical action is UNVERIFIED.  It is NOT a `CheckedPrimitive` and carries NO
    `WellTyped` legality — `obligations` ALWAYS contains `externalProtocolCert`. -/
structure ExternalClaimArtifact (caps : List Capability) (Γ : TypedEnv) (R : PPMState) where
  claim       : ExternalClaim
  obligations : List PrimitiveObligation

/-- Structural binding check of an external claim (NOT a legality verification). -/
def externalClaimBoundOk (Γ : TypedEnv) : ExternalClaim → Bool
  | .homCNOT p => homCNOTBoundOk Γ p
  | .gppm p    => gppmBoundOk Γ p

/-- The obligations an external claim defers (induced-action correctness is external). -/
def externalClaimObligations : ExternalClaim → List PrimitiveObligation
  | .homCNOT _ => [.externalProtocolCert, .qstabLoweringDeferred, .ftBoundaryDeferred]
  | .gppm _    => [.externalProtocolCert, .syndromeExtractionDeferred, .qstabLoweringDeferred,
                   .logicalAncillaDeferred, .ftBoundaryDeferred]

/-- Record an external protocol claim IF it is structurally bound to the env.  This is
    NOT `checkPrim?` and does NOT yield `WellTyped` — the returned artifact only asserts
    the structural Γ-binding (the induced logical action is `externalProtocolCert`). -/
def externalClaimCheck? (caps : List Capability) (Γ : TypedEnv) (R : PPMState) (c : ExternalClaim) :
    Except TypeError (ExternalClaimArtifact caps Γ R) :=
  if externalClaimBoundOk Γ c then
    .ok { claim := c, obligations := externalClaimObligations c }
  else
    .error (.certFailed "external protocol claim not structurally bound to the addressed live blocks (id / dims / sparsity / non-degeneracy / frame)")

/-! ## §P.5b. The VERIFIED homomorphic-CNOT BRIDGE — chain-cert `PhysMap` → symplectic
    induced LOGICAL action, via the verified `checkTransversalCNOTBatch`.

    This CLOSES the chain-level↔symplectic representation gap for the
    PHYSICALLY-TRANSVERSAL subclass.  The bridge does NOT bypass the protocol binding: it
    FIRST requires `homCNOTBoundOk Γ p` (blocks exist/live/distinct, `matchesDirection`,
    `structuralCheck`, dims = the actual `Γ` block sizes, `physicallyTransversal`,
    NON-DEGENERATE `rank = srcN`, valid frame), the recorded chain flags, and a nontrivial
    requested logical incidence; THEN, since a weight-≤1 `PhysMap` (`tgtN × srcN`) IS a
    physical CNOT incidence, it feeds it to the VERIFIED `checkTransversalCNOTBatch`, which
    LIFTS it to the width-`2n` symplectic map `Internal.cnotMap` and checks the INDUCED
    logical action equals the requested logical CNOT incidence on BOTH the X and Z bases,
    modulo the joint stabilizer RECOMPUTED from the actual `Γ` blocks (NOT the protocol's
    own — possibly bogus — `srcStab`/`tgtStab`).  So the homomorphic CNOT's induced logical
    action becomes a PROVED fact for this subclass, not an `externalProtocolCert` claim.

    SCOPE (honest, NOT overclaimed).  The VERIFIED content is: structural protocol binding +
    the INDUCED transversal logical CNOT action.  The chain-level HOMOLOGY commutation
    `∂φ = φ∂` is a RECORDED CLAIM (required set, but NOT recomputed — the protocol carries no
    boundary maps), and the full paper objects (binary lift / induced-homology map /
    injectivity / disjoint images) are NOT modeled.  A full GPPM additionally needs (i) the
    ancilla preparation,
    (ii) the ancilla-measurement-outcome = measured logical Pauli `g.target` step, and
    (iii) the byproduct frame — all STILL deferred.  So a GPPM is **NOT** promoted to a
    `CheckedPrimitive`; only its homomorphic-CNOT building block gains a verified
    induced-action certificate.  A non-transversal (multi-`1`-per-row) `PhysMap` has NO
    meaning as a tensor of physical CNOTs and is REJECTED at BOTH layers (the bridge's
    transversality guard AND the `homCNOTBoundOk` ExternalClaim binding, which itself
    already requires `physicallyTransversal`).  What stays a pure `ExternalClaim` is a
    TRANSVERSAL chain cert whose induced logical action is NOT confirmed equal to a
    requested logical CNOT incidence (the bridge was not run, or rejected it). -/

/-- The chain-level `PhysMap` (`tgtN × srcN`) reread as a `controlBlock × targetBlock`
    physical CNOT incidence (`nC × nT`), the shape `checkTransversalCNOTBatch` consumes
    (`incidence[i][j] = true` ⟺ a physical CNOT from control qubit `i` to target qubit
    `j`).  The induced-action proof goes through `Internal.cnotMap` (width `2n`), NOT
    through `PhysMap.applyRows` (width `n`, the wrong representation). -/
def physMapToIncidence (φ : PhysMap) : BoolMat := transpose φ.matrix φ.srcN

/-- A requested logical incidence is NONTRIVIAL (it requests ≥ 1 logical CNOT).  A
    "homomorphic CNOT" with an all-`false` logical incidence is a NO-OP (identity); this
    named bridge REJECTS it. -/
def logicalIncidenceNontrivial (L : BoolMat) : Bool := L.any (fun row => row.any (fun b => b))

/-- **Bridge a homomorphic-CNOT chain cert to the verified transversal-CNOT checker.**
    This is a PROTOCOL-bound bridge — it does NOT bypass the chain-cert binding.  It
    REQUIRES, before touching the incidence:
    * `homCNOTBoundOk Γ p` — blocks exist/live/distinct, `cert.matchesDirection`,
      `structuralCheck`, dims = the actual `Γ` block sizes, `physicallyTransversal`,
      NON-DEGENERATE `rank = srcN` (rejects the POSITIVE-dimension ZERO map, `rank 0 ≠ srcN`);
    * the recorded chain flags `claimedChainCommutes` ∧ `claimedStabilizerPreserved`
      (rejects a self-reported-invalid chain cert);
    * a NONTRIVIAL requested logical incidence (rejects the all-`false`/no-op `L` — and so
      also the degenerate `srcN = 0` 0-qubit no-op, since a 0-logical block admits no
      nontrivial requested CNOT, even though its `rank 0 = srcN 0` passes the rank gate);
    THEN feeds the `PhysMap` as a physical incidence to the verified
    `checkTransversalCNOTBatch`, which checks the INDUCED logical action equals `L` mod the
    joint stabilizer recomputed from the actual `Γ` blocks.

    HONEST SCOPE (NOT overclaimed): the chain-level HOMOLOGY commutation `∂φ = φ∂` is a
    RECORDED CLAIM (`claimed*`) — required to be set, but NOT recomputed over GF(2): the
    protocol does not carry the boundary maps `∂` (that recomputation, available only for a
    `DimensionJumpProtocol`'s `ChainMapSquare`, stays a deferred obligation).  So the
    VERIFIED content is exactly: structural protocol binding + the INDUCED transversal
    logical CNOT action.  The full paper objects (binary lift / induced-homology map /
    injectivity / disjoint images, 2407.18490 · 2510.07269 · 2510.06159) are NOT modeled. -/
def homCNOTBridge? (Γ : TypedEnv) (p : HomomorphicCNOTProtocol) (L : BoolMat) :
    Except TypeError TypedTransversalCNOTBatch :=
  if homCNOTBoundOk Γ p && p.cert.chain.claimedChainCommutes
      && p.cert.chain.claimedStabilizerPreserved && logicalIncidenceNontrivial L then
    checkTransversalCNOTBatch Γ
      { controlBlock := p.control, targetBlock := p.target,
        incidence := physMapToIncidence p.cert.chain.map, logicalIncidence := L }
  else
    .error (.certFailed "homomorphic-CNOT bridge: protocol not bound (homCNOTBoundOk / chain flags) or trivial logical incidence")

/-- **Protocol-binding evidence carried by an accepted bridge.**  A successful bridge
    necessarily passed the structural Γ-binding `homCNOTBoundOk` AND requested a nontrivial
    logical CNOT — so the bridge cannot accept an unbound or no-op protocol. -/
theorem homCNOTBridge_bound {Γ : TypedEnv} {p : HomomorphicCNOTProtocol} {L : BoolMat}
    {e : TypedTransversalCNOTBatch} (h : homCNOTBridge? Γ p L = .ok e) :
    homCNOTBoundOk Γ p = true ∧ logicalIncidenceNontrivial L = true := by
  simp only [homCNOTBridge?] at h
  split at h
  · rename_i hcond
    simp only [Bool.and_eq_true] at hcond
    exact ⟨hcond.1.1.1, hcond.2⟩
  · simp at h

/-- **Bridge soundness — the verified INDUCED LOGICAL ACTION** (the rep-gap closure).
    When the (protocol-bound) bridge ACCEPTS, the chain-cert's `PhysMap`, LIFTED to the
    width-`2n` symplectic map `Internal.cnotMap`, provably induces the requested logical
    CNOT incidence `L` on BOTH the X and Z logical bases, modulo the joint stabilizer
    recomputed from the actual `Γ` blocks.  This is `checkTransversalCNOTBatch_sound`
    re-exposed through the bridge — a GENUINE induced-action guarantee, NOT a vacuous
    wrapper.  Axioms: inherited from the pre-existing verified `checkTransversalCNOTBatch_sound`
    — `propext, Classical.choice, Quot.sound` (the classical axioms come from the GF(2)
    rank/span machinery in the audited transversal-CNOT soundness). -/
theorem homCNOTBridge_sound {Γ : TypedEnv} {p : HomomorphicCNOTProtocol} {L : BoolMat}
    {e : TypedTransversalCNOTBatch} {cTB tTB : TypedBlock}
    (hc : Γ.block? p.control = some cTB) (ht : Γ.block? p.target = some tTB)
    (h : homCNOTBridge? Γ p L = .ok e) :
    Internal.rowsEqualModStab (Internal.jointStab cTB.block tTB.block)
        (applyMap (cTB.block.n + tTB.block.n)
          (Internal.cnotMap cTB.block.n tTB.block.n (physMapToIncidence p.cert.chain.map))
          (Internal.jointLX cTB.block tTB.block))
        (Internal.expectedCNOTBatchLX cTB.block tTB.block L) = true ∧
      Internal.rowsEqualModStab (Internal.jointStab cTB.block tTB.block)
        (applyMap (cTB.block.n + tTB.block.n)
          (Internal.cnotMap cTB.block.n tTB.block.n (physMapToIncidence p.cert.chain.map))
          (Internal.jointLZ cTB.block tTB.block))
        (Internal.expectedCNOTBatchLZ cTB.block tTB.block L) = true := by
  simp only [homCNOTBridge?] at h
  split at h
  · have hs := checkTransversalCNOTBatch_sound hc ht h
    exact ⟨hs.2.2.2.1, hs.2.2.2.2⟩
  · simp at h

/-- A homomorphic-CNOT chain cert whose induced LOGICAL action has been VERIFIED by the
    bridge (transversal-realizable subclass).  Unlike `ExternalClaimArtifact`, the
    induced-CNOT action is a PROVED fact (`bridged` carries the verified-checker evidence
    `checked`); only the surrounding GPPM measurement-outcome + frame remain deferred. -/
structure BridgedHomCNOT (Γ : TypedEnv) where
  protocol         : HomomorphicCNOTProtocol
  logicalIncidence : BoolMat
  checked          : TypedTransversalCNOTBatch
  bridged          : homCNOTBridge? Γ protocol logicalIncidence = .ok checked

/-- Smart constructor: bridge a homomorphic-CNOT protocol against a requested logical
    incidence (or reject). -/
def bridgeHomCNOT? (Γ : TypedEnv) (p : HomomorphicCNOTProtocol) (L : BoolMat) :
    Except TypeError (BridgedHomCNOT Γ) :=
  match h : homCNOTBridge? Γ p L with
  | .ok e    => .ok { protocol := p, logicalIncidence := L, checked := e, bridged := h }
  | .error e => .error e

/-- **`BridgedHomCNOT` carries the PROTOCOL-BINDING evidence.**  Its protocol passed the
    structural Γ-binding (`homCNOTBoundOk`) and requested a nontrivial logical CNOT. -/
theorem BridgedHomCNOT.protocolBound {Γ : TypedEnv} (b : BridgedHomCNOT Γ) :
    homCNOTBoundOk Γ b.protocol = true ∧ logicalIncidenceNontrivial b.logicalIncidence = true :=
  homCNOTBridge_bound b.bridged

/-- **`BridgedHomCNOT` carries the verified induced action.**  The recorded evidence
    proves the lifted symplectic map induces the requested logical CNOT mod stabilizer. -/
theorem BridgedHomCNOT.inducesRequestedCNOT {Γ : TypedEnv} (b : BridgedHomCNOT Γ)
    {cTB tTB : TypedBlock}
    (hc : Γ.block? b.protocol.control = some cTB) (ht : Γ.block? b.protocol.target = some tTB) :
    Internal.rowsEqualModStab (Internal.jointStab cTB.block tTB.block)
        (applyMap (cTB.block.n + tTB.block.n)
          (Internal.cnotMap cTB.block.n tTB.block.n (physMapToIncidence b.protocol.cert.chain.map))
          (Internal.jointLX cTB.block tTB.block))
        (Internal.expectedCNOTBatchLX cTB.block tTB.block b.logicalIncidence) = true ∧
      Internal.rowsEqualModStab (Internal.jointStab cTB.block tTB.block)
        (applyMap (cTB.block.n + tTB.block.n)
          (Internal.cnotMap cTB.block.n tTB.block.n (physMapToIncidence b.protocol.cert.chain.map))
          (Internal.jointLZ cTB.block tTB.block))
        (Internal.expectedCNOTBatchLZ cTB.block tTB.block b.logicalIncidence) = true :=
  homCNOTBridge_sound hc ht b.bridged

/-- Bridge the homomorphic CNOT INSIDE a GPPM protocol.  REQUIRES the full GPPM protocol
    binding `gppmBoundOk Γ g` FIRST (data/ancilla block agreement, target well-formedness on
    the data block via `gppmTargetWf`, `ancillaPrepared`/`ancillaMeasured`/`frameTracked`,
    and — via `homCNOTBoundOk` — the hom-CNOT structural binding), THEN bridges the
    hom-CNOT.  Verifies the GPPM's data→ancilla homomorphic-CNOT INDUCED ACTION only; the
    GPPM MEASUREMENT (measuring the ancilla = measuring the data logical Pauli `g.target`),
    ancilla preparation, and byproduct frame remain DEFERRED — so a GPPM is NOT promoted to
    a `CheckedPrimitive`, only its hom-CNOT building block is verified. -/
def gppmBridgeHomCNOT? (Γ : TypedEnv) (g : GPPMProtocol) (L : BoolMat) :
    Except TypeError (BridgedHomCNOT Γ) :=
  if ! gppmBoundOk Γ g then
    .error (.certFailed "GPPM bridge: protocol not bound (data/ancilla block / target wf / prepared/measured/frame)")
  else
    bridgeHomCNOT? Γ g.homCNOT L

/-! ## §P.6. Test fixtures. -/

/-- A two-block bare environment (each block `n = k`). -/
def twoBlockEnv (k : Nat) : TypedEnv :=
  match TypedEnv.ofEnv? { blocks := [bareKBlock k, bareKBlock k] } with
  | .ok Γ    => Γ
  | .error _ => { blocks := [] }

def cnotEnv : TypedEnv := twoBlockEnv 1
def cnotSpec : TransversalCNOTSpec := { control := ⟨0, 0⟩, target := ⟨1, 0⟩, incidence := [[true]] }
def batchSpec : TransversalCNOTBatchSpec :=
  { controlBlock := 0, targetBlock := 1, incidence := [[true]], logicalIncidence := [[true]] }

-- external-claim fixtures (the protocol caller-supplied srcStab/tgtStab are BOGUS [] —
-- the binding uses Γ's real block sizes, and the rank gate rejects degenerate maps).
def hcEnv : TypedEnv := twoBlockEnv 2
def hcProt : HomomorphicCNOTProtocol :=
  { control := 0, target := 1,
    cert := { control := 0, target := 1, chain := goodChain, byproductFrame := [] },
    srcStab := [], tgtStab := [] }
def gppmProt : GPPMProtocol :=
  { dataBlock := 0, ancillaBlock := 1, target := [(⟨0, 0⟩, .Z)], homCNOT := hcProt,
    ancillaPrepared := true, ancillaMeasured := true, frameTracked := true }

/-! ## §P.7. Regression tests — POSITIVE (each verified primitive class). -/

example : ok? (checkPrim? [] (bareKEnv 4) PPMState.init (.ppm 0 [(⟨0, 0⟩, .Z)])) = true := by decide
example : ok? (checkPrim? [] (bareKEnv 4) PPMState.init (.parallelPPM .directDisjoint freshSched)) = true := by decide
example : ok? (checkPrim? [] (bareKEnv 4) PPMState.init (.parallelPPM .directSameOrId [sameLetterLayer])) = true := by decide
example : ok? (checkPrim? [] (bareKEnv 4) PPMState.init (.parallelPPM .commutingWithAncilla [overlapLayer])) = true := by decide
example : ok? (checkPrim? [] (bareKEnv 2) PPMState.init (.transversal 0 hGate2x2)) = true := by decide
example : ok? (checkPrim? [] cnotEnv PPMState.init (.transversalCNOT cnotSpec)) = true := by decide
example : ok? (checkPrim? [] cnotEnv PPMState.init (.transversalBatch batchSpec)) = true := by decide
example : ok? (checkPrim? [] (bareKEnv 2) PPMState.init (.automorphism 0 (idMat 4))) = true := by decide
example : ok? (checkPrim? [] bareEnv PPMState.init (.codeSwitch 0 bareBlock { kind := .teleport, f := identMat 2 })) = true := by decide
example : ok? (checkPrim? [] bareEnv PPMState.init (.magic { kind := .tGate, target := ⟨0, 0⟩ })) = true := by decide
example : ok? (checkPrim? [] bareEnv PPMState.init (.pauli ⟨0, 0⟩ .X)) = true := by decide
example : ok? (checkPrim? [] (bareKEnv 2) PPMState.init (.ppmFragment (progHAt ⟨0, 0⟩ ⟨0, 1⟩ 0 1))) = true := by decide

/-! ## §P.8. Regression tests — NEGATIVE (illegal primitives rejected). -/

example : ok? (checkPrim? [] (bareKEnv 4) PPMState.init (.ppm 0 [(⟨0, 9⟩, .Z)])) = false := by decide
example : ok? (checkPrim? [] (bareKEnv 4) { bound := [], dead := [⟨0, 0⟩] } (.ppm 1 [(⟨0, 0⟩, .Z)])) = false := by decide
example : ok? (checkPrim? [] (bareKEnv 4) PPMState.init (.parallelPPM .directDisjoint dupInLayer)) = false := by decide
def anticommSched : Schedule := [[(0, [(⟨0, 0⟩, .X)]), (1, [(⟨0, 0⟩, .Z)])]]
example : ok? (checkPrim? [] (bareKEnv 4) PPMState.init (.parallelPPM .directDisjoint anticommSched)) = false := by decide
example : ok? (checkPrim? [] (bareKEnv 4) PPMState.init (.parallelPPM .directSameOrId [overlapLayer])) = false := by decide
example : ok? (checkPrim? [] (bareKEnv 2) PPMState.init (.transversal 9 hGate2x2)) = false := by decide
example : ok? (checkPrim? [] cnotEnv PPMState.init
    (.transversalCNOT { control := ⟨0, 5⟩, target := ⟨1, 0⟩, incidence := [[true]] })) = false := by decide
example : ok? (checkPrim? [] cnotEnv PPMState.init
    (.transversalCNOT { control := ⟨5, 0⟩, target := ⟨1, 0⟩, incidence := [[true]] })) = false := by decide
example : ok? (checkPrim? [] cnotEnv PPMState.init
    (.transversalBatch { controlBlock := 0, targetBlock := 1, incidence := [[true, true]], logicalIncidence := [[true]] })) = false := by decide
example : ok? (checkPrim? [] bareEnv PPMState.init (.codeSwitch 0 (bareKBlock 2) { kind := .teleport, f := identMat 2 })) = false := by decide

-- THE VERIFIED homomorphic-CNOT path rejects a ZERO physical incidence that requests a
-- logical CNOT (checkTransversalCNOTBatch: the zero map induces identity, not the CNOT):
example : ok? (checkPrim? [] cnotEnv PPMState.init
    (.transversalBatch { controlBlock := 0, targetBlock := 1, incidence := [[false]], logicalIncidence := [[true]] })) = false := by decide

/-! ## §P.9. EXTERNAL-claim tests (NOT verified legality). -/

-- a structurally-bound external homomorphic-CNOT claim is RECORDED (id/dims/sparsity/
-- non-degeneracy/frame), carrying the externalProtocolCert obligation:
example : ok? (externalClaimCheck? [] hcEnv PPMState.init (.homCNOT hcProt)) = true := by decide
example : (externalClaimObligations (.homCNOT hcProt)).contains .externalProtocolCert = true := by decide
example : ok? (externalClaimCheck? [] hcEnv PPMState.init (.gppm gppmProt)) = true := by decide
-- a ZERO physical map is REJECTED even as an external claim (rank 0 ≠ srcN) — the audit fix:
def hcProtZero : HomomorphicCNOTProtocol :=
  { hcProt with cert := { hcProt.cert with
      chain := { goodChain with map := { srcN := 2, tgtN := 2, matrix := [[false, false], [false, false]] } } } }
example : homCNOTBoundOk hcEnv hcProtZero = false := by decide
example : ok? (externalClaimCheck? [] hcEnv PPMState.init (.homCNOT hcProtZero)) = false := by decide
-- a chain map with the WRONG dims (unrelated to the named blocks) is rejected:
def hcProtBadDim : HomomorphicCNOTProtocol :=
  { hcProt with cert := { hcProt.cert with
      chain := { goodChain with map := { srcN := 3, tgtN := 2, matrix := [[true, false], [false, true], [false, false]] } } } }
example : ok? (externalClaimCheck? [] hcEnv PPMState.init (.homCNOT hcProtBadDim)) = false := by decide
-- a claim on a NON-EXISTENT block is rejected:
example : ok? (externalClaimCheck? [] hcEnv PPMState.init
    (.homCNOT { hcProt with control := 7, cert := { hcProt.cert with control := 7 } })) = false := by decide
-- GPPM whose measured target is on the WRONG (ancilla) block is rejected:
example : ok? (externalClaimCheck? [] hcEnv PPMState.init (.gppm { gppmProt with target := [(⟨1, 0⟩, .Z)] })) = false := by decide

/-! ## §P.9b. EXTERNAL GPPM is GENERALIZED (Task 3, option B): the structural target predicate
    `gppmTargetWf` accepts HIGH-WEIGHT (>2-body) targets that the native `MTarget.wf` rejects —
    while the result is still only an `ExternalClaimArtifact` (NOT a `CheckedPrimitive`). -/

-- the WIDENING is real: a 3-body target is REJECTED by the native PPM checker but ACCEPTED as
-- a generalized external-GPPM target:
example : MTarget.wf [(⟨0, 0⟩, .Z), (⟨0, 1⟩, .Z), (⟨0, 2⟩, .Z)] = false := by decide
example : gppmTargetWf (bareKEnv 4) 0 [(⟨0, 0⟩, .Z), (⟨0, 1⟩, .Z), (⟨0, 2⟩, .Z)] = true := by decide
-- negatives still rejected: empty / wrong block / invalid logical / duplicate factor:
example : gppmTargetWf (bareKEnv 4) 0 [] = false := by decide
example : gppmTargetWf (twoBlockEnv 4) 0 [(⟨0, 0⟩, .Z), (⟨1, 0⟩, .Z)] = false := by decide
example : gppmTargetWf (bareKEnv 4) 0 [(⟨0, 9⟩, .Z)] = false := by decide
example : gppmTargetWf (bareKEnv 4) 0 [(⟨0, 0⟩, .Z), (⟨0, 0⟩, .X)] = false := by decide

-- END-TO-END: a HIGH-WEIGHT (3-body) external GPPM claim, bound to a 3-logical data block with
-- a matching (full-rank) chain map, is RECORDED (returns an `ExternalClaimArtifact`):
def chain3 : ChainMapCert :=
  { map := { srcN := 3, tgtN := 3,
             matrix := [[true, false, false], [false, true, false], [false, false, true]] },
    claimedChainCommutes := true, claimedStabilizerPreserved := true }
def hcProt3 : HomomorphicCNOTProtocol :=
  { control := 0, target := 1,
    cert := { control := 0, target := 1, chain := chain3, byproductFrame := [] },
    srcStab := [], tgtStab := [] }
def gppmProt3 : GPPMProtocol :=
  { dataBlock := 0, ancillaBlock := 1,
    target := [(⟨0, 0⟩, .Z), (⟨0, 1⟩, .Z), (⟨0, 2⟩, .Z)], homCNOT := hcProt3,
    ancillaPrepared := true, ancillaMeasured := true, frameTracked := true }
example : ok? (externalClaimCheck? [] (twoBlockEnv 3) PPMState.init (.gppm gppmProt3)) = true := by decide
-- it still carries the external-protocol obligation (NOT verified legality):
example : (externalClaimObligations (.gppm gppmProt3)).contains .externalProtocolCert = true := by decide

/-! ## §P.9c. The VERIFIED homomorphic-CNOT BRIDGE (chain-cert `PhysMap` → induced logical
    CNOT via `checkTransversalCNOTBatch`).  POSITIVE: a transversal `PhysMap` whose lift
    induces the requested CNOT is ACCEPTED (induced action PROVED, `homCNOTBridge_sound`);
    NEGATIVES: degenerate / wrong-action / non-transversal / wrong-block maps REJECTED. -/

/-- A 1×1 identity homomorphic-CNOT chain cert (its `PhysMap` `[[true]]` is a transversal
    matching). -/
def bridgeProt : HomomorphicCNOTProtocol :=
  { control := 0, target := 1,
    cert := { control := 0, target := 1,
              chain := { map := { srcN := 1, tgtN := 1, matrix := [[true]] },
                         claimedChainCommutes := true, claimedStabilizerPreserved := true },
              byproductFrame := [] },
    srcStab := [], tgtStab := [] }
-- POSITIVE: the identity physical incidence INDUCES the requested logical CNOT `[[true]]`:
example : ok? (homCNOTBridge? cnotEnv bridgeProt [[true]]) = true := by decide
example : ok? (bridgeHomCNOT? cnotEnv bridgeProt [[true]]) = true := by decide

-- NEGATIVE — a ZERO (degenerate) `PhysMap` induces IDENTITY, not the requested CNOT → REJECTED:
def bridgeProtZero : HomomorphicCNOTProtocol :=
  { bridgeProt with cert := { bridgeProt.cert with
      chain := { bridgeProt.cert.chain with map := { srcN := 1, tgtN := 1, matrix := [[false]] } } } }
example : ok? (homCNOTBridge? cnotEnv bridgeProtZero [[true]]) = false := by decide

-- NEGATIVE — passes DIMENSIONS but the requested logical action is WRONG: the identity
-- physical incidence DOES induce a CNOT, but here we request "no logical CNOT" (`[[false]]`),
-- so induced ≠ expected → REJECTED (the bogus-cert-with-right-dims case):
example : ok? (homCNOTBridge? cnotEnv bridgeProt [[false]]) = false := by decide

-- NEGATIVE — a NON-TRANSVERSAL `PhysMap` (a weight-2 column) has no CNOT-tensor meaning →
-- REJECTED by the transversality guard:
def bridgeProtDense : HomomorphicCNOTProtocol :=
  { control := 0, target := 1,
    cert := { control := 0, target := 1,
              chain := { map := { srcN := 2, tgtN := 2, matrix := [[true, true], [false, false]] },
                         claimedChainCommutes := true, claimedStabilizerPreserved := true },
              byproductFrame := [] },
    srcStab := [], tgtStab := [] }
example : ok? (homCNOTBridge? (twoBlockEnv 2) bridgeProtDense (idMat 2)) = false := by decide

-- NEGATIVE — a MISSING control block, and a SAME control/target block, are REJECTED:
example : ok? (homCNOTBridge? cnotEnv { bridgeProt with control := 7 } [[true]]) = false := by decide
example : ok? (homCNOTBridge? cnotEnv { bridgeProt with target := 0 } [[true]]) = false := by decide

-- NEGATIVE — the bridge does NOT bypass the protocol binding (`homCNOTBridge?` now REQUIRES
-- `homCNOTBoundOk` + chain flags + nontrivial L, so a bad protocol cannot sneak through):
--   * a MISMATCHED cert direction (`cert.control ≠ p.control`) fails `matchesDirection`:
example : ok? (homCNOTBridge? cnotEnv
    { bridgeProt with cert := { bridgeProt.cert with control := 5 } } [[true]]) = false := by decide
--   * a self-reported-invalid chain cert (false `claimedChainCommutes`) is REJECTED:
example : ok? (homCNOTBridge? cnotEnv
    { bridgeProt with cert := { bridgeProt.cert with
        chain := { bridgeProt.cert.chain with claimedChainCommutes := false } } } [[true]]) = false := by decide
--   * false `claimedStabilizerPreserved` is REJECTED:
example : ok? (homCNOTBridge? cnotEnv
    { bridgeProt with cert := { bridgeProt.cert with
        chain := { bridgeProt.cert.chain with claimedStabilizerPreserved := false } } } [[true]]) = false := by decide
--   * a ZERO physical map (positive dim) with a ZERO (no-op) logical incidence is REJECTED
--     (the `homCNOTBoundOk` rank gate rejects rank-0 ≠ srcN; a "homomorphic CNOT" is never a no-op):
example : ok? (homCNOTBridge? cnotEnv bridgeProtZero [[false]]) = false := by decide
--   * the degenerate srcN=0 0-qubit no-op (whose `rank 0 = srcN 0` PASSES the rank gate, so it
--     binds as an UNVERIFIED ExternalClaim) still CANNOT bridge: a 0-logical block admits no
--     nontrivial requested CNOT, so the bridge rejects it for every L (here `[]` and `[[]]`):
def bridgeProtSrcN0 : HomomorphicCNOTProtocol :=
  { control := 0, target := 1,
    cert := { control := 0, target := 1,
              chain := { map := { srcN := 0, tgtN := 0, matrix := [] },
                         claimedChainCommutes := true, claimedStabilizerPreserved := true },
              byproductFrame := [] },
    srcStab := [], tgtStab := [] }
example : homCNOTBoundOk (twoBlockEnv 0) bridgeProtSrcN0 = true := by decide   -- binds (unverified)…
example : ok? (homCNOTBridge? (twoBlockEnv 0) bridgeProtSrcN0 []) = false := by decide   -- …but cannot bridge
example : ok? (homCNOTBridge? (twoBlockEnv 0) bridgeProtSrcN0 [[]]) = false := by decide

-- The GPPM hom-CNOT bridge REQUIRES the full GPPM binding (`gppmBoundOk`) BEFORE bridging.
-- POSITIVE: `gppmProt`'s 2×2 identity `PhysMap` bridges (induces the batched CNOT) — but this
-- verifies ONLY the hom-CNOT action; the GPPM MEASUREMENT stays deferred (NOT a
-- `CheckedPrimitive`; there is NO `MixPrim.gppm`):
example : ok? (gppmBridgeHomCNOT? hcEnv gppmProt (idMat 2)) = true := by decide
-- NEGATIVE — the GPPM bridge rejects an unbound GPPM (no bypass of `gppmBoundOk`):
--   * wrong data block (homCNOT control ≠ dataBlock):
example : ok? (gppmBridgeHomCNOT? hcEnv { gppmProt with dataBlock := 5 } (idMat 2)) = false := by decide
--   * measured target NOT on the data block:
example : ok? (gppmBridgeHomCNOT? hcEnv { gppmProt with target := [(⟨1, 0⟩, .Z)] } (idMat 2)) = false := by decide
--   * ancilla not prepared / not measured / frame not tracked:
example : ok? (gppmBridgeHomCNOT? hcEnv { gppmProt with ancillaPrepared := false } (idMat 2)) = false := by decide
example : ok? (gppmBridgeHomCNOT? hcEnv { gppmProt with frameTracked := false } (idMat 2)) = false := by decide

/-! ## §P.10. The deferred obligations are recorded honestly. -/

example : (primObligations (.ppm 0 [(⟨0, 0⟩, .Z)])).contains .decoderDeferred = true := by decide
example : (primObligations (.magic { kind := .tGate, target := ⟨0, 0⟩ })).contains .magicStateDeferred = true := by decide
example : (primObligations (.parallelPPM .commutingWithAncilla [overlapLayer])).contains .twistFreeSurgeryDeferred = true := by decide
example : (primObligations (.parallelPPM .directDisjoint freshSched)).contains .twistFreeSurgeryDeferred = false := by decide

end Compiler.ChainQ2Mixed
