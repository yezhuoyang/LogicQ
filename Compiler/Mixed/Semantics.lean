/-
  Compiler.Mixed.Semantics — the ONE shared operational semantics of the mixed IR.

  This file owns the §4 evidence-carrying small-step semantics split out of
  Compiler/MixedSemantics.lean: the parametric interpretation `MixedInterp`, the
  unified `ExecState`, the `Step`/`Steps` relation, per-instruction realization +
  progress lemmas, the PPM-gadget frame lemmas, sequential composition, and the §5
  negative-step test theorems.  See `Compiler/MixedSemantics.lean` for the
  module-level design notes.
-/
import Compiler.Mixed.Check

namespace Compiler
open TypeChecker PPM ChainQ.GF2 Logical

/-! ## §4. One shared, EVIDENCE-CARRYING operational semantics.

    M12: every `Step` CONSUMES `checkInstr` evidence — there is no rule that runs a
    raw instruction with an invented environment.  A `switch`/`ppm` step transitions
    to the env/resource the CHECKER produced (`checkInstr ... = .ok (Γ', R')`), not an
    arbitrary `Γ'`.  The `ppm` step DELEGATES its quantum/classical/frame evolution to
    `PPM.Steps` (the existing PPM small-step semantics).  `magic` has NO rule (it
    type-checks as a deferred obligation but has no semantics), so `Step`/`Steps` is
    inhabited exactly by the magic-free direct + PPM fragment — `no_step_of_checkInstr_error`
    + `Step_implies_checkInstr` make this an honest, gap-free interface. -/

variable {Q : Type}

/-- How the (parametric) quantum carrier `Q` responds to operations: a symplectic
    Clifford map (`clifford`) for the direct fragment, and the PPM measurement
    back-action interface (`qinterp.proj`) for the PPM fragment.  Instantiate `Q`
    with a stabilizer tableau or density matrix. -/
structure MixedInterp (Q : Type) where
  clifford : BoolMat → Q → Q
  pauli    : PPM.PLetter → LQubit → Q → Q   -- apply a logical Pauli to the carrier (M18; NOT a Clifford basis-change)
  qinterp  : PPM.QInterp Q

/-- The unified execution state shared by ALL IR fragments (it carries exactly a
    `PPM.Config`'s components — `quantum`/`classical`/`frame` — plus the typed
    environment and the resource state the checker threads). -/
structure ExecState (Q : Type) where
  env       : TypedEnv
  resource  : PPMState
  frame     : PPM.Frame
  classical : PPM.Store
  quantum   : Q

/-- The number of physical qubits of block `b` (0 if absent). -/
def blockN (Γ : TypedEnv) (b : Nat) : Nat :=
  match Γ.block? b with | some tb => tb.block.n | none => 0

/-- Small-step semantics of a single mixed instruction, EVIDENCE-CARRYING: each
    rule has a `checkInstr … = .ok (Γ', R')` premise and steps to that CHECKED
    `(Γ', R')`.  The direct fragment (`transversal`/`automorphism`) acts on the
    carrier by its symplectic Clifford map (EXACT); a `switch` moves to the checked
    target env, preserving the logical state; a `ppm` delegates its
    quantum/classical/frame evolution to a terminating `PPM.Steps` run.  There is
    NO `magic` rule. -/
inductive Step (I : MixedInterp Q) (caps : List Capability) :
    MixedInstr → ExecState Q → ExecState Q → Prop where
  | transversal (b : Nat) (g : BoolMat) (s : ExecState Q) (Γ' : TypedEnv) (R' : PPMState)
      (hc : checkInstr caps s.env s.resource (.transversal b g) = .ok (Γ', R')) :
      Step I caps (.transversal b g) s
        { s with env := Γ', resource := R', quantum := I.clifford (Internal.transversalMap (blockN s.env b) g) s.quantum }
  | automorphism (b : Nat) (M : BoolMat) (s : ExecState Q) (Γ' : TypedEnv) (R' : PPMState)
      (hc : checkInstr caps s.env s.resource (.automorphism b M) = .ok (Γ', R')) :
      Step I caps (.automorphism b M) s
        { s with env := Γ', resource := R', quantum := I.clifford M s.quantum }
  | switch (b : Nat) (D : Block) (cert : SwitchCert) (s : ExecState Q) (Γ' : TypedEnv) (R' : PPMState)
      (hc : checkInstr caps s.env s.resource (.switch b D cert) = .ok (Γ', R')) :
      -- moves to the CHECKED target env `Γ'` (from `checkSwitch`), preserving the
      -- logical state (transparent coercion, ideal level).
      Step I caps (.switch b D cert) s { s with env := Γ', resource := R' }
  | ppm (stmt : PPM.Stmt) (s : ExecState Q) (Γ' : TypedEnv) (R' : PPMState)
      (ℓ : List PPM.Label) (q' : Q) (σ' : PPM.Store) (F' : PPM.Frame)
      (hc : checkInstr caps s.env s.resource (.ppm stmt) = .ok (Γ', R'))
      (hs : PPM.Steps I.qinterp ⟨s.quantum, s.classical, s.frame, stmt⟩ ℓ ⟨q', σ', F', .skip⟩) :
      -- DELEGATES the channel to PPM.Semantics: run `stmt` to a `skip` terminal,
      -- threading the carrier/store/frame.
      Step I caps (.ppm stmt) s
        { s with env := Γ', resource := R', quantum := q', classical := σ', frame := F' }
  | pauli (q : LQubit) (p : PPM.PLetter) (s : ExecState Q) (Γ' : TypedEnv) (R' : PPMState)
      (hc : checkInstr caps s.env s.resource (.pauli q p) = .ok (Γ', R')) :
      -- M18: a logical Pauli is APPLIED to the carrier (`I.pauli`), unlike a PPM
      -- `.frame` which only RECORDS a byproduct.  This is the real operational
      -- semantics of `xGate`/`zGate` — the carrier genuinely changes.
      Step I caps (.pauli q p) s
        { s with env := Γ', resource := R', quantum := I.pauli p q s.quantum }

/-- Reflexive-transitive closure over a mixed program. -/
inductive Steps (I : MixedInterp Q) (caps : List Capability) :
    LogicalExec → ExecState Q → ExecState Q → Prop where
  | nil (s : ExecState Q) : Steps I caps [] s s
  | cons {instr rest s s' s''} (h : Step I caps instr s s') (t : Steps I caps rest s' s'') :
      Steps I caps (instr :: rest) s s''

/-- **Checked instruction ⟹ type-checker acceptance.**  Every step consumes
    `checkInstr` evidence: if an instruction can step, it type-checks. -/
theorem Step_implies_checkInstr (I : MixedInterp Q) (caps : List Capability)
    (instr : MixedInstr) (s s' : ExecState Q) (h : Step I caps instr s s') :
    ∃ Γ' R', checkInstr caps s.env s.resource instr = .ok (Γ', R') := by
  cases h with
  | transversal _ _ _ Γ' R' hc => exact ⟨Γ', R', hc⟩
  | automorphism _ _ _ Γ' R' hc => exact ⟨Γ', R', hc⟩
  | switch _ _ _ _ Γ' R' hc => exact ⟨Γ', R', hc⟩
  | ppm _ _ Γ' R' _ _ _ _ hc _ => exact ⟨Γ', R', hc⟩
  | pauli _ _ _ Γ' R' hc => exact ⟨Γ', R', hc⟩

/-- **Invalid raw instruction cannot step through the checked interface.**  If
    `checkInstr` REJECTS an instruction (e.g. an invalid switch or a raw PPM that
    fails type-checking), no `Step` exists for it — the only way to step is through
    accepted evidence. -/
theorem no_step_of_checkInstr_error (I : MixedInterp Q) (caps : List Capability)
    (instr : MixedInstr) (s : ExecState Q) {e : TypeError}
    (herr : checkInstr caps s.env s.resource instr = .error e) :
    ¬ ∃ s', Step I caps instr s s' := by
  rintro ⟨s', h⟩
  obtain ⟨Γ', R', hc⟩ := Step_implies_checkInstr I caps instr s s' h
  rw [hc] at herr; exact absurd herr (by simp)

/-- **No step unless accepted** (decidable corollary): if `checkInstr` does not
    ACCEPT the instruction (`ok? … = false`), it cannot step.  Convenient for
    `by decide`-style negative tests on concrete invalid switch/PPM instructions. -/
theorem no_step_of_not_accepted (I : MixedInterp Q) (caps : List Capability)
    (instr : MixedInstr) (s : ExecState Q)
    (hck : ok? (checkInstr caps s.env s.resource instr) = false) :
    ¬ ∃ s', Step I caps instr s s' := by
  rintro ⟨s', h⟩
  obtain ⟨Γ', R', hc⟩ := Step_implies_checkInstr I caps instr s s' h
  rw [hc] at hck; simp [ok?] at hck

/-- **Magic is NOT executable.**  A `.magic` obligation type-checks (`checkInstr`
    accepts it) but has NO `Step` rule, so it cannot step — a magic-containing
    program is typed MODULO obligations but never executable.  (This is why
    `compile? .executable` requires `progNoMagic`.) -/
theorem no_step_magic (I : MixedInterp Q) (caps : List Capability) (ob : MagicObligation)
    (s : ExecState Q) : ¬ ∃ s', Step I caps (.magic ob) s s' := by
  rintro ⟨s', h⟩; cases h

/-- **Per-instruction realization (transversal).** -/
theorem Step_transversal_realizes (I : MixedInterp Q) (caps : List Capability) (b : Nat)
    (g : BoolMat) (s s' : ExecState Q) (h : Step I caps (.transversal b g) s s') :
    s'.quantum = I.clifford (Internal.transversalMap (blockN s.env b) g) s.quantum := by
  cases h; rfl

/-- **Per-instruction realization (automorphism).** -/
theorem Step_automorphism_realizes (I : MixedInterp Q) (caps : List Capability) (b : Nat)
    (M : BoolMat) (s s' : ExecState Q) (h : Step I caps (.automorphism b M) s s') :
    s'.quantum = I.clifford M s.quantum := by
  cases h; rfl

/-- **Per-instruction realization (Pauli) — the M18 contract.**  A `.pauli q p` step
    APPLIES the logical Pauli to the carrier (`I.pauli p q`), so the operational
    semantics of `xGate`/`zGate` genuinely changes the quantum state — it is NOT a
    record-only frame.  The executable interpreter (`Compiler.Sim.execMixed`) uses the
    SAME `I.pauli`, so running an emitted Pauli realizes exactly this Step. -/
theorem Step_pauli_realizes (I : MixedInterp Q) (caps : List Capability) (q : LQubit)
    (p : PPM.PLetter) (s s' : ExecState Q) (h : Step I caps (.pauli q p) s s') :
    s'.quantum = I.pauli p q s.quantum := by
  cases h; rfl

/-- **Progress (Pauli): a checked logical Pauli can step.** -/
theorem progress_pauli (I : MixedInterp Q) (caps : List Capability) (q : LQubit)
    (p : PPM.PLetter) (s : ExecState Q) {Γ' : TypedEnv} {R' : PPMState}
    (hc : checkInstr caps s.env s.resource (.pauli q p) = .ok (Γ', R')) :
    ∃ s', Step I caps (.pauli q p) s s' :=
  ⟨_, Step.pauli q p s Γ' R' hc⟩

/-- **A switch step uses the CHECKED target env.**  The post-switch `(env, resource)`
    is exactly what `checkInstr`/`checkSwitch` produced — not an arbitrary `Γ'`. -/
theorem Step_switch_uses_checked_env (I : MixedInterp Q) (caps : List Capability)
    (b : Nat) (D : Block) (cert : SwitchCert) (s s' : ExecState Q)
    (h : Step I caps (.switch b D cert) s s') :
    checkInstr caps s.env s.resource (.switch b D cert) = .ok (s'.env, s'.resource) := by
  cases h with | switch _ _ _ _ Γ' R' hc => exact hc

/-- **A switch step PRESERVES the logical state** (it transforms only env/resource). -/
theorem Step_switch_preserves_quantum (I : MixedInterp Q) (caps : List Capability) (b : Nat)
    (D : Block) (cert : SwitchCert) (s s' : ExecState Q) (h : Step I caps (.switch b D cert) s s') :
    s'.quantum = s.quantum := by
  cases h; rfl

/-- **PPM-step lift.**  A terminating `PPM.Steps` run of a CHECKED `ppm` fragment IS
    a mixed `Step` for `.ppm stmt` — the Mixed semantics delegates the
    measurement/frame channel to `PPM.Semantics`.  (Task 4: `Step` is now wired to
    `PPM.Step`, claiming carrier/store/frame evolution via the PPM interface — NOT
    end-to-end gadget unitary correctness, which `PPM.Semantics` itself defers.) -/
theorem ppm_step_lifts_ppm_semantics (I : MixedInterp Q) (caps : List Capability)
    (stmt : PPM.Stmt) (s : ExecState Q) {Γ' : TypedEnv} {R' : PPMState}
    {ℓ : List PPM.Label} {q' : Q} {σ' : PPM.Store} {F' : PPM.Frame}
    (hc : checkInstr caps s.env s.resource (.ppm stmt) = .ok (Γ', R'))
    (hs : PPM.Steps I.qinterp ⟨s.quantum, s.classical, s.frame, stmt⟩ ℓ ⟨q', σ', F', .skip⟩) :
    Step I caps (.ppm stmt) s
      { s with env := Γ', resource := R', quantum := q', classical := σ', frame := F' } :=
  Step.ppm stmt s Γ' R' ℓ q' σ' F' hc hs

/-- **Progress (direct fragment): a checked transversal can step.** -/
theorem progress_transversal (I : MixedInterp Q) (caps : List Capability) (b : Nat)
    (g : BoolMat) (s : ExecState Q) {Γ' : TypedEnv} {R' : PPMState}
    (hc : checkInstr caps s.env s.resource (.transversal b g) = .ok (Γ', R')) :
    ∃ s', Step I caps (.transversal b g) s s' :=
  ⟨_, Step.transversal b g s Γ' R' hc⟩

/-- **Progress (direct fragment): a checked automorphism can step.** -/
theorem progress_automorphism (I : MixedInterp Q) (caps : List Capability) (b : Nat)
    (M : BoolMat) (s : ExecState Q) {Γ' : TypedEnv} {R' : PPMState}
    (hc : checkInstr caps s.env s.resource (.automorphism b M) = .ok (Γ', R')) :
    ∃ s', Step I caps (.automorphism b M) s s' :=
  ⟨_, Step.automorphism b M s Γ' R' hc⟩

/-- **Progress (switch): a checked switch can step.** -/
theorem progress_switch (I : MixedInterp Q) (caps : List Capability) (b : Nat) (D : Block)
    (cert : SwitchCert) (s : ExecState Q) {Γ' : TypedEnv} {R' : PPMState}
    (hc : checkInstr caps s.env s.resource (.switch b D cert) = .ok (Γ', R')) :
    ∃ s', Step I caps (.switch b D cert) s s' :=
  ⟨_, Step.switch b D cert s Γ' R' hc⟩

/-- **Progress (PPM): a checked `ppm` fragment with a terminating run can step.**
    The PPM run (reaching a `skip` terminal) is the gadget's responsibility — it is
    discharged for the concrete gadgets (see `progress_ppm_progH`). -/
theorem progress_ppm (I : MixedInterp Q) (caps : List Capability) (stmt : PPM.Stmt)
    (s : ExecState Q) {Γ' : TypedEnv} {R' : PPMState}
    (hc : checkInstr caps s.env s.resource (.ppm stmt) = .ok (Γ', R'))
    (hs : ∃ ℓ q' σ' F', PPM.Steps I.qinterp ⟨s.quantum, s.classical, s.frame, stmt⟩ ℓ ⟨q', σ', F', .skip⟩) :
    ∃ s', Step I caps (.ppm stmt) s s' := by
  obtain ⟨ℓ, q', σ', F', hsteps⟩ := hs
  exact ⟨_, Step.ppm stmt s Γ' R' ℓ q' σ' F' hc hsteps⟩

/-- **No-stuck for the PPM H-gadget.**  A CHECKED `.ppm progH` from a fresh
    store/frame always steps: the gadget's `PPM.Steps`-to-`skip` run exists
    (`progH_frame`), so the direct + PPM fragment is non-stuck on this concrete
    gadget.  (The gadget's frame table is established for a fresh `Store`/`Frame`,
    matching a freshly-initialized ancilla.) -/
theorem progress_ppm_progH (I : MixedInterp Q) (caps : List Capability) (s : ExecState Q)
    {Γ' : TypedEnv} {R' : PPMState}
    (hcl : s.classical = PPM.Store.empty) (hfr : s.frame = PPM.Frame.id0)
    (hc : checkInstr caps s.env s.resource (.ppm PPM.progH) = .ok (Γ', R')) :
    ∃ s', Step I caps (.ppm PPM.progH) s s' := by
  obtain ⟨ℓ, q', σ', F', hsteps, _⟩ := PPM.progH_frame I.qinterp s.quantum .pos .pos
  exact ⟨_, Step.ppm PPM.progH s Γ' R' ℓ q' σ' F' hc (by rw [hcl, hfr]; exact hsteps)⟩

/-- **Frame-level progress for the PARAMETERIZED H gadget** `progHAt q anc r₁ r₂`
    (M13 task 3): for distinct fresh outcomes, a `PPM.Steps`-to-`skip` run exists
    (one branch — both `+1` outcomes), so the EMITTED H gadget (not just the fixed
    `progH`) terminates.  This is FRAME-LEVEL (control flow + store/frame); full
    gadget channel correctness is deferred. -/
theorem progHAt_steps (I : PPM.QInterp Q) (ρ : Q) (q anc : LQubit) (r₁ r₂ : CVar)
    (h : r₁ ≠ r₂) :
    ∃ ℓ ρ' σ' F',
      PPM.Steps I ⟨ρ, PPM.Store.empty, PPM.Frame.id0, progHAt q anc r₁ r₂⟩ ℓ ⟨ρ', σ', F', .skip⟩ :=
  ⟨_, _, _, _,
    (PPM.red_meas I r₁ _ .pos _).trans <| (PPM.red_meas I r₂ _ .pos _).trans <|
    (PPM.red_ite_pos I r₁ _ _ (by simp [PPM.Store.set, h])).trans <|
    (PPM.red_ite_pos I r₂ _ _ (by simp [PPM.Store.set])).trans <|
    PPM.Steps.single (PPM.Step.discard q)⟩

/-- **Full FOUR-BRANCH frame table for the PARAMETERIZED H gadget** (M14 task 4).
    For EVERY outcome pair `(s₁, s₂)`, `progHAt q anc r₁ r₂` (distinct fresh
    outcomes) reduces to a `skip` terminal whose Pauli frame on the ANCILLA is the
    expected H byproduct `hByp s₁ s₂` — the parameterized analogue of
    `PPM.progH_frame`.  This is FRAME / control-flow correctness (the classical
    byproduct table), NOT the full unitary/channel correctness of the gadget. -/
theorem progHAt_frame (I : PPM.QInterp Q) (ρ : Q) (q anc : LQubit) (r₁ r₂ : CVar)
    (h : r₁ ≠ r₂) (s₁ s₂ : PPM.Sign) :
    ∃ ℓ ρ' σ' F',
      PPM.Steps I ⟨ρ, PPM.Store.empty, PPM.Frame.id0, progHAt q anc r₁ r₂⟩ ℓ ⟨ρ', σ', F', .skip⟩ ∧
      F' anc = PPM.hByp s₁ s₂ := by
  cases s₁ <;> cases s₂
  · exact ⟨_, _, _, _,
      (PPM.red_meas I r₁ _ .pos _).trans <| (PPM.red_meas I r₂ _ .pos _).trans <|
      (PPM.red_ite_pos I r₁ _ _ (by simp [PPM.Store.set, h])).trans <|
      (PPM.red_ite_pos I r₂ _ _ (by simp [PPM.Store.set])).trans <|
      PPM.Steps.single (PPM.Step.discard q),
      by simp [PPM.Frame.id0, PPM.hByp]⟩
  · exact ⟨_, _, _, _,
      (PPM.red_meas I r₁ _ .pos _).trans <| (PPM.red_meas I r₂ _ .neg _).trans <|
      (PPM.red_ite_pos I r₁ _ _ (by simp [PPM.Store.set, h])).trans <|
      (PPM.red_ite_neg_frame I r₂ anc .X _ (by simp [PPM.Store.set])).trans <|
      PPM.Steps.single (PPM.Step.discard q),
      by simp [PPM.Frame.id0, PPM.Frame.mulAt, PPM.FPauli.mul, PPM.PLetter.toF, PPM.hByp]⟩
  · exact ⟨_, _, _, _,
      (PPM.red_meas I r₁ _ .neg _).trans <| (PPM.red_meas I r₂ _ .pos _).trans <|
      (PPM.red_ite_neg_frame I r₁ anc .Z _ (by simp [PPM.Store.set, h])).trans <|
      (PPM.red_ite_pos I r₂ _ _ (by simp [PPM.Store.set])).trans <|
      PPM.Steps.single (PPM.Step.discard q),
      by simp [PPM.Frame.id0, PPM.Frame.mulAt, PPM.FPauli.mul, PPM.PLetter.toF, PPM.hByp]⟩
  · exact ⟨_, _, _, _,
      (PPM.red_meas I r₁ _ .neg _).trans <| (PPM.red_meas I r₂ _ .neg _).trans <|
      (PPM.red_ite_neg_frame I r₁ anc .Z _ (by simp [PPM.Store.set, h])).trans <|
      (PPM.red_ite_neg_frame I r₂ anc .X _ (by simp [PPM.Store.set])).trans <|
      PPM.Steps.single (PPM.Step.discard q),
      by simp [PPM.Frame.id0, PPM.Frame.mulAt, PPM.FPauli.mul, PPM.PLetter.toF, PPM.hByp]⟩

/-- **No-stuck for the EMITTED (parameterized) H gadget.**  A CHECKED
    `.ppm (progHAt q anc r₁ r₂)` from a fresh store/frame with distinct fresh
    outcomes always steps — the M13 generalization of `progress_ppm_progH` to the
    gadget the compiler actually emits. -/
theorem progress_ppm_progHAt (I : MixedInterp Q) (caps : List Capability)
    (q anc : LQubit) (r₁ r₂ : CVar) (s : ExecState Q) {Γ' : TypedEnv} {R' : PPMState}
    (hcl : s.classical = PPM.Store.empty) (hfr : s.frame = PPM.Frame.id0) (hr : r₁ ≠ r₂)
    (hc : checkInstr caps s.env s.resource (.ppm (progHAt q anc r₁ r₂)) = .ok (Γ', R')) :
    ∃ s', Step I caps (.ppm (progHAt q anc r₁ r₂)) s s' := by
  obtain ⟨ℓ, q', σ', F', hsteps⟩ := progHAt_steps I.qinterp s.quantum q anc r₁ r₂ hr
  exact ⟨_, Step.ppm (progHAt q anc r₁ r₂) s Γ' R' ℓ q' σ' F' hc (by rw [hcl, hfr]; exact hsteps)⟩

/-- **Frame-level progress for the CZ gadget** `progCZAt c t anc r₁ r₂ r₃` (M22).
    Like `progHAt`, its two corrections are FLAT `.ite r .skip (.frame …)`, so the
    same `red_meas`/`red_ite_pos`/`discard` threading proves a `PPM.Steps`-to-`skip`
    run exists.  FRAME-LEVEL (control flow + store/frame) ONLY — the CZ carrier
    channel is NOT proven (`progCZAt` is an experimental placeholder gadget; CZ stays
    out of the exact-operational fragment). -/
theorem progCZAt_steps (I : PPM.QInterp Q) (ρ : Q) (c t anc : LQubit) (r₁ r₂ r₃ : CVar)
    (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃) :
    ∃ ℓ ρ' σ' F',
      PPM.Steps I ⟨ρ, PPM.Store.empty, PPM.Frame.id0, progCZAt c t anc r₁ r₂ r₃⟩ ℓ ⟨ρ', σ', F', .skip⟩ :=
  ⟨_, _, _, _,
    (PPM.red_meas I r₁ _ .pos _).trans <| (PPM.red_meas I r₂ _ .pos _).trans <|
    (PPM.red_meas I r₃ _ .pos _).trans <|
    (PPM.red_ite_pos I r₁ _ _ (by simp [PPM.Store.set, h12, h13])).trans <|
    (PPM.red_ite_pos I r₂ _ _ (by simp [PPM.Store.set, h23])).trans <|
    PPM.Steps.single (PPM.Step.discard anc)⟩

/-- **No-stuck for the emitted CZ gadget** — the M22 analogue of `progress_ppm_progHAt`. -/
theorem progress_ppm_progCZAt (I : MixedInterp Q) (caps : List Capability)
    (c t anc : LQubit) (r₁ r₂ r₃ : CVar) (s : ExecState Q) {Γ' : TypedEnv} {R' : PPMState}
    (hcl : s.classical = PPM.Store.empty) (hfr : s.frame = PPM.Frame.id0)
    (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃)
    (hc : checkInstr caps s.env s.resource (.ppm (progCZAt c t anc r₁ r₂ r₃)) = .ok (Γ', R')) :
    ∃ s', Step I caps (.ppm (progCZAt c t anc r₁ r₂ r₃)) s s' := by
  obtain ⟨ℓ, q', σ', F', hsteps⟩ := progCZAt_steps I.qinterp s.quantum c t anc r₁ r₂ r₃ h12 h13 h23
  exact ⟨_, Step.ppm (progCZAt c t anc r₁ r₂ r₃) s Γ' R' ℓ q' σ' F' hc (by rw [hcl, hfr]; exact hsteps)⟩

/-- **Frame-level progress for the S gadget** `progSAt q anc r₁ r₂` (M22, Task 3).
    `progSAt`'s three conditionals are NESTED, so the proof threads `red_ite_pos_into`
    / `red_ite_neg_into` (the no-`skip`-constraint reductions) through one outcome
    assignment (`r₁=+1, r₂=-1`) that reaches `skip`.  FRAME-LEVEL ONLY (the same
    boundary as `progHAt_steps`). -/
theorem progSAt_steps (I : PPM.QInterp Q) (ρ : Q) (q anc : LQubit) (r₁ r₂ : CVar)
    (h : r₁ ≠ r₂) :
    ∃ ℓ ρ' σ' F',
      PPM.Steps I ⟨ρ, PPM.Store.empty, PPM.Frame.id0, progSAt q anc r₁ r₂⟩ ℓ ⟨ρ', σ', F', .skip⟩ :=
  ⟨_, _, _, _,
    (PPM.red_meas I r₁ _ .pos _).trans <| (PPM.red_meas I r₂ _ .neg _).trans <|
    (PPM.red_ite_pos_into I r₁ _ _ _ (by simp [PPM.Store.set, h])).trans <|
    (PPM.red_ite_neg_into I r₂ _ _ _ (by simp [PPM.Store.set])).trans <|
    (PPM.Steps.single PPM.Step.seqSkip).trans <|
    (PPM.red_ite_pos I r₁ _ _ (by simp [PPM.Store.set, h])).trans <|
    (PPM.red_ite_pos I r₁ _ _ (by simp [PPM.Store.set, h])).trans <|
    PPM.Steps.single (PPM.Step.discard q)⟩

/-- **No-stuck for the emitted S gadget** (M22). -/
theorem progress_ppm_progSAt (I : MixedInterp Q) (caps : List Capability)
    (q anc : LQubit) (r₁ r₂ : CVar) (s : ExecState Q) {Γ' : TypedEnv} {R' : PPMState}
    (hcl : s.classical = PPM.Store.empty) (hfr : s.frame = PPM.Frame.id0) (hr : r₁ ≠ r₂)
    (hc : checkInstr caps s.env s.resource (.ppm (progSAt q anc r₁ r₂)) = .ok (Γ', R')) :
    ∃ s', Step I caps (.ppm (progSAt q anc r₁ r₂)) s s' := by
  obtain ⟨ℓ, q', σ', F', hsteps⟩ := progSAt_steps I.qinterp s.quantum q anc r₁ r₂ hr
  exact ⟨_, Step.ppm (progSAt q anc r₁ r₂) s Γ' R' ℓ q' σ' F' hc (by rw [hcl, hfr]; exact hsteps)⟩

/-- **Frame-level progress for the CNOT gadget** `progCNOTAt c t anc r₁ r₂ r₃` (M22,
    Task 3).  Its second correction is a 2-level nested `ite`; the proof threads
    `red_ite_pos_into` through the `r₁=r₂=r₃=+1` branch to `skip`.  FRAME-LEVEL ONLY. -/
theorem progCNOTAt_steps (I : PPM.QInterp Q) (ρ : Q) (c t anc : LQubit) (r₁ r₂ r₃ : CVar)
    (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃) :
    ∃ ℓ ρ' σ' F',
      PPM.Steps I ⟨ρ, PPM.Store.empty, PPM.Frame.id0, progCNOTAt c t anc r₁ r₂ r₃⟩ ℓ ⟨ρ', σ', F', .skip⟩ :=
  ⟨_, _, _, _,
    (PPM.red_meas I r₁ _ .pos _).trans <| (PPM.red_meas I r₂ _ .pos _).trans <|
    (PPM.red_meas I r₃ _ .pos _).trans <|
    (PPM.red_ite_pos I r₂ _ _ (by simp [PPM.Store.set, h23])).trans <|
    (PPM.red_ite_pos_into I r₁ _ _ _ (by simp [PPM.Store.set, h12, h13])).trans <|
    (PPM.red_ite_pos I r₃ _ _ (by simp [PPM.Store.set])).trans <|
    PPM.Steps.single (PPM.Step.discard anc)⟩

/-- **No-stuck for the emitted CNOT gadget** (M22). -/
theorem progress_ppm_progCNOTAt (I : MixedInterp Q) (caps : List Capability)
    (c t anc : LQubit) (r₁ r₂ r₃ : CVar) (s : ExecState Q) {Γ' : TypedEnv} {R' : PPMState}
    (hcl : s.classical = PPM.Store.empty) (hfr : s.frame = PPM.Frame.id0)
    (h12 : r₁ ≠ r₂) (h13 : r₁ ≠ r₃) (h23 : r₂ ≠ r₃)
    (hc : checkInstr caps s.env s.resource (.ppm (progCNOTAt c t anc r₁ r₂ r₃)) = .ok (Γ', R')) :
    ∃ s', Step I caps (.ppm (progCNOTAt c t anc r₁ r₂ r₃)) s s' := by
  obtain ⟨ℓ, q', σ', F', hsteps⟩ := progCNOTAt_steps I.qinterp s.quantum c t anc r₁ r₂ r₃ h12 h13 h23
  exact ⟨_, Step.ppm (progCNOTAt c t anc r₁ r₂ r₃) s Γ' R' ℓ q' σ' F' hc (by rw [hcl, hfr]; exact hsteps)⟩

/-! ## §4·M22. The gadget-correctness BOUNDARY (Task 3·4).

    Every compiler claim is tagged with the level at which it is established, so the
    correctness statement is parameterized by the boundary rather than implicitly
    assuming end-to-end correctness. -/

/-- The level at which a lowered op's correctness is established. -/
inductive GadgetBoundary
  | exact            -- operationally EXACT: emitted `Step` matches the ideal simulator (`execMixed`); PROVED
  | idealChannel     -- type-checked + `Step` via `PPM.Steps` (classical store + Pauli frame evolve);
                     -- the carrier channel (`QInterp.proj`) is UNCONSTRAINED = ASSUMED ideal
  | typecheckedOnly  -- lowers + type-checks (`compileOp_sound`); NO `Step` semantics (e.g. magic obligation)
  | provenChannel    -- (future) the physical carrier channel is PROVEN correct; NO op witnesses this yet
  deriving DecidableEq, Repr

/-- The correctness boundary of a source op's INTENDED lowering.  Direct Cliffords
    (`hGate`/`sGate` on a single-logical block, `blockTransversal` H/S) and logical
    Paulis (`xGate`/`zGate`) are `exact`; `cnotGate`/`czGate` and a multi-logical
    `hGate`/`sGate` lower to PPM gadgets at the `idealChannel` boundary (frame-level
    progress proved by `progCNOTAt_steps`/`progCZAt_steps`/…, carrier channel
    assumed); `measure` is `idealChannel` (native QMeas, ideal projector); `tGate` is
    `typecheckedOnly` (deferred magic, no `Step`).  NOTE `czGate` rides an EXPERIMENTAL
    placeholder gadget (`progCZAt`); `provenChannel` is currently witnessed by NO op. -/
def opBoundary : LogicalOp → GadgetBoundary
  | .hGate _ | .sGate _ | .xGate _ | .zGate _ | .blockTransversal _ _ => .exact
  | .cnotGate _ _ | .czGate _ _ | .measure _ _ => .idealChannel
  | .tGate _ => .typecheckedOnly

/-- **Sequential composition.**  Executions compose: `p` then `q` is an execution of
    `p ++ q`. -/
theorem Steps_append (I : MixedInterp Q) (caps : List Capability) {p q : LogicalExec}
    {s s' s'' : ExecState Q}
    (h₁ : Steps I caps p s s') (h₂ : Steps I caps q s' s'') : Steps I caps (p ++ q) s s'' := by
  induction h₁ with
  | nil _ => simpa using h₂
  | cons hstep _ ih => exact Steps.cons hstep (ih h₂)

/-- **Direct-fragment program realization.**  The emitted transversal step realizes
    the source gate's symplectic action; these compose along a program (via
    `Steps_append`).  Full PPM-gadget channel correctness is deferred. -/
theorem transversal_step_matches_action (I : MixedInterp Q) (caps : List Capability) (b : Nat)
    (g : BoolMat) (s s' : ExecState Q) (h : Step I caps (.transversal b g) s s')
    (M : BoolMat) (hM : MixedInstr.action s.env (.transversal b g) = some M) :
    s'.quantum = I.clifford M s.quantum := by
  cases h
  simp only [MixedInstr.action, blockN] at hM ⊢
  cases hb : s.env.block? b with
  | none => rw [hb] at hM; simp at hM
  | some tb => rw [hb] at hM; simp only [Option.map_some, Option.some.injEq] at hM; subst hM; rfl

/-! ### §5·M12 (negatives). Invalid raw instructions cannot STEP through the checked
    interface — `Step` only fires on accepted `checkInstr` evidence.  Stated over an
    arbitrary carrier `Q`, interpretation `I`, and a state whose env/resource match
    the (decidably-rejecting) fixture. -/

-- raw invalid PPM (an empty measurement) cannot step:
theorem no_step_empty_ppm (I : MixedInterp Q) (s : ExecState Q)
    (he : s.env = tenvQ) (hr : s.resource = PPMState.init) :
    ¬ ∃ s', Step I [] (.ppm (.meas 0 [])) s s' :=
  no_step_of_not_accepted I [] _ s (by rw [he, hr]; decide)

-- a DISCARDED logical qubit cannot be used by a direct TRANSVERSAL (checked step):
theorem no_step_transversal_discarded (I : MixedInterp Q) (s : ExecState Q)
    (he : s.env = tenvQ) (hr : s.resource = ⟨[], [⟨0, 0⟩]⟩) :
    ¬ ∃ s', Step I [] (.transversal 0 hGate2x2) s s' :=
  no_step_of_not_accepted I [] _ s (by rw [he, hr]; decide)

-- an invalid SWITCH (on a discarded block) cannot step (checked step):
theorem no_step_switch_discarded (I : MixedInterp Q) (s : ExecState Q) (D : Block) (cert : SwitchCert)
    (he : s.env = tenvQ) (hr : s.resource = ⟨[], [⟨0, 0⟩]⟩) :
    ¬ ∃ s', Step I [] (.switch 0 D cert) s s' :=
  -- the dead-block guard rejects BEFORE `D`/`cert` are inspected, so this reduces
  -- definitionally (no `decide` over the free `D`/`cert`).
  no_step_of_not_accepted I [] _ s (by rw [he, hr]; rfl)

end Compiler
