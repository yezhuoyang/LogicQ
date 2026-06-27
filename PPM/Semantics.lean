/-
  PPM.Semantics — the small-step operational semantics of QMeas.

  A configuration is `⟨ρ, σ, F, S⟩`:
    * `ρ` — the (logical) quantum state.  Here it is PARAMETRIC: a carrier `Q`
      with a measurement back-action `proj P s : Q → Q` (the normalized
      projection onto the `s`-eigenspace of the logical Pauli product `P`).
      This keeps the control-flow semantics independent of the state model;
      instantiate `Q` with a stabilizer tableau (Clifford fragment,
      Mathlib-free) or a density matrix later.  The frame-correction results
      below hold for ANY `Q`.
    * `σ : CVar → Option Sign` — the classical store of measurement outcomes.
    * `F : LQubit → FPauli` — the Pauli frame: a byproduct operator per LOGICAL
      qubit, which COMPOSES on update (see the remark on the `frame` rule).
    * `S` — the QMeas statement remaining to execute.

  Transitions are labelled by an observation: `tau` (silent classical step) or
  `out s` (a `±1` measurement outcome).  `abort` is a STUCK TERMINAL: no rule
  has it on the left, so post-selected programs partition cleanly into
  accepted (`skip`) and rejected (`abort`) terminal configurations.
-/
import PPM.Syntax

namespace PPM
open Logical

/-! ## §1. The Pauli frame (byproduct group, mod phase). -/

/-- A frame Pauli (the byproduct operator on a logical qubit), incl. identity. -/
inductive FPauli
  | I | X | Y | Z
  deriving DecidableEq, Repr, Inhabited

/-- Pauli multiplication modulo global phase (the frame tracks Paulis up to
    phase).  E.g. `X·Z = Y`. -/
def FPauli.mul : FPauli → FPauli → FPauli
  | .I, b  => b
  | a,  .I => a
  | .X, .X => .I | .Y, .Y => .I | .Z, .Z => .I
  | .X, .Y => .Z | .Y, .X => .Z
  | .Y, .Z => .X | .Z, .Y => .X
  | .X, .Z => .Y | .Z, .X => .Y

/-- A measurement/frame letter as a frame Pauli. -/
def PLetter.toF : PLetter → FPauli
  | .X => .X | .Y => .Y | .Z => .Z

/-- The classical store of measurement outcomes. -/
abbrev Store := CVar → Option Sign
/-- The Pauli frame: a byproduct Pauli per LOGICAL qubit. -/
abbrev Frame := LQubit → FPauli

/-- The empty store (no outcomes bound yet). -/
def Store.empty : Store := fun _ => none
/-- Bind outcome `s` to variable `r`. -/
def Store.set (σ : Store) (r : CVar) (s : Sign) : Store :=
  fun x => if x = r then some s else σ x
/-- The trivial frame (identity on every logical qubit). -/
def Frame.id0 : Frame := fun _ => FPauli.I
/-- Record byproduct `p` on logical qubit `q` by COMPOSING it into the frame. -/
def Frame.mulAt (F : Frame) (q : LQubit) (p : FPauli) : Frame :=
  fun x => if x = q then (F x).mul p else F x

/-! ## §2. Configurations, labels, and the quantum-state interface. -/

/-- The measurement back-action interface: `proj P s ρ` is the normalized
    projection of `ρ` onto the `s`-eigenspace of the logical Pauli product `P`. -/
structure QInterp (Q : Type) where
  proj : MTarget → Sign → Q → Q

/-- A QMeas configuration `⟨ρ, σ, F, S⟩`. -/
structure Config (Q : Type) where
  quantum : Q
  store   : Store
  frame   : Frame
  prog    : Stmt

/-- A small-step observation label. -/
inductive Label
  | tau            -- • silent classical step
  | out (s : Sign) -- ±1 measurement outcome
  deriving DecidableEq, Repr

/-! ## §3. The small-step relation.

    These are exactly the QMeas rules: `meas`, `frame`, `discard`,
    `if-pos`/`if-neg`, `for-zero`/`for-unroll`, `seq-step`/`seq-skip`.
    There is deliberately NO rule for `abort`. -/

variable {Q : Type}

inductive Step (I : QInterp Q) : Config Q → Label → Config Q → Prop where
  /-- (meas) measure logical Pauli `P`, observe `s`, project, bind `r ↦ s`. -/
  | meas {ρ σ F} (r : CVar) (P : MTarget) (s : Sign) :
      Step I ⟨ρ, σ, F, .meas r P⟩ (.out s)
             ⟨I.proj P s ρ, σ.set r s, F, .skip⟩
  /-- (frame) record byproduct `p` on logical qubit `q` (frame composes). -/
  | frame {ρ σ F} (q : LQubit) (p : PLetter) :
      Step I ⟨ρ, σ, F, .frame q p⟩ .tau
             ⟨ρ, σ, F.mulAt q p.toF, .skip⟩
  /-- (discard) retire logical qubit `q`; silent. -/
  | discard {ρ σ F} (q : LQubit) :
      Step I ⟨ρ, σ, F, .discard q⟩ .tau ⟨ρ, σ, F, .skip⟩
  /-- (if-pos) take the then-branch when `σ r = +1`. -/
  | ifPos {ρ σ F s₁ s₂} (r : CVar) (h : σ r = some .pos) :
      Step I ⟨ρ, σ, F, .ite r s₁ s₂⟩ .tau ⟨ρ, σ, F, s₁⟩
  /-- (if-neg) take the else-branch when `σ r = -1`. -/
  | ifNeg {ρ σ F s₁ s₂} (r : CVar) (h : σ r = some .neg) :
      Step I ⟨ρ, σ, F, .ite r s₁ s₂⟩ .tau ⟨ρ, σ, F, s₂⟩
  /-- (for-zero) an exhausted loop is `skip`. -/
  | forZero {ρ σ F b} :
      Step I ⟨ρ, σ, F, .forLoop 0 b⟩ .tau ⟨ρ, σ, F, .skip⟩
  /-- (for-unroll) one iteration peels off the front. -/
  | forUnroll {ρ σ F b} (n : Nat) :
      Step I ⟨ρ, σ, F, .forLoop (n+1) b⟩ .tau ⟨ρ, σ, F, b ;; .forLoop n b⟩
  /-- (seq-skip) drop a leading `skip`. -/
  | seqSkip {ρ σ F S} :
      Step I ⟨ρ, σ, F, .skip ;; S⟩ .tau ⟨ρ, σ, F, S⟩
  /-- (seq-step) reduce inside the head of a sequence. -/
  | seqStep {ρ σ F ρ' σ' F' o S₁ S₁' S₂}
      (h : Step I ⟨ρ, σ, F, S₁⟩ o ⟨ρ', σ', F', S₁'⟩) :
      Step I ⟨ρ, σ, F, S₁ ;; S₂⟩ o ⟨ρ', σ', F', S₁' ;; S₂⟩

/-- The reflexive-transitive closure, indexed by the list of observations. -/
inductive Steps (I : QInterp Q) : Config Q → List Label → Config Q → Prop where
  | refl (c : Config Q) : Steps I c [] c
  | cons {c o c' os c''} (h : Step I c o c') (t : Steps I c' os c'') :
      Steps I c (o :: os) c''

/-- A single step is a one-element reduction. -/
theorem Steps.single {I : QInterp Q} {c o c'} (h : Step I c o c') :
    Steps I c [o] c' := Steps.cons h (Steps.refl _)

/-- Reductions compose (and the observation lists concatenate). -/
theorem Steps.trans {I : QInterp Q} {a b l₁} (h₁ : Steps I a l₁ b) :
    ∀ {c l₂}, Steps I b l₂ c → Steps I a (l₁ ++ l₂) c := by
  induction h₁ with
  | refl => intro c l₂ h₂; simpa using h₂
  | cons hstep _ ih => intro c l₂ h₂; exact Steps.cons hstep (ih h₂)

/-! ## §4. `abort` is a stuck terminal; accepted vs. rejected runs. -/

/-- No rule fires on `abort`: it cannot take a step. -/
theorem abort_stuck (I : QInterp Q) {ρ σ F} :
    ¬ ∃ o c', Step I ⟨ρ, σ, F, .abort⟩ o c' := by
  rintro ⟨o, c', h⟩; cases h

/-- A run from `c₀` is **accepted** if it reaches a `skip` terminal. -/
def Accepted (I : QInterp Q) (c₀ : Config Q) : Prop :=
  ∃ ℓ c', Steps I c₀ ℓ c' ∧ c'.prog = .skip

/-- A run from `c₀` is **rejected** if it reaches an `abort` terminal. -/
def Rejected (I : QInterp Q) (c₀ : Config Q) : Prop :=
  ∃ ℓ c', Steps I c₀ ℓ c' ∧ c'.prog = .abort

/-! ## §5. Derived head-of-sequence reductions (the paper's combinators). -/

/-- (meas) in head position: `r := M_P; S` reduces to `S` in two steps,
    binding `r ↦ s` and projecting the state.  This is the paper's
    head-form measurement rule, derived from `meas` + `seqStep` + `seqSkip`. -/
theorem red_meas (I : QInterp Q) {ρ : Q} {σ F} (r : CVar) (P : MTarget)
    (s : Sign) (S : Stmt) :
    Steps I ⟨ρ, σ, F, .meas r P ;; S⟩ [.out s, .tau]
           ⟨I.proj P s ρ, σ.set r s, F, S⟩ :=
  Steps.cons (Step.seqStep (Step.meas r P s)) (Steps.single Step.seqSkip)

/-- (if-pos) on a `then = skip` guard in head position: two silent steps. -/
theorem red_ite_pos (I : QInterp Q) {ρ : Q} {σ F} (r : CVar) (s₂ S : Stmt)
    (h : σ r = some .pos) :
    Steps I ⟨ρ, σ, F, .ite r .skip s₂ ;; S⟩ [.tau, .tau] ⟨ρ, σ, F, S⟩ :=
  Steps.cons (Step.seqStep (Step.ifPos r h)) (Steps.single Step.seqSkip)

/-- (if-neg) into a `frame` byproduct in head position: three silent steps,
    composing `p` into the frame at logical qubit `q`. -/
theorem red_ite_neg_frame (I : QInterp Q) {ρ : Q} {σ F} (r : CVar) (q : LQubit)
    (p : PLetter) (S : Stmt) (h : σ r = some .neg) :
    Steps I ⟨ρ, σ, F, .ite r .skip (.frame q p) ;; S⟩ [.tau, .tau, .tau]
           ⟨ρ, σ, F.mulAt q p.toF, S⟩ :=
  Steps.cons (Step.seqStep (Step.ifNeg r h))
    (Steps.cons (Step.seqStep (Step.frame q p)) (Steps.single Step.seqSkip))

/-- (if-pos) into an ARBITRARY then-branch `s₁` in head position (no `skip`
    constraint): ONE silent step `.ite r s₁ s₂ ;; S → s₁ ;; S`.  Needed for the
    NESTED conditionals in `progSAt`/`progCNOTAt` (whose then-branch is itself an
    `ite`, so `red_ite_pos` — which requires `then = skip` — does not apply). -/
theorem red_ite_pos_into (I : QInterp Q) {ρ : Q} {σ F} (r : CVar) (s₁ s₂ S : Stmt)
    (h : σ r = some .pos) :
    Steps I ⟨ρ, σ, F, .ite r s₁ s₂ ;; S⟩ [.tau] ⟨ρ, σ, F, s₁ ;; S⟩ :=
  Steps.single (Step.seqStep (Step.ifPos r h))

/-- (if-neg) into an ARBITRARY else-branch `s₂` in head position: ONE silent step
    `.ite r s₁ s₂ ;; S → s₂ ;; S`. -/
theorem red_ite_neg_into (I : QInterp Q) {ρ : Q} {σ F} (r : CVar) (s₁ s₂ S : Stmt)
    (h : σ r = some .neg) :
    Steps I ⟨ρ, σ, F, .ite r s₁ s₂ ;; S⟩ [.tau] ⟨ρ, σ, F, s₂ ;; S⟩ :=
  Steps.single (Step.seqStep (Step.ifNeg r h))

/-! ## §6. Worked example: the Hadamard gadget frame table.

    For each outcome pair `(r₁, r₂)`, the H gadget reduces to a terminal
    `skip` configuration whose Pauli frame on the ANCILLA logical qubit
    `a = ⟨1,0⟩` is the expected byproduct.  This reproduces the paper's H
    correction table `(+,+)→I, (+,-)→X, (-,+)→Z, (-,-)→Y` — DERIVED from the
    small-step rules.  The frame is determined entirely by the classical store
    + control flow, so the result is independent of the quantum back-end `Q`. -/

/-- The H-gadget byproduct table. -/
def hByp : Sign → Sign → FPauli
  | .pos, .pos => .I
  | .pos, .neg => .X
  | .neg, .pos => .Z
  | .neg, .neg => .Y

/-- **H-gadget correctness (frame level), all four branches.**  For every
    outcome pair `(s₁, s₂)`, `progH` reduces (under the outcomes `s₁, s₂`) to a
    `skip` terminal whose frame on the ancilla logical qubit `a = ⟨1,0⟩` equals
    `hByp s₁ s₂`. -/
theorem progH_frame (I : QInterp Q) (ρ : Q) (s₁ s₂ : Sign) :
    ∃ ℓ ρ' σ' F',
      Steps I ⟨ρ, Store.empty, Frame.id0, progH⟩ ℓ ⟨ρ', σ', F', .skip⟩ ∧
      F' (ancQ 0) = hByp s₁ s₂ := by
  -- One explicit reduction per outcome branch: thread the two measurements
  -- with the branch outcomes, fire the matching conditional rule for each
  -- `ite` (`if-pos` → no frame change; `if-neg` → compose the byproduct on the
  -- ancilla), and finish with `discard` of the data qubit.
  cases s₁ <;> cases s₂
  · exact ⟨_, _, _, _,
      (red_meas I 0 _ .pos _).trans <| (red_meas I 1 _ .pos _).trans <|
      (red_ite_pos I 0 _ _ (by simp [Store.set])).trans <|
      (red_ite_pos I 1 _ _ (by simp [Store.set])).trans <|
      Steps.single (Step.discard (dataQ 0)),
      by simp [Frame.id0, hByp]⟩
  · exact ⟨_, _, _, _,
      (red_meas I 0 _ .pos _).trans <| (red_meas I 1 _ .neg _).trans <|
      (red_ite_pos I 0 _ _ (by simp [Store.set])).trans <|
      (red_ite_neg_frame I 1 (ancQ 0) .X _ (by simp [Store.set])).trans <|
      Steps.single (Step.discard (dataQ 0)),
      by simp [Frame.id0, Frame.mulAt, FPauli.mul, PLetter.toF, hByp]⟩
  · exact ⟨_, _, _, _,
      (red_meas I 0 _ .neg _).trans <| (red_meas I 1 _ .pos _).trans <|
      (red_ite_neg_frame I 0 (ancQ 0) .Z _ (by simp [Store.set])).trans <|
      (red_ite_pos I 1 _ _ (by simp [Store.set])).trans <|
      Steps.single (Step.discard (dataQ 0)),
      by simp [Frame.id0, Frame.mulAt, FPauli.mul, PLetter.toF, hByp]⟩
  · exact ⟨_, _, _, _,
      (red_meas I 0 _ .neg _).trans <| (red_meas I 1 _ .neg _).trans <|
      (red_ite_neg_frame I 0 (ancQ 0) .Z _ (by simp [Store.set])).trans <|
      (red_ite_neg_frame I 1 (ancQ 0) .X _ (by simp [Store.set])).trans <|
      Steps.single (Step.discard (dataQ 0)),
      by simp [Frame.id0, Frame.mulAt, FPauli.mul, PLetter.toF, hByp]⟩

/-- The post-selection check accepts on a `+1` outcome (reaches `skip`). -/
theorem checkPlus_accepts (I : QInterp Q) (ρ : Q) (σ : Store) (F : Frame)
    (r : CVar) (P : MTarget) :
    Accepted I ⟨ρ, σ, F, checkPlus r P⟩ :=
  ⟨_, _, (red_meas I r P .pos _).trans
           (Steps.single (Step.ifPos r (by simp [Store.set]))), rfl⟩

/-- The post-selection check rejects on a `-1` outcome (reaches `abort`). -/
theorem checkPlus_rejects (I : QInterp Q) (ρ : Q) (σ : Store) (F : Frame)
    (r : CVar) (P : MTarget) :
    Rejected I ⟨ρ, σ, F, checkPlus r P⟩ :=
  ⟨_, _, (red_meas I r P .neg _).trans
           (Steps.single (Step.ifNeg r (by simp [Store.set]))), rfl⟩

end PPM
