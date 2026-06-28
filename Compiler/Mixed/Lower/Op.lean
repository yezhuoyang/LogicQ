/-
  Compiler.Mixed.Lower.Op — the resource-aware per-op selector `compileOpR` and
  its soundness / completeness theorems (split out of Compiler/Mixed/Lower.lean).
-/
import Compiler.Mixed.Check
import Compiler.Mixed.Source

namespace Compiler
open TypeChecker PPM ChainQ.GF2 Logical

/-! ## §2. Resource-aware compilation  `Γ; R ⊢ op ⇝ instr ⊣ Γ'; R'`.

    `compileOpR` lowers an op through `checkInstr` (which consults the resource
    state `R`), so the emitted instruction is type-checked BY CONSTRUCTION.  The
    compilation relation is its success: `Γ; R ⊢ op ⇝ instr ⊣ Γ'; R'  :=
    compileOpR … op = .ok (instr, Γ', R')`. -/
def compileOpR (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) :
    LogicalOp → Except TypeError (MixedInstr × TypedEnv × PPMState)
  | .measure r P =>
      match checkInstr caps Γ R (.ppm (.meas r P)) with
      | .ok (Γ', R') => .ok (.ppm (.meas r P), Γ', R')
      | .error e     => .error e
  | .hGate q =>
      -- DIRECT transversal only on a SINGLE-LOGICAL block (k=1), where it coincides
      -- with the single-qubit gate; otherwise the qubit-level PPM gadget.
      if singleLogicalBlock Γ q.blk then
        match checkInstr caps Γ R (.transversal q.blk hGate2x2) with
        | .ok (Γ', R') => .ok (.transversal q.blk hGate2x2, Γ', R')
        | .error _ =>
          match checkInstr caps Γ R (.ppm (progHAt q anc r₁ r₂)) with  -- PPM gadget fallback
          | .ok (Γ', R') => .ok (.ppm (progHAt q anc r₁ r₂), Γ', R')
          | .error _     => .error (.notImplemented "H: no legal transversal and no PPM gadget")
      else
        match checkInstr caps Γ R (.ppm (progHAt q anc r₁ r₂)) with    -- multi-logical: PPM gadget only
        | .ok (Γ', R') => .ok (.ppm (progHAt q anc r₁ r₂), Γ', R')
        | .error _     => .error (.notImplemented "H: multi-logical block — needs a PPM gadget (no block-wide transversal)")
  | .sGate q =>
      if singleLogicalBlock Γ q.blk then
        match checkInstr caps Γ R (.transversal q.blk sGate2x2) with
        | .ok (Γ', R') => .ok (.transversal q.blk sGate2x2, Γ', R')
        | .error _ =>
          match checkInstr caps Γ R (.ppm (progSAt q anc r₁ r₂)) with
          | .ok (Γ', R') => .ok (.ppm (progSAt q anc r₁ r₂), Γ', R')
          | .error _     => .error (.notImplemented "S: no legal transversal and no PPM gadget")
      else
        match checkInstr caps Γ R (.ppm (progSAt q anc r₁ r₂)) with
        | .ok (Γ', R') => .ok (.ppm (progSAt q anc r₁ r₂), Γ', R')
        | .error _     => .error (.notImplemented "S: multi-logical block — needs a PPM gadget (no block-wide transversal)")
  | .cnotGate c t =>
      match checkInstr caps Γ R (.ppm (progCNOTAt c t anc r₁ r₂ r₃)) with
      | .ok (Γ', R') => .ok (.ppm (progCNOTAt c t anc r₁ r₂ r₃), Γ', R')
      | .error _     => .error (.notImplemented "CNOT: no PPM gadget (transversal CNOT deferred)")
  | .transversalLogicalCNOT c t incidence =>
      let spec : TransversalCNOTSpec := { control := c, target := t, incidence := incidence }
      match checkInstr caps Γ R (.transversalCNOT spec) with
      | .ok (Γ', R') => .ok (.transversalCNOT spec, Γ', R')
      | .error e     => .error e
  | .transversalLogicalCNOTBatch controlBlock targetBlock incidence logicalIncidence =>
      let spec : TransversalCNOTBatchSpec :=
        { controlBlock := controlBlock, targetBlock := targetBlock,
          incidence := incidence, logicalIncidence := logicalIncidence }
      match checkInstr caps Γ R (.transversalCNOTBatch spec) with
      | .ok (Γ', R') => .ok (.transversalCNOTBatch spec, Γ', R')
      | .error e     => .error e
  | .tGate q =>
      -- T (π/8) lowers to a DEFERRED, TYPED magic obligation carrying its target `q`:
      -- the checker accepts `.magic` (well-typed MODULO magic) but it has NO Step
      -- semantics (MagicQ unwired).  A `ProgramOk`-accepted `T` (allowMagic) lowers
      -- rather than failing — but the EXECUTABLE path (`compile? .executable`) still rejects it.
      .ok (.magic { kind := .tGate, target := q }, Γ, R)
  | .blockTransversal b g =>
      -- a BLOCK-LEVEL direct transversal: emit it directly (honestly block-wide).
      match checkInstr caps Γ R (.transversal b g) with
      | .ok (Γ', R') => .ok (.transversal b g, Γ', R')
      | .error e     => .error e
  | .xGate q =>
      -- M18: a logical Pauli lowers to a REAL `.pauli` instruction that is APPLIED to
      -- the carrier under `Step` (not a record-only PPM `.frame`), so its operational
      -- semantics matches the ideal source action.
      match checkInstr caps Γ R (.pauli q .X) with
      | .ok (Γ', R') => .ok (.pauli q .X, Γ', R')
      | .error e     => .error e
  | .zGate q =>
      match checkInstr caps Γ R (.pauli q .Z) with
      | .ok (Γ', R') => .ok (.pauli q .Z, Γ', R')
      | .error e     => .error e
  | .czGate c t =>
      -- CZ is a 2-qubit Clifford: lowers to the (ideal-assumed) CZ PPM gadget.
      match checkInstr caps Γ R (.ppm (progCZAt c t anc r₁ r₂ r₃)) with
      | .ok (Γ', R') => .ok (.ppm (progCZAt c t anc r₁ r₂ r₃), Γ', R')
      | .error _     => .error (.notImplemented "CZ: no PPM gadget (transversal CZ deferred)")

/-- **`compileOp_sound`.**  Whatever instruction `compileOpR` emits TYPE-CHECKS
    under the same environment and resource state — the compilation relation is
    sound w.r.t. the mixed checker. -/
theorem compileOp_sound (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) (op : LogicalOp)
    {instr : MixedInstr} {Γ' : TypedEnv} {R' : PPMState}
    (h : compileOpR caps Γ R anc r₁ r₂ r₃ op = .ok (instr, Γ', R')) :
    checkInstr caps Γ R instr = .ok (Γ', R') := by
  unfold compileOpR at h
  cases op with
  | measure r P =>
    cases hc : checkInstr caps Γ R (.ppm (.meas r P)) with
    | error e => simp [hc] at h
    | ok p =>
      obtain ⟨Γ₀, R₀⟩ := p
      simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; exact hc
  | hGate q =>
    cases hsb : singleLogicalBlock Γ q.blk with
    | true =>
      simp only [hsb] at h
      cases hc : checkInstr caps Γ R (.transversal q.blk hGate2x2) with
      | ok p =>
        obtain ⟨Γ₀, R₀⟩ := p
        simp only [hc] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; exact hc
      | error e =>
        cases hc2 : checkInstr caps Γ R (.ppm (progHAt q anc r₁ r₂)) with
        | ok p =>
          obtain ⟨Γ₀, R₀⟩ := p
          simp only [hc, hc2] at h
          obtain ⟨rfl, rfl, rfl⟩ := h; exact hc2
        | error e2 => simp [hc, hc2] at h
    | false =>
      simp only [hsb] at h
      cases hc2 : checkInstr caps Γ R (.ppm (progHAt q anc r₁ r₂)) with
      | ok p =>
        obtain ⟨Γ₀, R₀⟩ := p
        simp only [hc2] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; exact hc2
      | error e2 => simp [hc2] at h
  | sGate q =>
    cases hsb : singleLogicalBlock Γ q.blk with
    | true =>
      simp only [hsb] at h
      cases hc : checkInstr caps Γ R (.transversal q.blk sGate2x2) with
      | ok p =>
        obtain ⟨Γ₀, R₀⟩ := p
        simp only [hc] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; exact hc
      | error e =>
        cases hc2 : checkInstr caps Γ R (.ppm (progSAt q anc r₁ r₂)) with
        | ok p =>
          obtain ⟨Γ₀, R₀⟩ := p
          simp only [hc, hc2] at h
          obtain ⟨rfl, rfl, rfl⟩ := h; exact hc2
        | error e2 => simp [hc, hc2] at h
    | false =>
      simp only [hsb] at h
      cases hc2 : checkInstr caps Γ R (.ppm (progSAt q anc r₁ r₂)) with
      | ok p =>
        obtain ⟨Γ₀, R₀⟩ := p
        simp only [hc2] at h
        obtain ⟨rfl, rfl, rfl⟩ := h; exact hc2
      | error e2 => simp [hc2] at h
  | cnotGate c t =>
    cases hc : checkInstr caps Γ R (.ppm (progCNOTAt c t anc r₁ r₂ r₃)) with
    | ok p =>
      obtain ⟨Γ₀, R₀⟩ := p
      simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; exact hc
    | error e => simp [hc] at h
  | transversalLogicalCNOT c t incidence =>
    cases hc : checkInstr caps Γ R (.transversalCNOT { control := c, target := t, incidence := incidence }) with
    | ok p =>
      obtain ⟨Γ₀, R₀⟩ := p
      simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; exact hc
    | error e => simp [hc] at h
  | transversalLogicalCNOTBatch controlBlock targetBlock incidence logicalIncidence =>
    cases hc : checkInstr caps Γ R
        (.transversalCNOTBatch
          { controlBlock := controlBlock, targetBlock := targetBlock,
            incidence := incidence, logicalIncidence := logicalIncidence }) with
    | ok p =>
      obtain ⟨Γ₀, R₀⟩ := p
      simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; exact hc
    | error e => simp [hc] at h
  | tGate q =>
    -- T emits a `.magic` obligation, which `checkInstr` accepts as a typed deferred
    -- obligation; so the emitted instruction type-checks (with `Γ`, `R` unchanged).
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h; rfl
  | blockTransversal b g =>
    cases hc : checkInstr caps Γ R (.transversal b g) with
    | ok p =>
      obtain ⟨Γ₀, R₀⟩ := p
      simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; exact hc
    | error e => simp [hc] at h
  | xGate q =>
    cases hc : checkInstr caps Γ R (.pauli q .X) with
    | ok p =>
      obtain ⟨Γ₀, R₀⟩ := p
      simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; exact hc
    | error e => simp [hc] at h
  | zGate q =>
    cases hc : checkInstr caps Γ R (.pauli q .Z) with
    | ok p =>
      obtain ⟨Γ₀, R₀⟩ := p
      simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; exact hc
    | error e => simp [hc] at h
  | czGate c t =>
    cases hc : checkInstr caps Γ R (.ppm (progCZAt c t anc r₁ r₂ r₃)) with
    | ok p =>
      obtain ⟨Γ₀, R₀⟩ := p
      simp only [hc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h; exact hc
    | error e => simp [hc] at h

/-- **`compileOp_complete` (measurement fragment).**  If a logical measurement is
    accepted by the mixed checker, `compileOpR` lowers it (to the native PPM
    measurement). -/
theorem compileOp_complete_measure (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) (r : CVar) (P : MTarget) {Γ' : TypedEnv} {R' : PPMState}
    (h : checkInstr caps Γ R (.ppm (.meas r P)) = .ok (Γ', R')) :
    compileOpR caps Γ R anc r₁ r₂ r₃ (.measure r P) = .ok (.ppm (.meas r P), Γ', R') := by
  simp only [compileOpR, h]

/-- **`compileOp_complete` (direct-transversal fragment).**  If transversal `H` is
    legal, `compileOpR` emits it DIRECTLY (never the PPM gadget). -/
theorem compileOp_complete_hGate (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) (q : LQubit) {Γ' : TypedEnv} {R' : PPMState}
    (hsingle : singleLogicalBlock Γ q.blk = true)   -- direct transversal only on a k=1 block
    (h : checkInstr caps Γ R (.transversal q.blk hGate2x2) = .ok (Γ', R')) :
    compileOpR caps Γ R anc r₁ r₂ r₃ (.hGate q) = .ok (.transversal q.blk hGate2x2, Γ', R') := by
  simp [compileOpR, hsingle, h]

/-- **Progress (source typing drives compilation).**  The source-typing judgment
    is LOAD-BEARING: if `Γ; R ⊢ H q ok` and a transversal `H` is legal on `q`'s
    code, then `H q` COMPILES to a direct transversal — `srcOpOk`'s resource
    component is exactly what discharges the checker's dead-block guard. -/
theorem srcOpOk_hGate_compiles (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) (q : LQubit) {e : TypedTransversal}
    (hsingle : singleLogicalBlock Γ q.blk = true)
    (hsrc : srcOpOk Γ R (.hGate q) = true)
    (htrans : checkTransversal Γ q.blk hGate2x2 = .ok e) :
    compileOpR caps Γ R anc r₁ r₂ r₃ (.hGate q) = .ok (.transversal q.blk hGate2x2, Γ, R) := by
  have hblk : R.dead.hasBlock q.blk = false := by
    simp only [srcOpOk, Bool.and_eq_true, Bool.not_eq_true'] at hsrc; exact hsrc.2
  have hfind : R.dead.find? (fun x => x.blk == q.blk) = none :=
    DeadSet.find?_eq_none_of_not_hasBlock hblk
  have hchk : checkInstr caps Γ R (.transversal q.blk hGate2x2) = .ok (Γ, R) := by
    simp only [checkInstr, hfind, htrans]
  exact compileOp_complete_hGate caps Γ R anc r₁ r₂ r₃ q hsingle hchk

/-! ### Direct-fragment SEMANTIC correctness for the resource-aware path.

    These migrate the M9 `compileOp_*_transversal_sound` results onto the PUBLIC
    `compileOpR` selector: when a logical `H`/`S` is emitted as a TRANSVERSAL, the
    target instruction's symplectic action EQUALS the source gate's intended action
    (the gate is realized directly, never erased into a measurement gadget). -/

theorem compileOpR_hGate_action_sound
    (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) (q : LQubit)
    {b : Nat} {g : BoolMat} {Γ' : TypedEnv} {R' : PPMState}
    (h : compileOpR caps Γ R anc r₁ r₂ r₃ (.hGate q) = .ok (.transversal b g, Γ', R')) :
    MixedInstr.action Γ (.transversal b g) = (LogicalOp.hGate q).srcAction Γ := by
  unfold compileOpR at h
  cases hsb : singleLogicalBlock Γ q.blk with
  | true =>
    simp only [hsb] at h
    cases hc : checkInstr caps Γ R (.transversal q.blk hGate2x2) with
    | ok p =>
      obtain ⟨Γ₀, R₀⟩ := p
      simp only [hc] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      simp [LogicalOp.srcAction, MixedInstr.action, hsb]
    | error e =>
      cases hc2 : checkInstr caps Γ R (.ppm (progHAt q anc r₁ r₂)) with
      | ok p => obtain ⟨Γ₀, R₀⟩ := p; simp [hc, hc2] at h
      | error e2 => simp [hc, hc2] at h
  | false =>
    simp only [hsb] at h
    cases hc2 : checkInstr caps Γ R (.ppm (progHAt q anc r₁ r₂)) with
    | ok p => obtain ⟨Γ₀, R₀⟩ := p; simp [hc2] at h
    | error e2 => simp [hc2] at h

theorem compileOpR_sGate_action_sound
    (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) (q : LQubit)
    {b : Nat} {g : BoolMat} {Γ' : TypedEnv} {R' : PPMState}
    (h : compileOpR caps Γ R anc r₁ r₂ r₃ (.sGate q) = .ok (.transversal b g, Γ', R')) :
    MixedInstr.action Γ (.transversal b g) = (LogicalOp.sGate q).srcAction Γ := by
  unfold compileOpR at h
  cases hsb : singleLogicalBlock Γ q.blk with
  | true =>
    simp only [hsb] at h
    cases hc : checkInstr caps Γ R (.transversal q.blk sGate2x2) with
    | ok p =>
      obtain ⟨Γ₀, R₀⟩ := p
      simp only [hc] at h; obtain ⟨rfl, rfl, rfl⟩ := h
      simp [LogicalOp.srcAction, MixedInstr.action, hsb]
    | error e =>
      cases hc2 : checkInstr caps Γ R (.ppm (progSAt q anc r₁ r₂)) with
      | ok p => obtain ⟨Γ₀, R₀⟩ := p; simp [hc, hc2] at h
      | error e2 => simp [hc, hc2] at h
  | false =>
    simp only [hsb] at h
    cases hc2 : checkInstr caps Γ R (.ppm (progSAt q anc r₁ r₂)) with
    | ok p => obtain ⟨Γ₀, R₀⟩ := p; simp [hc2] at h
    | error e2 => simp [hc2] at h

/-! ## §3·5. Source PROGRAM typing  `ProgramOk`  +  supported completeness.

    `ProgramOk Γ caps res ops` is the real source-program typing judgment.  The
    SUPPORTED fragment (transversal-legal `H`/`S`) is shown COMPLETE: it always
    compiles (`ProgramOkSupported_compiles`). -/

/-- The direct-`S` completeness lemma (analogue of `compileOp_complete_hGate`). -/
theorem compileOp_complete_sGate (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) (q : LQubit) {Γ' : TypedEnv} {R' : PPMState}
    (hsingle : singleLogicalBlock Γ q.blk = true)
    (h : checkInstr caps Γ R (.transversal q.blk sGate2x2) = .ok (Γ', R')) :
    compileOpR caps Γ R anc r₁ r₂ r₃ (.sGate q) = .ok (.transversal q.blk sGate2x2, Γ', R') := by
  simp [compileOpR, hsingle, h]

/-- Progress for `S` (analogue of `srcOpOk_hGate_compiles`). -/
theorem srcOpOk_sGate_compiles (caps : List Capability) (Γ : TypedEnv) (R : PPMState)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) (q : LQubit) {e : TypedTransversal}
    (hsingle : singleLogicalBlock Γ q.blk = true)
    (hsrc : srcOpOk Γ R (.sGate q) = true)
    (htrans : checkTransversal Γ q.blk sGate2x2 = .ok e) :
    compileOpR caps Γ R anc r₁ r₂ r₃ (.sGate q) = .ok (.transversal q.blk sGate2x2, Γ, R) := by
  have hblk : R.dead.hasBlock q.blk = false := by
    simp only [srcOpOk, Bool.and_eq_true, Bool.not_eq_true'] at hsrc; exact hsrc.2
  have hfind : R.dead.find? (fun x => x.blk == q.blk) = none :=
    DeadSet.find?_eq_none_of_not_hasBlock hblk
  have hchk : checkInstr caps Γ R (.transversal q.blk sGate2x2) = .ok (Γ, R) := by
    simp only [checkInstr, hfind, htrans]
  exact compileOp_complete_sGate caps Γ R anc r₁ r₂ r₃ q hsingle hchk

end Compiler
