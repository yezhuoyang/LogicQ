/-
  TypeChecker.Judgment.PPMProgram.Soundness — the ∀ soundness theorems for the
  PPM program checker.
-/
import TypeChecker.Judgment.PPMProgram.Check

namespace TypeChecker
open ChainQ.GF2 Logical PPM

/-! ## Soundness theorems (∀, separate from the `decide` examples). -/

/-- **All emitted measurements are legal.**  A type-checked statement's every
    measurement target passes `checkPPM`. -/
theorem checkPPMStmt_meas_sound (Γ : TypedEnv) (caps : List Capability) :
    ∀ (s : Stmt) (st st' : PPMState),
      checkPPMStmt Γ caps st s = .ok st' →
      (measTargets s).all (fun P => ok? (checkPPM Γ caps P)) = true := by
  intro s
  induction s with
  | meas r P =>
    intro st st' h
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · next hP => simp only [measTargets, List.all_cons, List.all_nil, Bool.and_true, hP, ok?]
      · exact absurd h (by simp)
  | frame q p => intro _ _ _; rfl
  | discard q => intro _ _ _; rfl
  | skip => intro _ _ _; rfl
  | abort => intro _ _ _; rfl
  | ite r s₁ s₂ ih₁ ih₂ =>
    intro st st' h
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · next st₁ h₁ =>
        split at h
        · exact absurd h (by simp)
        · next st₂ h₂ =>
          simp only [measTargets, List.all_append, Bool.and_eq_true]
          exact ⟨ih₁ _ _ h₁, ih₂ _ _ h₂⟩
  | forLoop n body ih =>
    intro st st' h
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · next st₁ hb =>
      split at h
      · simpa only [measTargets] using ih _ _ hb
      · exact absurd h (by simp)
  | seq s₁ s₂ ih₁ ih₂ =>
    intro st st' h
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · next st₁ h₁ =>
      simp only [measTargets, List.all_append, Bool.and_eq_true]
      exact ⟨ih₁ _ _ h₁, ih₂ _ _ h⟩

/-- **All frame/discard targets are valid.**  A type-checked statement's every
    `frame`/`discard` target passes `validLQubit`. -/
theorem checkPPMStmt_targets_valid (Γ : TypedEnv) (caps : List Capability) :
    ∀ (s : Stmt) (st st' : PPMState),
      checkPPMStmt Γ caps st s = .ok st' →
      (frameDiscardTargets s).all (validLQubit Γ) = true := by
  intro s
  induction s with
  | meas r P => intro _ _ _; rfl
  | frame q p =>
    intro st st' h
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · next hq => simpa only [frameDiscardTargets, List.all_cons, List.all_nil, Bool.and_true] using hq
      · exact absurd h (by simp)
  | discard q =>
    intro st st' h
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · next hq => simpa only [frameDiscardTargets, List.all_cons, List.all_nil, Bool.and_true] using hq
      · exact absurd h (by simp)
  | skip => intro _ _ _; rfl
  | abort => intro _ _ _; rfl
  | ite r s₁ s₂ ih₁ ih₂ =>
    intro st st' h
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · next st₁ h₁ =>
        split at h
        · exact absurd h (by simp)
        · next st₂ h₂ =>
          simp only [frameDiscardTargets, List.all_append, Bool.and_eq_true]
          exact ⟨ih₁ _ _ h₁, ih₂ _ _ h₂⟩
  | forLoop n body ih =>
    intro st st' h
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · next st₁ hb =>
      split at h
      · simpa only [frameDiscardTargets] using ih _ _ hb
      · exact absurd h (by simp)
  | seq s₁ s₂ ih₁ ih₂ =>
    intro st st' h
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · next st₁ h₁ =>
      simp only [frameDiscardTargets, List.all_append, Bool.and_eq_true]
      exact ⟨ih₁ _ _ h₁, ih₂ _ _ h⟩

/-- **Discards only accumulate** (the dead set is monotone along execution). -/
theorem checkPPMStmt_dead_mono (Γ : TypedEnv) (caps : List Capability) (q : LQubit) :
    ∀ (s : Stmt) (st st' : PPMState),
      checkPPMStmt Γ caps st s = .ok st' →
      st.dead.contains q = true → st'.dead.contains q = true := by
  intro s
  induction s with
  | meas r P =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · next hP => cases h; exact hq
      · exact absurd h (by simp)
  | frame q' p =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · cases h; exact hq
      · exact absurd h (by simp)
  | discard q' =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · cases h; exact DeadSet.contains_insert_of_contains hq
      · exact absurd h (by simp)
  | skip => intro st st' h hq; cases h; exact hq
  | abort => intro st st' h hq; cases h; exact hq
  | ite r s₁ s₂ ih₁ ih₂ =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · next st₁ h₁ =>
        split at h
        · exact absurd h (by simp)
        · next st₂ h₂ =>
          cases h
          exact DeadSet.contains_union_left (ih₁ _ _ h₁ hq)
  | forLoop n body ih =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · next st₁ hb =>
      split at h
      · next => cases h; exact ih _ _ hb hq
      · exact absurd h (by simp)
  | seq s₁ s₂ ih₁ ih₂ =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · next st₁ h₁ => exact ih₂ _ _ h (ih₁ _ _ h₁ hq)

/-- **No use-after-discard.**  If a statement type-checks from a state in which
    `q` is already discarded, the statement never references `q` (it does not
    measure, frame, or discard `q`).  Together with `checkPPMProgram` starting
    from the empty state, this means a well-typed program never uses a logical
    qubit after discarding it. -/
theorem checkPPMStmt_no_use_after_discard (Γ : TypedEnv) (caps : List Capability) (q : LQubit) :
    ∀ (s : Stmt) (st st' : PPMState),
      checkPPMStmt Γ caps st s = .ok st' →
      st.dead.contains q = true → touches s q = false := by
  intro s
  induction s with
  | meas r P =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · next hfind =>
      simp only [touches]
      exact Bool.eq_false_iff.mpr (fun hc => (List.find?_eq_none.mp hfind q (List.contains_iff_mem.mp hc)) hq)
  | frame q' p =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · next hd =>
      split at h
      · simp only [touches]
        exact Bool.eq_false_iff.mpr (fun hc => absurd hq (of_decide_eq_true hc ▸ hd))
      · exact absurd h (by simp)
  | discard q' =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · next hd =>
      split at h
      · simp only [touches]
        exact Bool.eq_false_iff.mpr (fun hc => absurd hq (of_decide_eq_true hc ▸ hd))
      · exact absurd h (by simp)
  | skip => intro _ _ _ _; rfl
  | abort => intro _ _ _ _; rfl
  | ite r s₁ s₂ ih₁ ih₂ =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · next st₁ h₁ =>
        split at h
        · exact absurd h (by simp)
        · next st₂ h₂ =>
          simp only [touches, Bool.or_eq_false_iff]
          exact ⟨ih₁ _ _ h₁ hq, ih₂ _ _ h₂ hq⟩
  | forLoop n body ih =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · next st₁ hb =>
      split at h
      · next => simp only [touches]; exact ih _ _ hb hq
      · exact absurd h (by simp)
  | seq s₁ s₂ ih₁ ih₂ =>
    intro st st' h hq
    simp only [checkPPMStmt] at h
    split at h
    · exact absurd h (by simp)
    · next st₁ h₁ =>
      simp only [touches, Bool.or_eq_false_iff]
      exact ⟨ih₁ _ _ h₁ hq, ih₂ _ _ h (checkPPMStmt_dead_mono Γ caps q s₁ st st₁ h₁ hq)⟩

end TypeChecker
