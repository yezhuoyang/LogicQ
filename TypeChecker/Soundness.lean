/-
  TypeChecker.Soundness — MILESTONE 4 + M6/M7: the judgments are SOUND.

  Each theorem extracts, from "the judgment returned `.ok`", the algebraic
  CERTIFICATE that genuinely holds.  M7: judgments run over a TYPED environment
  (`TypedEnv`/`TypedBlock`), so block well-formedness is GUARANTEED by the types —
  the soundness statements no longer restate `Block.valid` guards.  `checkPPM`
  soundness now extracts the MERGED-CODE certificate (not just block validity).
-/
import TypeChecker.Judgment.Transversal
import TypeChecker.Judgment.Switch
import TypeChecker.Judgment.PPM

namespace TypeChecker
open ChainQ ChainQ.GF2

/-- From a surviving `if !c then .error else …` guard hypothesis `¬((!c) = true)`,
    recover `c = true` (surgical, avoids `simp_all` over noisy context). -/
private theorem of_guard_false {c : Bool} (h : ¬ ((!c) = true)) : c = true := by
  cases c
  · exact absurd rfl h
  · rfl

/-- **Completeness extraction.**  A well-formed block exposes EXACTLY the code's
    logical dimension: `k = n − rank(stab)` (rank, so redundant generators are
    fine).  This is the M7 completeness law, read back out of `Block.valid`. -/
theorem Block.valid_complete {b : Block} (h : Block.valid b = true) :
    b.lx.length = b.n - rank b.stab := by
  simp only [Block.valid, Bool.and_eq_true] at h
  exact of_decide_eq_true h.2

/-- **Soundness of `checkLogicalAutomorphism`** (over a typed env).  Acceptance of
    `M` implies `M` preserves the symplectic form AND maps every stabilizer back
    into the code — a genuine code automorphism.  (Block validity is given by
    `TypedEnv`, so it is not restated.) -/
theorem checkLogicalAutomorphism_sound {Γ : TypedEnv} {b : BlockId} {M : BoolMat}
    {e : TypedAutomorphism} {tb : TypedBlock} (hb : Γ.block? b = some tb)
    (h : checkLogicalAutomorphism Γ b M = .ok e) :
    preservesSymp tb.block.n M = true ∧
      (applyMap tb.block.n M tb.block.stab).all (fun r => inSpan tb.block.stab r) = true := by
  simp only [checkLogicalAutomorphism, hb] at h
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  exact ⟨by simp_all, by simp_all⟩

/-- **Soundness of `checkTransversal`** (over a typed env).  Acceptance of the
    local gate `g` implies `g` is a single-qubit symplectic AND its tensor power
    maps every stabilizer back into the code. -/
theorem checkTransversal_sound {Γ : TypedEnv} {b : BlockId} {g : BoolMat}
    {e : TypedTransversal} {tb : TypedBlock} (hb : Γ.block? b = some tb)
    (h : checkTransversal Γ b g = .ok e) :
    preservesSymp 1 g = true ∧
      (applyMap tb.block.n (Internal.transversalMap tb.block.n g) tb.block.stab).all
        (fun r => inSpan tb.block.stab r) = true := by
  simp only [checkTransversal, hb] at h
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  exact ⟨by simp_all, by simp_all⟩

/-- **Soundness of `checkSwitch`** (over a typed env, typed target).  Acceptance
    implies the source was owned & live, and the certifying map `f` preserves the
    stabilizers and the logical basis (mod `S_D`) — a transparent logical coercion.
    Both codes' validity is given by their types, so it is not restated. -/
theorem checkSwitch_sound {Γ : TypedEnv} {b : BlockId} {D : TypedBlock} {cert : SwitchCert}
    {tb : TypedBlock} {ev : TypedEnv × TypedSwitch} (hC : Γ.block? b = some tb)
    (h : checkSwitch Γ b D cert = .ok ev) :
    tb.block.live = true ∧ tb.block.own = Owned.owned ∧
      (applyCross (2 * D.block.n) cert.f tb.block.stab).all (fun r => inSpan D.block.stab r) = true ∧
      rowsEqualModSpan D.block.stab (applyCross (2 * D.block.n) cert.f tb.block.lx) D.block.lx = true ∧
      rowsEqualModSpan D.block.stab (applyCross (2 * D.block.n) cert.f tb.block.lz) D.block.lz = true := by
  simp only [checkSwitch, hC] at h
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  split at h <;> first | contradiction | skip
  exact ⟨by simp_all, by simp_all, by simp_all, by simp_all, by simp_all⟩

/-- **`checkPPM` rejects empty targets** (no identity/no-op measurement form). -/
theorem checkPPM_nonempty {Γ : TypedEnv} {caps : List Capability} {P : PPM.MTarget}
    {r : TypedPPM} (h : checkPPM Γ caps P = .ok r) : P.isEmpty = false := by
  simp only [checkPPM] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hne; simpa using hne

/-- **Merged-code soundness of `checkPPM`** (the cross-code capability branch).
    If a multi-block PPM is accepted via capability `cap`, then the recomputed
    merged stabilizer code (a) pairwise commutes — it is a valid code; (b) contains
    every lifted data stabilizer — it preserves the data codes; and (c) measures
    the target Pauli's representative.  This is the merged-code certificate, not
    merely touched-block validity. -/
theorem checkPPM_merged_sound {Γ : TypedEnv} {caps : List Capability} {P : PPM.MTarget}
    {r : TypedPPM} {bos : List (BlockId × Block × Nat)} {dataN : Nat} {cap : Capability}
    (hg : gather Γ (dedupNat (P.map (fun f => f.1.blk))) = some (bos, dataN))
    (hcap : caps.find? (fun c => decide (c.blocks = dedupNat (P.map (fun f => f.1.blk)))) = some cap)
    (hmulti : ¬ ((dedupNat (P.map (fun f => f.1.blk))).length ≤ 1))
    (h : checkPPM Γ caps P = .ok r) :
    sympOrthogonal (dataN + cap.ancN) (mergedStabOf bos (dataN + cap.ancN) cap.connStab)
        (mergedStabOf bos (dataN + cap.ancN) cap.connStab) = true ∧
      (liftedStabOf bos (dataN + cap.ancN)).all
        (fun row => inSpan (mergedStabOf bos (dataN + cap.ancN) cap.connStab) row) = true ∧
      inSpan (mergedStabOf bos (dataN + cap.ancN) cap.connStab) (targetPOf bos (dataN + cap.ancN) P) = true := by
  simp only [checkPPM, hg, hcap] at h
  -- peel every guard: error branches die (`contradiction`, using `hmulti` for the
  -- native `touched.length ≤ 1` case); only the capability-success branch survives.
  repeat (split at h <;> first | contradiction | skip)
  refine ⟨of_guard_false ?_, of_guard_false ?_, of_guard_false ?_⟩ <;> assumption

end TypeChecker
