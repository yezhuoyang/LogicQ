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

/-- **Soundness of `checkTransversalCNOT`**.  Acceptance of an incidence-certified
    logical CNOT implies physical transversality, stabilizer preservation on the
    product code, and the requested logical X/Z action modulo the product
    stabilizer. -/
theorem checkTransversalCNOT_sound {Γ : TypedEnv} {spec : TransversalCNOTSpec}
    {e : TypedTransversalCNOT} {cTB tTB : TypedBlock}
    (hc : Γ.block? spec.control.blk = some cTB)
    (ht : Γ.block? spec.target.blk = some tTB)
    (h : checkTransversalCNOT Γ spec = .ok e) :
    Internal.physicallyTransversalIncidence cTB.block.n tTB.block.n spec.incidence = true ∧
      (applyMap (cTB.block.n + tTB.block.n)
        (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence)
        (Internal.jointStab cTB.block tTB.block)).all
        (fun r => inSpan (Internal.jointStab cTB.block tTB.block) r) = true ∧
      Internal.rowsEqualModStab (Internal.jointStab cTB.block tTB.block)
        (applyMap (cTB.block.n + tTB.block.n)
          (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence)
          (Internal.jointLX cTB.block tTB.block))
        (Internal.expectedCNOTLX cTB.block tTB.block spec.control.idx spec.target.idx) = true ∧
      Internal.rowsEqualModStab (Internal.jointStab cTB.block tTB.block)
        (applyMap (cTB.block.n + tTB.block.n)
          (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence)
          (Internal.jointLZ cTB.block tTB.block))
        (Internal.expectedCNOTLZ cTB.block tTB.block spec.control.idx spec.target.idx) = true := by
  unfold checkTransversalCNOT at h
  simp only [hc, ht] at h
  by_cases hsame : (spec.control == spec.target) = true
  · simp [hsame] at h
  · by_cases hblk : (spec.control.blk == spec.target.blk) = true
    · simp [hsame, hblk] at h
    · by_cases hclive : (!cTB.block.live) = true
      · simp [hsame, hblk, hclive] at h
      · simp at hclive
        by_cases htlive : (!tTB.block.live) = true
        · simp [hsame, hblk, hclive, htlive] at h
        · simp at htlive
          by_cases hcidx : decide (spec.control.idx < cTB.block.lx.length) = true
          · by_cases htidx : decide (spec.target.idx < tTB.block.lx.length) = true
            · by_cases hphys :
                Internal.physicallyTransversalIncidence cTB.block.n tTB.block.n
                    spec.incidence = true
              · by_cases hsymp :
                  preservesSymp (cTB.block.n + tTB.block.n)
                      (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence) = true
                · by_cases hstab :
                    (applyMap (cTB.block.n + tTB.block.n)
                      (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence)
                      (Internal.jointStab cTB.block tTB.block)).all
                      (fun r => inSpan (Internal.jointStab cTB.block tTB.block) r) = true
                  · by_cases hLX :
                      Internal.rowsEqualModStab (Internal.jointStab cTB.block tTB.block)
                        (applyMap (cTB.block.n + tTB.block.n)
                          (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence)
                          (Internal.jointLX cTB.block tTB.block))
                        (Internal.expectedCNOTLX cTB.block tTB.block spec.control.idx
                          spec.target.idx) = true
                    · by_cases hLZ :
                        Internal.rowsEqualModStab (Internal.jointStab cTB.block tTB.block)
                          (applyMap (cTB.block.n + tTB.block.n)
                            (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence)
                            (Internal.jointLZ cTB.block tTB.block))
                          (Internal.expectedCNOTLZ cTB.block tTB.block spec.control.idx
                            spec.target.idx) = true
                      · exact ⟨hphys, hstab, hLX, hLZ⟩
                      · simp at hLZ
                        simp [hsame, hblk, hclive, htlive, hcidx, htidx, hphys,
                          hsymp, hstab, hLX, hLZ] at h
                    · simp at hLX
                      simp [hsame, hblk, hclive, htlive, hcidx, htidx, hphys,
                        hsymp, hstab, hLX] at h
                  · simp at hstab
                    simp [hsame, hblk, hclive, htlive, hcidx, htidx, hphys,
                      hsymp, hstab] at h
                · simp at hsymp
                  simp [hsame, hblk, hclive, htlive, hcidx, htidx, hphys, hsymp] at h
              · simp at hphys
                simp [hsame, hblk, hclive, htlive, hcidx, htidx, hphys] at h
            · simp at htidx
              simp [hsame, hblk, hclive, htlive, hcidx, htidx] at h
          · simp at hcidx
            simp [hsame, hblk, hclive, htlive, hcidx] at h

/-- **Soundness of `checkTransversalCNOTBatch`**.  Acceptance of a batched
    incidence-certified logical CNOT implies physical transversality, stabilizer
    preservation on the product code, and the requested full logical CNOT
    incidence on X/Z logical bases modulo the product stabilizer. -/
theorem checkTransversalCNOTBatch_sound {Gamma : TypedEnv}
    {spec : TransversalCNOTBatchSpec} {e : TypedTransversalCNOTBatch}
    {cTB tTB : TypedBlock}
    (hc : Gamma.block? spec.controlBlock = some cTB)
    (ht : Gamma.block? spec.targetBlock = some tTB)
    (h : checkTransversalCNOTBatch Gamma spec = .ok e) :
    Internal.logicalIncidenceWf cTB.block.lx.length tTB.block.lx.length
        spec.logicalIncidence = true ∧
      Internal.physicallyTransversalIncidence cTB.block.n tTB.block.n
        spec.incidence = true ∧
      (applyMap (cTB.block.n + tTB.block.n)
        (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence)
        (Internal.jointStab cTB.block tTB.block)).all
        (fun r => inSpan (Internal.jointStab cTB.block tTB.block) r) = true ∧
      Internal.rowsEqualModStab (Internal.jointStab cTB.block tTB.block)
        (applyMap (cTB.block.n + tTB.block.n)
          (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence)
          (Internal.jointLX cTB.block tTB.block))
        (Internal.expectedCNOTBatchLX cTB.block tTB.block spec.logicalIncidence) = true ∧
      Internal.rowsEqualModStab (Internal.jointStab cTB.block tTB.block)
        (applyMap (cTB.block.n + tTB.block.n)
          (Internal.cnotMap cTB.block.n tTB.block.n spec.incidence)
          (Internal.jointLZ cTB.block tTB.block))
        (Internal.expectedCNOTBatchLZ cTB.block tTB.block spec.logicalIncidence) = true := by
  simp only [checkTransversalCNOTBatch, hc, ht] at h
  repeat (split at h <;> first | contradiction | skip)
  exact ⟨by simp_all (config := { maxSteps := 1000000 }),
    by simp_all (config := { maxSteps := 1000000 }),
    by simp_all (config := { maxSteps := 1000000 }),
    by simp_all (config := { maxSteps := 1000000 }),
    by simp_all (config := { maxSteps := 1000000 })⟩

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

/-- **Merged-code soundness of `checkPPM`** (the cross-code / HIGH-WEIGHT capability
    branch).  If a PPM is accepted via capability `cap` (i.e. the NATIVE gate
    `touched ≤ 1 ∧ nativeArity` is FALSE — a multi-block OR high-weight target), then the
    recomputed merged stabilizer code (a) pairwise commutes — it is a valid code; (b)
    contains every lifted data stabilizer — it preserves the data codes; and (c) measures
    the target Pauli's representative.  This is the merged-code certificate, not merely
    touched-block validity; it holds for ANY target weight (the proof never used `P.wf`),
    so it now also covers high-weight (>2-body) GPPM/QGPU/high-rate targets. -/
theorem checkPPM_merged_sound {Γ : TypedEnv} {caps : List Capability} {P : PPM.MTarget}
    {r : TypedPPM} {bos : List (BlockId × Block × Nat)} {dataN : Nat} {cap : Capability}
    (hg : gather Γ (dedupNat (P.map (fun f => f.1.blk))) = some (bos, dataN))
    (hcap : caps.find? (fun c => decide (c.blocks = dedupNat (P.map (fun f => f.1.blk)))) = some cap)
    (hbranch : ¬ ((decide ((dedupNat (P.map (fun f => f.1.blk))).length ≤ 1) && P.nativeArity) = true))
    (h : checkPPM Γ caps P = .ok r) :
    sympOrthogonal (dataN + cap.ancN) (mergedStabOf bos (dataN + cap.ancN) cap.connStab)
        (mergedStabOf bos (dataN + cap.ancN) cap.connStab) = true ∧
      (liftedStabOf bos (dataN + cap.ancN)).all
        (fun row => inSpan (mergedStabOf bos (dataN + cap.ancN) cap.connStab) row) = true ∧
      inSpan (mergedStabOf bos (dataN + cap.ancN) cap.connStab) (targetPOf bos (dataN + cap.ancN) P) = true := by
  simp only [checkPPM, hg, hcap] at h
  -- peel every guard: error branches die (`contradiction`, using `hbranch` for the
  -- native gate case); only the capability-success branch survives.
  repeat (split at h <;> first | contradiction | skip)
  refine ⟨of_guard_false ?_, of_guard_false ?_, of_guard_false ?_⟩ <;> assumption

/-- **Structural no-dup soundness of `checkPPM`** (preserved across the weight refactor):
    every accepted target has no repeated logical qubit, at ANY weight. -/
theorem checkPPM_noDup {Γ : TypedEnv} {caps : List Capability} {P : PPM.MTarget}
    {r : TypedPPM} (h : checkPPM Γ caps P = .ok r) : P.noDupQubits = true := by
  simp only [checkPPM] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · rename_i hnd; simpa using hnd

end TypeChecker
