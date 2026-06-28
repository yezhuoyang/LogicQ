/-
  TypeChecker.Judgment.PPM.Check — the proof-carrying capability matcher
  `checkPPM` and its raw entry point `checkPPMFromEnv`.
-/
import TypeChecker.Judgment.PPM.Lift
import TypeChecker.Judgment.PPM.Certificate
import TypeChecker.Capability.Defs
import TypeChecker.Core.Error

namespace TypeChecker
open ChainQ.GF2

/-- Deferred obligations per construction (faithful to the papers). -/
def ppmObligations : CapKind → List String
  | .nativeSurgery          => ["merged-code distance", "fault distance R ≥ d", "decoder for merged syndrome"]
  | .adapterPPM             => ["relative expansion β_d ≥ 1", "thickening L", "decoder for merged code"]
  | .productSurgery         => ["Künneth / numerical merged distance", "soundness ρ", "schedule feasibility"]
  | .homomorphicMeasurement => ["Cheeger h ≥ 1 (X-distance)", "Z-distance preserved", "ancilla Shor prep"]
  | .bridge                 => ["bridge gauge-check weight", "recursive-bridging β_d ≥ 1", "R ≥ d rounds"]

/-- **MILESTONE 3.**  The proof-carrying capability matcher for logical PPM over a
    TYPED environment.  Every touched block is well-formed by `TypedEnv` (no
    `Block.valid` recheck).  An EMPTY target is rejected (no identity/no-op form). -/
def checkPPM (Γ : TypedEnv) (caps : List Capability) (P : PPM.MTarget) :
    Except TypeError TypedPPM :=
  if P.isEmpty then .error .emptyMeasurement
  -- STRUCTURAL: no repeated logical qubit (the weight-independent part of the old
  -- `MTarget.wf`).  The native 1-/2-body ARITY cap is now applied ONLY in the native
  -- branch below, so a HIGH-WEIGHT target can still reach the capability path and be
  -- admitted IFF a merged-code certificate proves it is measured.
  else if !P.noDupQubits then .error .nonNativeMeasurement else
  let touched := dedupNat (P.map (fun f => f.1.blk))
  match gather Γ touched with
  | none => .error (.badBlock 0)
  | some (bos, dataN) =>
    -- HARD: every factor must reference an IN-RANGE logical index of a live block
    -- (a nonexistent logical qubit is REJECTED, never treated as identity/zero).
    match P.find? (fun f =>
        match bos.find? (fun t => t.1 == f.1.blk) with
        | some t => (factorRep? t.2.1 f.1.idx f.2).isNone
        | none   => true) with
    | some f => .error (.badLogicalIndex f.1.blk f.1.idx)
    | none =>
    -- DEFENSIVE: P restricted to each block must be a logical operator (commute
    -- with the block's stabilizers).  NOTE: since `TypedEnv` guarantees every
    -- block's `lx`/`lz` already commute with its stabilizers, and `restrictOf` is
    -- an XOR of those logical rows, this always holds — so `notLogicalOp` is now
    -- SUBSUMED by the typed environment and fires only as a defensive backstop.
    let restrictOf := fun (bid : BlockId) (blk : Block) =>
      (P.filter (fun f => f.1.blk == bid)).foldl
        (fun acc f => vecXor acc (factorRepD blk f.1.idx f.2)) (zeros (2 * blk.n))
    if !(bos.all (fun t => commutesAllSt t.2.1.n t.2.1.stab (restrictOf t.1 t.2.1))) then
      .error .notLogicalOp
    else if decide (touched.length ≤ 1) && P.nativeArity then
      -- a NATIVE single-code logical measurement: one block, weight 1 or 2
      .ok { target := P, kind := .nativeSurgery, mergedN := dataN,
            obligations := ["fault-tolerant syndrome extraction"] }
    else
      match caps.find? (fun c => decide (c.blocks = touched)) with
      | none =>
        .error (.noCommonCapability
          "no native PPM, no adapter, no switch path: the blocks live in different measurement domains and no installed capability bridges them")
      | some cap =>
        let mergedN    := dataN + cap.ancN
        if !(cap.connStab.all (fun r => decide (r.length = 2 * mergedN))) then
          .error (.shapeMismatch "capability connStab rows must have width 2·mergedN")
        else
        let mergedStab := mergedStabOf bos mergedN cap.connStab
        if !(sympOrthogonal mergedN mergedStab mergedStab) then
          .error (.certFailed "merged code stabilizers must pairwise commute")
        else if !((liftedStabOf bos mergedN).all (fun r => inSpan mergedStab r)) then
          .error (.certFailed "merge must preserve the data codes (data stabilizers ⊆ merged group)")
        else if !(inSpan mergedStab (targetPOf bos mergedN P)) then
          .error (.certFailed "the target logical Pauli is not measured by the merge")
        else
          .ok { target := P, kind := cap.kind, mergedN := mergedN,
                obligations := ppmObligations cap.kind }

/-- Raw entry point: validate the environment ONCE at the boundary, then run the
    matcher.  A malformed env block is rejected here as `malformedBlock i`. -/
def checkPPMFromEnv (Γ : Env) (caps : List Capability) (P : PPM.MTarget) :
    Except TypeError TypedPPM := do
  let tΓ ← TypedEnv.ofEnv? Γ
  checkPPM tΓ caps P

end TypeChecker
