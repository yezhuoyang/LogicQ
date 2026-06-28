/-
  Compiler.CodeSwitch.GPPMSemantics — the GPPM static/semantic premises, made EXPLICIT.

  The homomorphic-CNOT bridge (`Compiler.ChainQ2Mixed.homCNOTBridge?`) verifies only the
  CNOT induced action.  A FULL generalized PPM additionally needs:

    (1) the ancilla PREPARED in the required basis;
    (2) the ancilla MEASUREMENT basis;
    (3) the outcome variable EQUALS the claimed logical Pauli product;
    (4) the byproduct FRAME update.

  This module records all four as EXPLICIT premises.  What is RECOMPUTED here: the merged
  code is CSS and the claimed target IS measured by the merge (premise 3's structural
  half — `target ∈ merged Z-span`, via `ProductSurgeryCert`), and the byproduct frame is
  TYPE-CHECKED (`Compiler.ChainQ2Mixed.Frame`).  What stays DEFERRED (so this is HONEST):
  the OPERATIONAL measurement-outcome rule (outcome var = the measured Pauli's eigenvalue)
  has no `Step` semantics, and the ancilla STATE preparation is a declared tag.  Therefore
  a `GPPMArtifact` is **NOT a `CheckedPrimitive`** (there is deliberately no `MixPrim.gppm`).
-/
import Compiler.CodeSwitch.ProductSurgery
import Compiler.ChainQ2Mixed.Frame

namespace Compiler.CodeSwitch
open ChainQ.GF2 TypeChecker

/-! ## §G.1. Declared bases + the GPPM spec. -/

/-- The basis an ancilla must be PREPARED in for the protocol. -/
inductive PrepBasis | zeroState | plusState | magicY
  deriving DecidableEq, Repr

/-- The ancilla MEASUREMENT basis. -/
inductive MeasBasis | zBasis | xBasis
  deriving DecidableEq, Repr

/-- A GPPM protocol spec: the product surgery realizing the merge, the CLAIMED measured
    logical Pauli product (a merged-`Z` support vector), the declared ancilla prep +
    measurement bases, the outcome variable, and the byproduct-frame feed-forward. -/
structure GPPMSpec where
  surgery     : ProductSurgeryCert
  target      : BoolVec
  prepBasis   : PrepBasis
  measBasis   : MeasBasis
  outcome     : Nat
  feedforward : List Compiler.ChainQ2Mixed.Frame.FrameExpr
  deriving Repr

/-- The DEFERRED semantic obligations a GPPM still carries (so it is NOT a CheckedPrimitive). -/
def gppmSemanticObligations : List String :=
  ["operational measurement-outcome rule: outcome var = eigenvalue of the measured logical Pauli (DEFERRED — no Step)",
   "ancilla STATE preparation in the declared basis (DEFERRED — declared tag, not operational)",
   "byproduct frame application (TYPED by Frame.checkFrameProgram; operational rule DEFERRED)",
   "merged-code distance / decoder / fault tolerance (DEFERRED — see ProductSurgeryCert)"]

/-- The feed-forward binds the GPPM measurement OUTCOME variable EXACTLY once (SSA): the
    `outcome` is the result of the measurement event and must be a `.bind outcome` in the
    feed-forward — so a stray/unconnected outcome variable is rejected. -/
def GPPMSpec.bindsOutcomeOnce (s : GPPMSpec) : Bool :=
  (s.feedforward.filter (fun e => match e with
    | Compiler.ChainQ2Mixed.Frame.FrameExpr.bind v => v == s.outcome
    | _                                            => false)).length == 1

/-- A GPPM artifact over a feed-forward typing context `(Γ, loc, dead)`: the merged code is
    RECOMPUTED-CSS, the claimed target IS measured by the merge (`target ∈ merged Z-span`),
    the byproduct-frame feed-forward TYPE-CHECKS (bind-before-use / no-dup / live carrier
    through `loc`), AND the measurement `outcome` is bound exactly once by the feed-forward.
    Explicitly NOT a `CheckedPrimitive` — the operational measurement-outcome rule + ancilla
    state prep are the deferred `obligations`. -/
structure GPPMArtifact (Γ : TypedEnv) (loc : Compiler.LocMap) (dead : List Logical.LQubit) where
  spec           : GPPMSpec
  merged         : CheckedProductSurgery
  frame          : Compiler.ChainQ2Mixed.Frame.FrameState
  measuresTarget : spec.surgery.measuresZ spec.target = true
  frameChecked   : Compiler.ChainQ2Mixed.Frame.checkFrameProgram Γ loc dead spec.feedforward
                     Compiler.ChainQ2Mixed.Frame.FrameState.init = .ok frame
  outcomeBound   : spec.bindsOutcomeOnce = true
  obligations    : List String

/-! ## §G.2. The checker. -/

/-- **Check a GPPM spec.**  Recomputes (1) the product-surgery merged code (Item 2), (2) that
    the claimed target is measured by the merge, and (3) that the byproduct-frame
    feed-forward TYPE-CHECKS against `(Γ, loc, dead)` via `Frame.checkFrameProgram` (Item 7) —
    so an unbound/dead/duplicate feed-forward is REJECTED.  Records the bases/outcome/checked
    frame + the deferred operational obligations.  Returns a `GPPMArtifact` — NOT a
    `CheckedPrimitive`. -/
def checkGPPM? (Γ : TypedEnv) (loc : Compiler.LocMap) (dead : List Logical.LQubit)
    (maxMerge : Nat) (s : GPPMSpec) : Except TypeError (GPPMArtifact Γ loc dead) :=
  match checkProductSurgery? s.surgery maxMerge with
  | .error e => .error e
  | .ok merged =>
      if hm : s.surgery.measuresZ s.target = true then
        if hb : s.bindsOutcomeOnce = true then
          match hf : Compiler.ChainQ2Mixed.Frame.checkFrameProgram Γ loc dead s.feedforward
                       Compiler.ChainQ2Mixed.Frame.FrameState.init with
          | .ok fr => .ok { spec := s, merged := merged, frame := fr, measuresTarget := hm,
                            frameChecked := hf, outcomeBound := hb, obligations := gppmSemanticObligations }
          | .error e => .error e
        else .error (.certFailed "GPPM: the measurement outcome variable is not bound exactly once by the feed-forward")
      else .error (.certFailed "GPPM: the claimed target Pauli is not measured by the merged code (target ∉ merged Z-span)")

/-- **GPPM soundness (HONEST, structural).**  A checked GPPM has a CSS merged code, a target
    MEASURED by the merge, and a feed-forward that TYPE-CHECKS (recomputed over GF(2) +
    bind/live discipline).  This is NOT operational equivalence: the outcome-var =
    Pauli-eigenvalue rule and ancilla state prep stay deferred (`obligations`), and a
    `GPPMArtifact` is NOT a `CheckedPrimitive`. -/
theorem checkGPPM?_sound (Γ : TypedEnv) (loc : Compiler.LocMap) (dead : List Logical.LQubit)
    (maxMerge : Nat) (s : GPPMSpec) {a : GPPMArtifact Γ loc dead}
    (_h : checkGPPM? Γ loc dead maxMerge s = .ok a) :
    orthogonal a.merged.cert.mergedHX a.merged.cert.mergedHZ = true ∧
      a.spec.surgery.measuresZ a.spec.target = true ∧
      Compiler.ChainQ2Mixed.Frame.checkFrameProgram Γ loc dead a.spec.feedforward
        Compiler.ChainQ2Mixed.Frame.FrameState.init = .ok a.frame ∧
      a.spec.bindsOutcomeOnce = true :=
  ⟨a.merged.mergedCSS, a.measuresTarget, a.frameChecked, a.outcomeBound⟩

/-! ## §G.3. Tests. -/

/-- A GPPM measuring the data `Z₀Z₁`-product via the `psOK` product surgery, ancilla in
    `|+⟩`, measured in `Z`, with an outcome-conditioned `X` byproduct frame. -/
def gppmOK : GPPMSpec :=
  { surgery := psOK, target := [true, true, false, false], prepBasis := .plusState,
    measBasis := .zBasis, outcome := 0,
    feedforward := [.bind 0, .applyIf 0 ⟨0, 0⟩ .X] }

/-- The feed-forward typing context: the 1-logical env (block 0 has ⟨0,0⟩), identity loc, no
    dead carriers. -/
abbrev gEnv : TypedEnv := Compiler.ChainQ2Mixed.Frame.fEnv

example : ok? (checkGPPM? gEnv [] [] 1 gppmOK) = true := by decide
-- the artifact carries the DEFERRED operational obligations (NOT operational correctness):
example : (match checkGPPM? gEnv [] [] 1 gppmOK with | .ok a => a.obligations.length | .error _ => 0) = 4 := by decide

-- NEGATIVE — a GPPM with an UNBOUND feed-forward variable is REJECTED by checkGPPM? (the
-- frame check is now INTEGRATED — Item 4 fix: an applyIf with no prior bind cannot pass):
def gppmUnbound : GPPMSpec := { gppmOK with feedforward := [.applyIf 0 ⟨0, 0⟩ .X] }
example : ok? (checkGPPM? gEnv [] [] 1 gppmUnbound) = false := by decide
-- NEGATIVE — a feed-forward frame update to a DEAD carrier is REJECTED:
example : ok? (checkGPPM? gEnv [] [⟨0, 0⟩] 1 gppmOK) = false := by decide
-- NEGATIVE — a DUPLICATE outcome binding in the feed-forward is REJECTED (SSA, via the frame checker):
def gppmDupOutcome : GPPMSpec := { gppmOK with feedforward := [.bind 0, .bind 0] }
example : ok? (checkGPPM? gEnv [] [] 1 gppmDupOutcome) = false := by decide
-- NEGATIVE — an OUTCOME variable NOT bound by the feed-forward is REJECTED (load-bearing outcome):
example : ok? (checkGPPM? gEnv [] [] 1 { gppmOK with outcome := 999 }) = false := by decide
-- NEGATIVE — a STALE loc carrier: the feed-forward targets q0 but loc relocates it to the dead ⟨0,0⟩:
example : ok? (checkGPPM? gEnv [(⟨0, 0⟩, ⟨0, 0⟩)] [⟨0, 0⟩] 1 gppmOK) = false := by decide

-- NEGATIVE — a GPPM whose claimed target is NOT in the merged Z-span is REJECTED:
def gppmBadTarget : GPPMSpec := { gppmOK with target := [false, true, false, false] }
example : psOK.measuresZ [false, true, false, false] = false := by decide
example : ok? (checkGPPM? gEnv [] [] 1 gppmBadTarget) = false := by decide

-- NEGATIVE — a GPPM over a non-CSS merged surgery is REJECTED (inherited from Item 2):
def gppmBadSurgery : GPPMSpec := { gppmOK with surgery := psBadCommute }
example : ok? (checkGPPM? gEnv [] [] 4 gppmBadSurgery) = false := by decide

end Compiler.CodeSwitch
