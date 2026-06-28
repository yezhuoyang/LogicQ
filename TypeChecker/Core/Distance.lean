/-
  TypeChecker.Core.Distance -- distance-bound obligations for typed blocks.

  The core block validity check proves algebraic code/logical well-formedness.
  Fault-tolerant operations often need more: a certified lower bound on code
  distance.  This module keeps that requirement explicit and machine-checkable.
-/
import TypeChecker.Core.Block

namespace TypeChecker
open ChainQ ChainQ.GF2

/-- Evidence that a typed block carries a distance profile strong enough for a
    requested operation/protocol threshold. -/
structure TypedDistanceEvidence where
  block    : BlockId
  required : Nat
  bounds   : CSSDistanceBounds
  deriving Repr

/-- A named distance obligation.  The checker accepts it only when the profile
    carries lower bounds on both X and Z distances and their minimum is at least
    `required`. -/
structure DistanceObligation where
  required : Nat
  reason   : String := ""
  bounds   : CSSDistanceBounds
  deriving Repr

def DistanceObligation.verifiedCheck (o : DistanceObligation) : Bool :=
  o.bounds.meetsLower o.required

def Block.distanceLower? (b : Block) : Option Nat :=
  match b.dist with
  | some bounds => bounds.lower?
  | none => none

def Block.meetsDistance (b : Block) (required : Nat) : Bool :=
  match b.dist with
  | some bounds => bounds.meetsLower required
  | none => false

/-- Check a block-local distance obligation inside a typed environment.  This is
    the hook protocol checkers should call before discharging any FT path whose
    paper proof assumes `d >= required`. -/
def checkBlockDistance
    (Gamma : TypedEnv) (b : BlockId) (required : Nat) :
    Except TypeError TypedDistanceEvidence :=
  match Gamma.block? b with
  | none => .error (.badBlock b)
  | some tb =>
      match tb.block.dist with
      | some bounds =>
          if bounds.meetsLower required then
            .ok { block := b, required := required, bounds := bounds }
          else
            .error (.certFailed "distance lower-bound obligation is not discharged")
      | none =>
          .error (.certFailed "block has no certified distance lower-bound profile")

/-- Convenience checker for a standalone obligation. -/
def verifyDistanceObligation (o : DistanceObligation) :
    Except TypeError DistanceObligation :=
  if o.verifiedCheck then .ok o
  else .error (.certFailed "distance obligation failed")

/-! ## Smoke checks. -/

def oneQWithDistance : Block :=
  { n := 1,
    stab := [],
    lx := [[true, false]],
    lz := [[false, true]],
    dist := some (paperTableExact "toy exact distance theorem" 1) }

def oneQNoDistance : Block :=
  { n := 1,
    stab := [],
    lx := [[true, false]],
    lz := [[false, true]] }

def oneQDistanceEnv : TypedEnv :=
  { blocks := [⟨oneQWithDistance, by decide⟩] }

def oneQNoDistanceEnv : TypedEnv :=
  { blocks := [⟨oneQNoDistance, by decide⟩] }

example : ok? (checkBlockDistance oneQDistanceEnv 0 1) = true := by decide
example : ok? (checkBlockDistance oneQDistanceEnv 0 2) = false := by decide
example : ok? (checkBlockDistance oneQNoDistanceEnv 0 1) = false := by decide
example :
    (DistanceObligation.mk 1 "test" (paperTableExact "toy exact distance theorem" 1)).verifiedCheck = true := by decide

end TypeChecker
