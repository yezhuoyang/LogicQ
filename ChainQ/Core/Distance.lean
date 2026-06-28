/-
  ChainQ.Distance -- theorem-backed CSS distance-bound profiles.

  Policy:
    * Lean does NOT search for distance.
    * Lean does NOT enumerate supports/vectors.
    * Lean does NOT call solvers, decoders, ILP/SAT, or bounded brute force.

  Distance information enters the type system as a theorem/profile certificate:
  a family theorem, product/systolic inequality, graph-expansion theorem, cleaning
  lemma upper bound, or paper-table theorem that has been audited outside Lean.
  The executable Lean work here is cheap arithmetic and consistency checking.
-/
import ChainQ.Core.Params

namespace ChainQ

/-- Logical side whose distance is being bounded. -/
inductive LogicalSide
  | x
  | z
  deriving DecidableEq, Repr, Inhabited

/-- A source class for distance information.  These tags describe why a bound is
    available; they deliberately do not encode any search procedure. -/
inductive DistanceBoundSource
  | familyTheorem        (name : String)
  | productSystolic      (name : String)
  | graphExpansion       (name : String)
  | cleaningUpperBound   (name : String)
  | paperTableTheorem    (name : String)
  | externalFormalTheorem (name : String)
  deriving Repr, Inhabited

/-- Lower/upper bounds for one logical side, together with their theorem sources. -/
structure SideDistanceBounds where
  lower       : Option Nat := none
  upper       : Option Nat := none
  lowerSource : Option DistanceBoundSource := none
  upperSource : Option DistanceBoundSource := none
  deriving Repr, Inhabited

/-- CSS distance profile.  Code distance is `min(dX,dZ)`, so a certified lower
    bound needs both sides; a certified upper bound needs either side. -/
structure CSSDistanceBounds where
  x : SideDistanceBounds := {}
  z : SideDistanceBounds := {}
  deriving Repr, Inhabited

def optionLe (lo hi : Option Nat) : Bool :=
  match lo, hi with
  | some a, some b => decide (a <= b)
  | _, _ => true

def hasLowerSource (b : SideDistanceBounds) : Bool :=
  match b.lower with
  | some _ => b.lowerSource.isSome
  | none => true

def hasUpperSource (b : SideDistanceBounds) : Bool :=
  match b.upper with
  | some _ => b.upperSource.isSome
  | none => true

def SideDistanceBounds.consistent (b : SideDistanceBounds) : Bool :=
  optionLe b.lower b.upper && hasLowerSource b && hasUpperSource b

def CSSDistanceBounds.consistent (b : CSSDistanceBounds) : Bool :=
  b.x.consistent && b.z.consistent

/-- Lower bound on code distance needs lower bounds for both X and Z sides. -/
def minBoth? : Option Nat -> Option Nat -> Option Nat
  | some a, some b => some (Nat.min a b)
  | _, _ => none

/-- Upper bound on code distance needs an upper bound for at least one side. -/
def minKnown? : Option Nat -> Option Nat -> Option Nat
  | none, none => none
  | some a, none => some a
  | none, some b => some b
  | some a, some b => some (Nat.min a b)

def CSSDistanceBounds.lower? (b : CSSDistanceBounds) : Option Nat :=
  minBoth? b.x.lower b.z.lower

def CSSDistanceBounds.upper? (b : CSSDistanceBounds) : Option Nat :=
  minKnown? b.x.upper b.z.upper

def CSSDistanceBounds.meetsLower (b : CSSDistanceBounds) (required : Nat) : Bool :=
  b.consistent &&
  match b.lower? with
  | some lb => decide (required <= lb)
  | none => false

def CSSDistanceBounds.exactFrom (source : DistanceBoundSource) (d : Nat) : CSSDistanceBounds :=
  { x := { lower := some d, upper := some d,
           lowerSource := some source, upperSource := some source },
    z := { lower := some d, upper := some d,
           lowerSource := some source, upperSource := some source } }

def CSSDistanceBounds.lowerFrom
    (source : DistanceBoundSource) (dx dz : Nat) : CSSDistanceBounds :=
  { x := { lower := some dx, lowerSource := some source },
    z := { lower := some dz, lowerSource := some source } }

def CSSDistanceBounds.upperFrom
    (source : DistanceBoundSource) (side : LogicalSide) (d : Nat) : CSSDistanceBounds :=
  match side with
  | .x => { x := { upper := some d, upperSource := some source } }
  | .z => { z := { upper := some d, upperSource := some source } }

/-- Merge two profiles by taking the strongest known lower bounds and strongest
    known upper bounds.  Sources for equal ties prefer the left profile. -/
def maxOpt : Option Nat -> Option Nat -> Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (Nat.max a b)

def minOpt : Option Nat -> Option Nat -> Option Nat
  | none, b => b
  | a, none => a
  | some a, some b => some (Nat.min a b)

def chooseLowerSource (a b : SideDistanceBounds) : Option DistanceBoundSource :=
  match a.lower, b.lower with
  | some av, some bv => if bv > av then b.lowerSource else a.lowerSource
  | some _, none => a.lowerSource
  | none, some _ => b.lowerSource
  | none, none => none

def chooseUpperSource (a b : SideDistanceBounds) : Option DistanceBoundSource :=
  match a.upper, b.upper with
  | some av, some bv => if bv < av then b.upperSource else a.upperSource
  | some _, none => a.upperSource
  | none, some _ => b.upperSource
  | none, none => none

def SideDistanceBounds.merge (a b : SideDistanceBounds) : SideDistanceBounds :=
  { lower := maxOpt a.lower b.lower,
    upper := minOpt a.upper b.upper,
    lowerSource := chooseLowerSource a b,
    upperSource := chooseUpperSource a b }

def CSSDistanceBounds.merge (a b : CSSDistanceBounds) : CSSDistanceBounds :=
  { x := a.x.merge b.x, z := a.z.merge b.z }

/-! ## Cheap theorem combinators. -/

def surfaceDistanceBounds? (d : Nat) : Option CSSDistanceBounds :=
  if 2 <= d then
    some (CSSDistanceBounds.exactFrom (.familyTheorem "surface code distance theorem") d)
  else none

def toricDistanceBounds? (d : Nat) : Option CSSDistanceBounds :=
  if 2 <= d then
    some (CSSDistanceBounds.exactFrom (.familyTheorem "toric code distance theorem") d)
  else none

/-- Zeng--Pryadko-style product systolic lower bound:
    `sys_k(A⊗B) >= min(sys_{k-1}(A) * sys_1(B), sys_k(A) * sys_0(B))`.
    This is arithmetic over supplied component systoles, not a search. -/
def zengPryadkoLower (sysAPrev sysA sysB0 sysB1 : Nat) : Nat :=
  Nat.min (sysAPrev * sysB1) (sysA * sysB0)

def productSystolicLowerBounds
    (sourceName : String)
    (xSysAPrev xSysA xSysB0 xSysB1 : Nat)
    (zSysAPrev zSysA zSysB0 zSysB1 : Nat) : CSSDistanceBounds :=
  let source := DistanceBoundSource.productSystolic sourceName
  CSSDistanceBounds.lowerFrom source
    (zengPryadkoLower xSysAPrev xSysA xSysB0 xSysB1)
    (zengPryadkoLower zSysAPrev zSysA zSysB0 zSysB1)

/-- Expansion/cosystolic-expansion theorem as a pre-audited lower-bound profile.
    The checker verifies only that a named theorem supplied both side bounds. -/
def expansionLowerBounds (sourceName : String) (dx dz : Nat) : CSSDistanceBounds :=
  CSSDistanceBounds.lowerFrom (.graphExpansion sourceName) dx dz

/-- A cleaning-lemma/geometric/no-go theorem can provide an upper bound. -/
def cleaningUpperBound (sourceName : String) (side : LogicalSide) (d : Nat) : CSSDistanceBounds :=
  CSSDistanceBounds.upperFrom (.cleaningUpperBound sourceName) side d

/-- Paper table theorem: used for fixed named examples whose distance/bounds come
    from a cited construction, not from Lean search. -/
def paperTableExact (sourceName : String) (d : Nat) : CSSDistanceBounds :=
  CSSDistanceBounds.exactFrom (.paperTableTheorem sourceName) d

/-- Catalog of fixed paper-table profiles currently known to ChainQ.  This is
    deliberately a whitelist: arbitrary strings do not become distance theorems. -/
def knownPaperTableProfile? (sourceName : String) (n k d : Nat) : Option CSSDistanceBounds :=
  let ok (n0 k0 d0 : Nat) :=
    if n == n0 && k == k0 && d == d0 then some (paperTableExact sourceName d0) else none
  if sourceName == "Universal Adapters BB1 [[98,6,12]]" then
    ok 98 6 12
  else if sourceName == "Universal Adapters LP2 [[200,20,10]]" then
    ok 200 20 10
  else if sourceName == "Transversal dimension-jump BB [[18,2,3]] row" then
    ok 18 2 3
  else if sourceName == "Transversal dimension-jump BB [[30,2,5]] row" then
    ok 30 2 5
  else if sourceName == "Transversal dimension-jump BB [[54,2,6]] row" then
    ok 54 2 6
  else if sourceName == "Transversal dimension-jump lifted-toric LP [[16,2,4]] row" then
    ok 16 2 4
  else if sourceName == "Transversal dimension-jump lifted-toric LP [[36,2,6]] row" then
    ok 36 2 6
  else none

def knownPaperTableProfileByParams? (n k d : Nat) : Option CSSDistanceBounds :=
  if n == 98 && k == 6 && d == 12 then
    some (paperTableExact "Universal Adapters BB1 [[98,6,12]]" 12)
  else if n == 200 && k == 20 && d == 10 then
    some (paperTableExact "Universal Adapters LP2 [[200,20,10]]" 10)
  else if n == 18 && k == 2 && d == 3 then
    some (paperTableExact "Transversal dimension-jump BB [[18,2,3]] row" 3)
  else if n == 30 && k == 2 && d == 5 then
    some (paperTableExact "Transversal dimension-jump BB [[30,2,5]] row" 5)
  else if n == 54 && k == 2 && d == 6 then
    some (paperTableExact "Transversal dimension-jump BB [[54,2,6]] row" 6)
  else if n == 16 && k == 2 && d == 4 then
    some (paperTableExact "Transversal dimension-jump lifted-toric LP [[16,2,4]] row" 4)
  else if n == 36 && k == 2 && d == 6 then
    some (paperTableExact "Transversal dimension-jump lifted-toric LP [[36,2,6]] row" 6)
  else none

/-! ## Smoke checks. -/

example :
    (match surfaceDistanceBounds? 3 with
     | some b => b.meetsLower 3
     | none => false) = true := by decide

example :
    (match surfaceDistanceBounds? 1 with
     | some _ => true
     | none => false) = false := by decide

example : zengPryadkoLower 2 5 1 7 = 5 := by decide
example :
    (productSystolicLowerBounds "toy product theorem" 2 5 1 7 3 4 2 5).lower? = some 5 := by decide

example :
    (paperTableExact "toy [[n,k,d]] theorem" 3).meetsLower 3 = true := by decide

example :
    (knownPaperTableProfile? "Universal Adapters LP2 [[200,20,10]]" 200 20 10).isSome = true := by decide

example :
    knownPaperTableProfile? "Universal Adapters LP2 [[200,20,10]]" 199 20 10 = none := by decide

example :
    knownPaperTableProfile? "Universal Adapters LP2 [[200,20,10]]" 200 20 11 = none := by decide

example :
    (knownPaperTableProfileByParams? 200 20 10).isSome = true := by decide

example :
    knownPaperTableProfileByParams? 200 20 11 = none := by decide

example :
    (CSSDistanceBounds.merge
      (CSSDistanceBounds.lowerFrom (.graphExpansion "A") 3 4)
      (CSSDistanceBounds.lowerFrom (.productSystolic "B") 5 2)).lower? = some 4 := by decide

end ChainQ
