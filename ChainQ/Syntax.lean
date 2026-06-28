/-
  ChainQ.Syntax -- source declarations for ChainQ code families.

  This module is the small language-facing boundary for declaring CSS code
  families.  The declarations are pure syntax/data; `CodeDecl.check?` is the
  elaboration/type-checking step into the proof-carrying `CheckedCSSCode`
  constructors owned by `ChainQ.Checked`.
-/
import ChainQ.Checked
import ChainQ.Distance
import ChainQ.LogicalIndex

namespace ChainQ
open ChainQ.GF2

/-! ## Code-family declarations. -/

/-- Source-level ChainQ code declarations.

    These constructors are intentionally close to the mathematical families:
    users describe a family instance here, and the checked constructors remain
    the only route into `CheckedCSSCode`. -/
inductive CodeDecl where
  | css (code : CSSCode)
  | surface (d : Nat)
  | toric (d : Nat)
  | hgp (h1 h2 : BoolMat) (m1 n1 m2 n2 : Nat)
  | bb (l m : Nat) (a b : List (Prod Nat Nat))
  | liftedProduct (l : Nat) (A : List (List Circ)) (rA nA : Nat)
  deriving Repr

/-- Source-level declared parameters `[[n,k,d]]`.  `n` and `k` are checked against
    the compiled code; `d` must be backed by a theorem/profile certificate. -/
structure CodeParamClaim where
  n : Nat
  k : Nat
  d : Nat
  deriving Repr, DecidableEq, Inhabited

/-- A named ChainQ declaration, matching the shape of source programs where code
    families are referred to by identifier. -/
structure NamedCodeDecl where
  name : String
  decl : CodeDecl
  claimedParams : Option CodeParamClaim := none
  distanceProfile : Option CSSDistanceBounds := none
  logicalIndex : Option LogicalIndexSpec := none
  deriving Repr

/-- Elaborate and type-check a ChainQ code declaration. -/
def CodeDecl.check? : CodeDecl -> Except ChainQError CheckedCSSCode
  | .css code => mkCSS code
  | .surface d => mkSurface d
  | .toric d => mkToric d
  | .hgp h1 h2 m1 n1 m2 n2 => mkHGP h1 h2 m1 n1 m2 n2
  | .bb l m a b => mkBB l m a b
  | .liftedProduct l A rA nA => mkLiftedProduct l A rA nA

/-- Does a theorem-backed distance profile prove exact distance `d`?  Exactness
    means the profile gives both a lower and an upper bound equal to `d`. -/
def CSSDistanceBounds.provesExactDistance (bounds : CSSDistanceBounds) (d : Nat) : Bool :=
  bounds.consistent && bounds.lower? == some d && bounds.upper? == some d

def CodeParamClaim.checkAgainst
    (claim : CodeParamClaim) (cc : CheckedCSSCode) (bounds? : Option CSSDistanceBounds) :
    Except ChainQError Unit :=
  if !(cc.code.n == claim.n) then
    .error (.badDimension s!"declared n={claim.n}, but compiled code has n={cc.code.n}")
  else if !(cc.code.k == claim.k) then
    .error (.badDimension s!"declared k={claim.k}, but compiled code has k={cc.code.k}")
  else
    match bounds? with
    | none =>
        .error (.badDimension s!"declared d={claim.d}, but no theorem-backed exact distance profile was supplied")
    | some bounds =>
        if bounds.provesExactDistance claim.d then .ok ()
        else .error (.badDimension s!"declared d={claim.d}, but the supplied distance profile does not prove exact d")

/-- Elaborate and type-check a named ChainQ declaration. -/
def NamedCodeDecl.check? (decl : NamedCodeDecl) : Except ChainQError CheckedCSSCode :=
  match decl.decl.check? with
  | .error e => .error e
  | .ok cc =>
      match decl.claimedParams with
      | none => .ok cc
      | some claim =>
          match claim.checkAgainst cc decl.distanceProfile with
          | .ok _ => .ok cc
          | .error e => .error e

/-- Elaborate a named declaration and require the user-specified logical-qubit
    indexing to validate.  This is the strict source entry point for protocols
    that address logical qubits by declared names. -/
def NamedCodeDecl.checkLogicalIndex? (decl : NamedCodeDecl) :
    Except ChainQError CheckedLogicalIndex := do
  let cc ← decl.check?
  match decl.logicalIndex with
  | some spec => mkLogicalIndex? cc spec
  | none => .error (.logicalDerivationFailed "missing user-specified logical qubit indexing")

/-! ## Syntax smoke tests. -/

example : isOk ((CodeDecl.surface 3).check?) = true := by decide
example : isOk ((CodeDecl.toric 2).check?) = true := by decide
example : isOk ((CodeDecl.bb 3 3 [(0, 0), (1, 0), (0, 2)] [(0, 0), (2, 0), (0, 1)]).check?) = true := by decide
example : isOk ((CodeDecl.liftedProduct 3 [[[0], [1]]] 1 2).check?) = true := by decide

def claimedSurface3 : NamedCodeDecl :=
  { name := "surface3",
    decl := .surface 3,
    claimedParams := some { n := 13, k := 1, d := 3 },
    distanceProfile := surfaceDistanceBounds? 3 }

def badNClaimSurface3 : NamedCodeDecl :=
  { claimedSurface3 with claimedParams := some { n := 12, k := 1, d := 3 } }

def badDClaimSurface3 : NamedCodeDecl :=
  { claimedSurface3 with claimedParams := some { n := 13, k := 1, d := 4 } }

def missingDistanceClaimSurface3 : NamedCodeDecl :=
  { claimedSurface3 with distanceProfile := none }

example : isOk claimedSurface3.check? = true := by decide
example : isOk badNClaimSurface3.check? = false := by decide
example : isOk badDClaimSurface3.check? = false := by decide
example : isOk missingDistanceClaimSurface3.check? = false := by decide

def badNClaimTinyLP : NamedCodeDecl :=
  { name := "bad_tiny_lp",
    decl := .liftedProduct 3 [[[0], [1]]] 1 2,
    claimedParams := some { n := 14, k := 0, d := 1 },
    distanceProfile := some (paperTableExact "toy tiny LP exact profile" 1) }

example : isOk badNClaimTinyLP.check? = false := by decide

def indexedBareDecl : NamedCodeDecl :=
  { name := "bare",
    decl := .css bareQubit,
    logicalIndex := some bareQubitIndexSpec }

def badIndexedBareDecl : NamedCodeDecl :=
  { indexedBareDecl with logicalIndex := some badBareQubitIndexSpec }

def indexedTwoLogicalDecl : NamedCodeDecl :=
  { name := "two_logicals",
    decl := .css bareTwoQubit,
    logicalIndex := some bareTwoQubitIndexSpec }

example : isOk indexedBareDecl.checkLogicalIndex? = true := by decide
example : isOk badIndexedBareDecl.checkLogicalIndex? = false := by decide
example : isOk ({ indexedBareDecl with logicalIndex := none }).checkLogicalIndex? = false := by decide
example : isOk indexedTwoLogicalDecl.checkLogicalIndex? = true := by decide

end ChainQ
