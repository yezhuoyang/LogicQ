/-
  ChainQ.Core.LogicalIndex -- user-declared logical-qubit indexing.

  Logical Z is a homology object: for a CSS code it is a Z-support vector in
  `ker Hx` modulo the row span of `Hz`; for a chain complex it is a 1-cycle in
  `ker ∂₁` modulo 1-boundaries `im ∂₂`.  The source-level logical index names
  these Z representatives first, then supplies dual X representatives to finish
  the logical-qubit coordinate system.
-/
import ChainQ.Checked.Basic
import ChainQ.ChainComplex

namespace ChainQ
open ChainQ.GF2

private def firstIndexAux {α : Type} (p : α -> Bool) : List α -> Nat -> Option Nat
  | [], _ => none
  | x :: xs, i => if p x then some i else firstIndexAux p xs (i + 1)

private def firstIndex? {α : Type} (p : α -> Bool) (xs : List α) : Option Nat :=
  firstIndexAux p xs 0

/-! ## Certified logical representatives and diagnostics. -/

inductive LogicalRepError where
  | invalidCSS
  | wrongLength (got expected : Nat)
  | notCycle (checkIndex : Nat)
  | isBoundary (coeffs : BoolVec)
  deriving Repr, DecidableEq

inductive LogicalBasisError where
  | invalidCSS
  | nameCountMismatch (got expected : Nat)
  | duplicateName (name : String)
  | zBasisWrongLength (got expected : Nat)
  | xBasisWrongLength (got expected : Nat)
  | zNotLogical (i : Nat) (err : LogicalRepError)
  | xNotLogical (i : Nat) (err : LogicalRepError)
  | zDependentModuloStabilizers (basisCoeffs stabCoeffs : BoolVec)
  | xDependentModuloStabilizers (basisCoeffs stabCoeffs : BoolVec)
  | badDualPairing (i j : Nat) (got expected : Bool)
  deriving Repr, DecidableEq

def LogicalRepError.message : LogicalRepError -> String
  | .invalidCSS => "code is not a valid CSS code"
  | .wrongLength got expected => s!"support has length {got}, expected {expected}"
  | .notCycle i => s!"support anticommutes with check row {i}"
  | .isBoundary coeffs => s!"support is a stabilizer boundary with coefficients {repr coeffs}"

def LogicalBasisError.message : LogicalBasisError -> String
  | .invalidCSS => "code is not a valid CSS code"
  | .nameCountMismatch got expected => s!"logical-name count {got}, expected {expected}"
  | .duplicateName name => s!"duplicate logical name '{name}'"
  | .zBasisWrongLength got expected => s!"Z-basis row count {got}, expected {expected}"
  | .xBasisWrongLength got expected => s!"X-basis row count {got}, expected {expected}"
  | .zNotLogical i err => s!"Z-basis row {i} failed: {err.message}"
  | .xNotLogical i err => s!"X-basis row {i} failed: {err.message}"
  | .zDependentModuloStabilizers basisCoeffs stabCoeffs =>
      s!"Z-basis is dependent modulo Z-stabilizers; basis={repr basisCoeffs}, stabilizers={repr stabCoeffs}"
  | .xDependentModuloStabilizers basisCoeffs stabCoeffs =>
      s!"X-basis is dependent modulo X-stabilizers; basis={repr basisCoeffs}, stabilizers={repr stabCoeffs}"
  | .badDualPairing i j got expected =>
      s!"bad X/Z pairing at ({i},{j}): got {got}, expected {expected}"

/-- A certified nonzero Z logical representative.  This is not a basis element by
    itself; it is only a nonzero class in `ker Hx / rowSpan Hz`. -/
structure ZLogicalRep (c : CSSCode) where
  support : BoolVec
  valid : c.isNontrivialZLogicalRep support = true

/-- A certified nonzero X logical representative. -/
structure XLogicalRep (c : CSSCode) where
  support : BoolVec
  valid : c.isNontrivialXLogicalRep support = true

def CSSCode.firstAnticommutingXCheck? (c : CSSCode) (z : BoolVec) : Option Nat :=
  firstIndex? (fun x => dotBit x z) c.hx

def CSSCode.firstAnticommutingZCheck? (c : CSSCode) (x : BoolVec) : Option Nat :=
  firstIndex? (fun z => dotBit x z) c.hz

def CSSCode.checkZLogicalRep? (c : CSSCode) (z : BoolVec) :
    Except LogicalRepError (ZLogicalRep c) :=
  if h : c.isNontrivialZLogicalRep z = true then
    .ok { support := z, valid := h }
  else if !c.valid then
    .error .invalidCSS
  else if !(decide (z.length = c.n)) then
    .error (.wrongLength z.length c.n)
  else
    match c.firstAnticommutingXCheck? z with
    | some i => .error (.notCycle i)
    | none =>
        if c.zBoundary z then
          .error (.isBoundary ((solveInSpan? c.hz z).getD []))
        else
          .error .invalidCSS

def CSSCode.checkXLogicalRep? (c : CSSCode) (x : BoolVec) :
    Except LogicalRepError (XLogicalRep c) :=
  if h : c.isNontrivialXLogicalRep x = true then
    .ok { support := x, valid := h }
  else if !c.valid then
    .error .invalidCSS
  else if !(decide (x.length = c.n)) then
    .error (.wrongLength x.length c.n)
  else
    match c.firstAnticommutingZCheck? x with
    | some i => .error (.notCycle i)
    | none =>
        if c.xBoundary x then
          .error (.isBoundary ((solveInSpan? c.hx x).getD []))
        else
          .error .invalidCSS

/-- The dual logical-Pauli coordinate data.  `zBasis[i]` names the logical Z for
    qubit `i`; `xDualBasis[i]` must pair with it by `x_i · z_j = δᵢⱼ`. -/
structure LogicalPauliBasisSpec where
  zBasis : BoolMat
  xDualBasis : BoolMat
  deriving Repr, Inhabited

def LogicalPauliBasisSpec.toCSSLogicalBasis (spec : LogicalPauliBasisSpec) :
    CSSLogicalBasis :=
  { lx := spec.xDualBasis, lz := spec.zBasis }

/-- Bool-level no-duplicates check for source-level logical names. -/
def noDuplicateStrings : List String -> Bool
  | [] => true
  | x :: xs => !(xs.contains x) && noDuplicateStrings xs

def firstDuplicateString? : List String -> Option String
  | [] => none
  | x :: xs => if xs.contains x then some x else firstDuplicateString? xs

/-- One named logical-Z candidate.  This is the Z-only user-facing layer. -/
structure LogicalZSpec where
  name : String
  z : BoolVec
  deriving Repr, Inhabited

/-- A Z-only logical basis specification: enough to name computational-basis
    observables, but not yet enough to define full X/Z Pauli coordinates. -/
structure LogicalZBasisSpec where
  reps : List LogicalZSpec
  deriving Repr, Inhabited

def LogicalZBasisSpec.names (spec : LogicalZBasisSpec) : List String :=
  spec.reps.map (·.name)

def LogicalZBasisSpec.zBasis (spec : LogicalZBasisSpec) : BoolMat :=
  spec.reps.map (·.z)

structure CheckedLogicalZBasis where
  code : CSSCode
  names : List String
  zBasis : BoolMat
  valid : code.logicalZBasisShapeAndCycle zBasis = true

structure CheckedLogicalPauliBasis where
  code : CSSCode
  names : List String
  zBasis : BoolMat
  xDualBasis : BoolMat
  valid : CSSLogicalBasis.valid code { lx := xDualBasis, lz := zBasis } = true

theorem CheckedLogicalPauliBasis.valid_css (basis : CheckedLogicalPauliBasis) :
    CSSLogicalBasis.valid basis.code { lx := basis.xDualBasis, lz := basis.zBasis } = true :=
  basis.valid

def CheckedLogicalPauliBasis.zCoordinates (basis : CheckedLogicalPauliBasis) (z : BoolVec) :
    BoolVec :=
  basis.xDualBasis.map (fun x => dotBit x z)

def CheckedLogicalPauliBasis.xCoordinates (basis : CheckedLogicalPauliBasis) (x : BoolVec) :
    BoolVec :=
  basis.zBasis.map (fun z => dotBit x z)

def CheckedLogicalPauliBasis.zRepresentative
    (basis : CheckedLogicalPauliBasis) (coeffs : BoolVec) : BoolVec :=
  xorRowsByCoeffWithWidth basis.code.n coeffs basis.zBasis

def CheckedLogicalPauliBasis.xRepresentative
    (basis : CheckedLogicalPauliBasis) (coeffs : BoolVec) : BoolVec :=
  xorRowsByCoeffWithWidth basis.code.n coeffs basis.xDualBasis

def CheckedLogicalPauliBasis.zCoordinateClassOk
    (basis : CheckedLogicalPauliBasis) (z : BoolVec) : Bool :=
  basis.code.zCycle z &&
  basis.code.sameZLogicalClass z (basis.zRepresentative (basis.zCoordinates z))

def CheckedLogicalPauliBasis.xCoordinateClassOk
    (basis : CheckedLogicalPauliBasis) (x : BoolVec) : Bool :=
  basis.code.xCycle x &&
  basis.code.sameXLogicalClass x (basis.xRepresentative (basis.xCoordinates x))

def LogicalZBasisSpec.valid (c : CSSCode) (spec : LogicalZBasisSpec) : Bool :=
  decide (spec.names.length = c.k) &&
  noDuplicateStrings spec.names &&
  c.logicalZBasisShapeAndCycle spec.zBasis

private def firstZRepError? (c : CSSCode) (zs : BoolMat) : Option (Nat × LogicalRepError) :=
  firstIndexAux
    (fun z => match c.checkZLogicalRep? z with | .error _ => true | .ok _ => false)
    zs 0 |>.map
    (fun i =>
      match c.checkZLogicalRep? (zs.getD i []) with
      | .error e => (i, e)
      | .ok _ => (i, .invalidCSS))

private def firstXRepError? (c : CSSCode) (xs : BoolMat) : Option (Nat × LogicalRepError) :=
  firstIndexAux
    (fun x => match c.checkXLogicalRep? x with | .error _ => true | .ok _ => false)
    xs 0 |>.map
    (fun i =>
      match c.checkXLogicalRep? (xs.getD i []) with
      | .error e => (i, e)
      | .ok _ => (i, .invalidCSS))

private def splitAtAux {α : Type} : Nat -> List α -> List α -> List α × List α
  | _, [], acc => (acc.reverse, [])
  | 0, xs, acc => (acc.reverse, xs)
  | n + 1, x :: xs, acc => splitAtAux n xs (x :: acc)

private def takeList {α : Type} (n : Nat) (xs : List α) : List α := (splitAtAux n xs []).1
private def dropList {α : Type} (n : Nat) (xs : List α) : List α := (splitAtAux n xs []).2

private def padTo (n : Nat) (xs : BoolVec) : BoolVec :=
  xs ++ List.replicate (n - xs.length) false

private def dependencyWitnessAux
    (stab : BoolMat) (total : Nat) : Nat -> BoolMat -> BoolMat ->
    Option (BoolVec × BoolVec)
  | _, [], _ => none
  | i, row :: rest, prev =>
      match solveInSpan? (stab ++ prev) row with
      | some coeffs =>
          let stabCoeffs := takeList stab.length coeffs
          let prevCoeffs := takeList i (dropList stab.length coeffs)
          let basisCoeffs :=
            padTo total (prevCoeffs ++ [true] ++ List.replicate (total - (i + 1)) false)
          some (basisCoeffs, stabCoeffs)
      | none => dependencyWitnessAux stab total (i + 1) rest (prev ++ [row])

def dependentModuloWitness? (stab rows : BoolMat) : Option (BoolVec × BoolVec) :=
  dependencyWitnessAux stab rows.length 0 rows []

def mkLogicalZBasis? (cc : CheckedCSSCode) (spec : LogicalZBasisSpec) :
    Except LogicalBasisError CheckedLogicalZBasis :=
  let c := cc.code
  if !(decide (spec.names.length = c.k)) then
    .error (.nameCountMismatch spec.names.length c.k)
  else
    match firstDuplicateString? spec.names with
    | some name => .error (.duplicateName name)
    | none =>
        if !(decide (spec.zBasis.length = c.k)) then
          .error (.zBasisWrongLength spec.zBasis.length c.k)
        else
          match firstZRepError? c spec.zBasis with
          | some (i, err) => .error (.zNotLogical i err)
          | none =>
              if !independentModulo c.hz spec.zBasis then
                match dependentModuloWitness? c.hz spec.zBasis with
                | some (basisCoeffs, stabCoeffs) =>
                    .error (.zDependentModuloStabilizers basisCoeffs stabCoeffs)
                | none => .error (.zDependentModuloStabilizers [] [])
              else if h : c.logicalZBasisShapeAndCycle spec.zBasis = true then
                .ok { code := c, names := spec.names, zBasis := spec.zBasis, valid := h }
              else
                .error .invalidCSS

/-- User-facing logical-qubit indexing for a CSS code.

    `names[i]` names logical qubit `i`; `basis.lz[i]` is its logical Z and
    `basis.lx[i]` is its paired logical X. -/
structure LogicalIndexSpec where
  names : List String
  pauliBasis : LogicalPauliBasisSpec
  deriving Repr, Inhabited

def LogicalIndexSpec.basis (spec : LogicalIndexSpec) : CSSLogicalBasis :=
  spec.pauliBasis.toCSSLogicalBasis

def CheckedLogicalPauliBasis.toLogicalIndexSpec (basis : CheckedLogicalPauliBasis) :
    LogicalIndexSpec :=
  { names := basis.names,
    pauliBasis := { zBasis := basis.zBasis, xDualBasis := basis.xDualBasis } }

/-- Preferred per-logical-qubit full X/Z specification.  This avoids parallel
    name/Z/X arrays in user-facing code. -/
structure LogicalQubitSpec where
  name : String
  z : BoolVec
  x : BoolVec
  deriving Repr, Inhabited

def LogicalIndexSpec.ofQubits (qubits : List LogicalQubitSpec) : LogicalIndexSpec :=
  { names := qubits.map (·.name),
    pauliBasis :=
      { zBasis := qubits.map (·.z),
        xDualBasis := qubits.map (·.x) } }

def LogicalIndexSpec.namesValid (c : CSSCode) (spec : LogicalIndexSpec) : Bool :=
  decide (spec.names.length = c.k) && noDuplicateStrings spec.names

/-- Full source-boundary check: names have exactly length `k`, names are unique,
    the named Z rows are nontrivial cycles modulo boundaries, and the dual X rows
    complete a valid Pauli coordinate basis. -/
def LogicalIndexSpec.valid (c : CSSCode) (spec : LogicalIndexSpec) : Bool :=
  spec.namesValid c &&
  c.logicalZBasisShapeAndCycle spec.pauliBasis.zBasis &&
  c.logicalXBasisShapeAndCycle spec.pauliBasis.xDualBasis &&
  CSSLogicalBasis.valid c spec.basis

/-- A user-declared logical index after validation. -/
structure CheckedLogicalIndex where
  code       : CSSCode
  names      : List String
  basis      : CSSLogicalBasis
  namesValid : (decide (names.length = code.k) && noDuplicateStrings names) = true
  basisValid : CSSLogicalBasis.valid code basis = true

/-- Forget the user names, keeping the checked basis. -/
def CheckedLogicalIndex.toCheckedLogicalBasis (idx : CheckedLogicalIndex) :
    CheckedLogicalBasis :=
  { code := idx.code, basis := idx.basis, valid := idx.basisValid }

def CheckedLogicalIndex.toCheckedLogicalPauliBasis (idx : CheckedLogicalIndex) :
    CheckedLogicalPauliBasis :=
  { code := idx.code,
    names := idx.names,
    zBasis := idx.basis.lz,
    xDualBasis := idx.basis.lx,
    valid := idx.basisValid }

private def indexOfAux (needle : String) : List String -> Nat -> Option Nat
  | [], _ => none
  | x :: xs, i => if x == needle then some i else indexOfAux needle xs (i + 1)

/-- Resolve a source-level logical name to the row/index used by `Logical.LQubit`. -/
def CheckedLogicalIndex.indexOf? (idx : CheckedLogicalIndex) (name : String) : Option Nat :=
  indexOfAux name idx.names 0

private def firstBadDualPairInRow?
    (x : BoolVec) (zs : BoolMat) (i : Nat) : Nat -> Option (Nat × Nat × Bool × Bool)
  | j =>
      match zs with
      | [] => none
      | z :: rest =>
          let got := dotBit x z
          let expected := decide (i = j)
          if got == expected then
            firstBadDualPairInRow? x rest i (j + 1)
          else
            some (i, j, got, expected)

private def firstBadDualPair?
    (xs zs : BoolMat) : Nat -> Option (Nat × Nat × Bool × Bool)
  | i =>
      match xs with
      | [] => none
      | x :: rest =>
          match firstBadDualPairInRow? x zs i 0 with
          | some bad => some bad
          | none => firstBadDualPair? rest zs (i + 1)

def mkLogicalIndexDetailed? (cc : CheckedCSSCode) (spec : LogicalIndexSpec) :
    Except LogicalBasisError CheckedLogicalIndex :=
  let c := cc.code
  if !(decide (spec.names.length = c.k)) then
    .error (.nameCountMismatch spec.names.length c.k)
  else
    match firstDuplicateString? spec.names with
    | some name => .error (.duplicateName name)
    | none =>
        if !(decide (spec.pauliBasis.zBasis.length = c.k)) then
          .error (.zBasisWrongLength spec.pauliBasis.zBasis.length c.k)
        else if !(decide (spec.pauliBasis.xDualBasis.length = c.k)) then
          .error (.xBasisWrongLength spec.pauliBasis.xDualBasis.length c.k)
        else
          match firstZRepError? c spec.pauliBasis.zBasis with
          | some (i, err) => .error (.zNotLogical i err)
          | none =>
          match firstXRepError? c spec.pauliBasis.xDualBasis with
          | some (i, err) => .error (.xNotLogical i err)
          | none =>
              if !independentModulo c.hz spec.pauliBasis.zBasis then
                match dependentModuloWitness? c.hz spec.pauliBasis.zBasis with
                | some (basisCoeffs, stabCoeffs) =>
                    .error (.zDependentModuloStabilizers basisCoeffs stabCoeffs)
                | none => .error (.zDependentModuloStabilizers [] [])
              else if !independentModulo c.hx spec.pauliBasis.xDualBasis then
                match dependentModuloWitness? c.hx spec.pauliBasis.xDualBasis with
                | some (basisCoeffs, stabCoeffs) =>
                    .error (.xDependentModuloStabilizers basisCoeffs stabCoeffs)
                | none => .error (.xDependentModuloStabilizers [] [])
              else
                match firstBadDualPair? spec.pauliBasis.xDualBasis spec.pauliBasis.zBasis 0 with
                | some (i, j, got, expected) => .error (.badDualPairing i j got expected)
                | none =>
                    if hNames : spec.namesValid c = true then
                      if hBasis : CSSLogicalBasis.valid c spec.basis = true then
                        .ok { code := c, names := spec.names, basis := spec.basis,
                              namesValid := hNames, basisValid := hBasis }
                      else
                        .error .invalidCSS
                    else
                      .error (.nameCountMismatch spec.names.length c.k)

/-- Validate a user-specified logical index against an already-checked CSS code. -/
def mkLogicalIndex? (cc : CheckedCSSCode) (spec : LogicalIndexSpec) :
    Except ChainQError CheckedLogicalIndex :=
  match mkLogicalIndexDetailed? cc spec with
  | .ok idx => .ok idx
  | .error err => .error (.logicalDerivationFailed err.message)

def mkLogicalIndexFromQubits? (cc : CheckedCSSCode) (qubits : List LogicalQubitSpec) :
    Except LogicalBasisError CheckedLogicalIndex :=
  mkLogicalIndexDetailed? cc (LogicalIndexSpec.ofQubits qubits)

/-- Complete a checked Z-basis with some dual X-basis and return the checked
    logical-index object.  This guarantees logical correctness, but it does not
    optimize weight, sparsity, geometry, or qLDPC locality. -/
private def completeLogicalIndex? (cc : CheckedCSSCode) (zb : CheckedLogicalZBasis) :
    Except LogicalBasisError CheckedLogicalIndex :=
  let c := cc.code
  match quotientBasis? c.hx (kernelBasis c.hz c.n) with
  | none => .error .invalidCSS
  | some xCands =>
      let pairing := gemmT xCands zb.zBasis
      match gf2Inv? pairing c.k with
      | none => .error (.badDualPairing 0 0 false true)
      | some pinv =>
          let xDual := matMul pinv xCands c.n
          let spec : LogicalIndexSpec :=
            { names := zb.names,
              pauliBasis := { zBasis := zb.zBasis, xDualBasis := xDual } }
          match mkLogicalIndexDetailed? cc spec with
          | .ok idx => .ok idx
          | .error err => .error err

/-- Complete a checked Z-basis and return a proof-carrying Pauli-basis wrapper.
    Prefer this API in protocol checkers; it carries the `CSSLogicalBasis.valid`
    certificate instead of returning naked Boolean vectors. -/
def completeCheckedLogicalPauliBasis? (cc : CheckedCSSCode) (zb : CheckedLogicalZBasis) :
    Except LogicalBasisError CheckedLogicalPauliBasis :=
  match completeLogicalIndex? cc zb with
  | .ok idx => .ok idx.toCheckedLogicalPauliBasis
  | .error err => .error err

theorem completeCheckedLogicalPauliBasis?_sound
    {cc : CheckedCSSCode} {zb : CheckedLogicalZBasis} {basis : CheckedLogicalPauliBasis}
    (_h : completeCheckedLogicalPauliBasis? cc zb = .ok basis) :
    CSSLogicalBasis.valid basis.code { lx := basis.xDualBasis, lz := basis.zBasis } = true :=
  basis.valid

/-- Compatibility API returning the raw source-level spec.  New code should prefer
    `completeCheckedLogicalPauliBasis?` when it needs a proof-carrying result. -/
def completeLogicalPauliBasis? (cc : CheckedCSSCode) (zb : CheckedLogicalZBasis) :
    Except LogicalBasisError LogicalIndexSpec :=
  match completeCheckedLogicalPauliBasis? cc zb with
  | .ok basis => .ok basis.toLogicalIndexSpec
  | .error err => .error err

/-- Same implementation as `completeLogicalPauliBasis?`, with a name that makes
    the "any valid dual, not locality-preserving" contract explicit. -/
def completeAnyLogicalPauliBasis? (cc : CheckedCSSCode) (zb : CheckedLogicalZBasis) :
    Except LogicalBasisError LogicalIndexSpec :=
  completeLogicalPauliBasis? cc zb

/-! ## Small executable checks. -/

def bareQubitIndexSpec : LogicalIndexSpec :=
  { names := ["data"],
    pauliBasis := { zBasis := [[true]], xDualBasis := [[true]] } }

example : isOk (mkLogicalIndex? ⟨bareQubit, by decide⟩ bareQubitIndexSpec) = true := by decide

example :
    (match mkLogicalIndex? ⟨bareQubit, by decide⟩ bareQubitIndexSpec with
     | .ok idx => idx.indexOf? "data" == some 0 && idx.indexOf? "anc" == none
     | .error _ => false) = true := by decide

def badBareQubitIndexSpec : LogicalIndexSpec :=
  { names := ["data"],
    pauliBasis := { zBasis := [[false]], xDualBasis := [[true]] } }

example : isOk (mkLogicalIndex? ⟨bareQubit, by decide⟩ badBareQubitIndexSpec) = false := by decide

def bareTwoQubit : CSSCode := { n := 2, hx := [], hz := [] }

def bareTwoQubitBasis : CSSLogicalBasis :=
  { lx := [[true, false], [false, true]],
    lz := [[true, false], [false, true]] }

def bareTwoQubitIndexSpec : LogicalIndexSpec :=
  { names := ["left", "right"],
    pauliBasis := { zBasis := bareTwoQubitBasis.lz, xDualBasis := bareTwoQubitBasis.lx } }

def duplicateBareTwoIndexSpec : LogicalIndexSpec :=
  { names := ["q", "q"],
    pauliBasis := { zBasis := bareTwoQubitBasis.lz, xDualBasis := bareTwoQubitBasis.lx } }

example : CSSLogicalBasis.valid bareTwoQubit bareTwoQubitBasis = true := by decide
example : isOk (mkLogicalIndex? ⟨bareTwoQubit, by decide⟩ bareTwoQubitIndexSpec) = true := by decide
example :
    (match mkLogicalIndex? ⟨bareTwoQubit, by decide⟩ bareTwoQubitIndexSpec with
     | .ok idx => idx.indexOf? "left" == some 0 && idx.indexOf? "right" == some 1
     | .error _ => false) = true := by decide
example : isOk (mkLogicalIndex? ⟨bareTwoQubit, by decide⟩ duplicateBareTwoIndexSpec) = false := by decide

/-! ## Toy lifted-product logical Z example from the homology definition. -/

def ones (n : Nat) : BoolVec := List.replicate n true
def zeros (n : Nat) : BoolVec := List.replicate n false
def unitVec (n i : Nat) : BoolVec := (List.range n).map (fun j => decide (j = i))

/-- The abelian LP toy model with `A = B = 1 + x`: `Hx = [M M]`,
    `Hz = [Mᵀ Mᵀ]`, where `M = I + P`. -/
def toyLPCSS (L : Nat) : CSSCode :=
  let M := circulant L [0, 1]
  { n := 2 * L,
    hx := M.map (fun r => r ++ r),
    hz := (transpose M L).map (fun r => r ++ r) }

def toyLPCSS? (L : Nat) : Except String CSSCode :=
  if 2 ≤ L then .ok (toyLPCSS L) else .error "toy LP code requires L >= 2"

def toyLPZ1 (L : Nat) : BoolVec := ones L ++ zeros L
def toyLPZ2 (L : Nat) : BoolVec := unitVec L 0 ++ unitVec L 0
def toyLPX1 (L : Nat) : BoolVec := unitVec L 0 ++ unitVec L 0
def toyLPX2 (L : Nat) : BoolVec := zeros L ++ ones L

def toyLPIndexSpec (L : Nat) : LogicalIndexSpec :=
  { names := ["global_a", "bridge_ab"],
    pauliBasis :=
      { zBasis := [toyLPZ1 L, toyLPZ2 L],
        xDualBasis := [toyLPX1 L, toyLPX2 L] } }

example : isOk (toyLPCSS? 0) = false := by decide
example : isOk (toyLPCSS? 1) = false := by decide
example : isOk (toyLPCSS? 2) = true := by decide
example : (toyLPCSS 2).k = 2 := by decide
example : (toyLPCSS 3).valid = true := by decide
example : (toyLPCSS 3).k = 2 := by decide
example : (toyLPCSS 4).k = 2 := by decide
example : (toyLPCSS 5).k = 2 := by decide
example : (toyLPCSS 2).logicalZ (toyLPZ1 2) = true := by decide
example : (toyLPCSS 3).logicalZ (toyLPZ1 3) = true := by decide
example : (toyLPCSS 4).logicalZ (toyLPZ1 4) = true := by decide
example : (toyLPCSS 5).logicalZ (toyLPZ1 5) = true := by decide
example : (toyLPCSS 2).logicalZ (toyLPZ2 2) = true := by decide
example : (toyLPCSS 3).logicalZ (toyLPZ2 3) = true := by decide
example : (toyLPCSS 4).logicalZ (toyLPZ2 4) = true := by decide
example : (toyLPCSS 5).logicalZ (toyLPZ2 5) = true := by decide
example : (toyLPCSS 3).logicalX (toyLPX1 3) = true := by decide
example : (toyLPCSS 3).logicalX (toyLPX2 3) = true := by decide
example : isOk (mkLogicalIndex? ⟨toyLPCSS 3, by decide⟩ (toyLPIndexSpec 3)) = true := by decide

example : isOk ((toyLPCSS 3).checkZLogicalRep? (toyLPZ1 3)) = true := by decide
example :
    (match (toyLPCSS 3).checkZLogicalRep? (toyLPZ1 3 ++ [true]) with
     | .error (.wrongLength 7 6) => true
     | _ => false) = true := by decide
example :
    (match (toyLPCSS 3).checkZLogicalRep? (unitVec 3 0 ++ zeros 3) with
     | .error (.notCycle _) => true
     | _ => false) = true := by decide
example :
    (match (toyLPCSS 3).checkZLogicalRep? ((toyLPCSS 3).hz.getD 0 []) with
     | .error (.isBoundary coeffs) =>
         xorRowsByCoeffWithWidth 6 coeffs (toyLPCSS 3).hz == ((toyLPCSS 3).hz.getD 0 [])
     | _ => false) = true := by decide

example : (toyLPCSS 3).logicalZ (zeros 6) = false := by decide
example : (toyLPCSS 3).logicalZ (toyLPZ1 3 ++ [true]) = false := by decide
example : (toyLPCSS 3).logicalZ ((toyLPCSS 3).hz.getD 0 []) = false := by decide
example : (toyLPCSS 3).logicalZ (unitVec 3 0 ++ zeros 3) = false := by decide

def toyLPZOnlySpec : LogicalZBasisSpec :=
  { reps :=
      [ { name := "global_a", z := toyLPZ1 3 },
        { name := "bridge_ab", z := toyLPZ2 3 } ] }

example : isOk (mkLogicalZBasis? ⟨toyLPCSS 3, by decide⟩ toyLPZOnlySpec) = true := by decide
example :
    (match mkLogicalZBasis? ⟨toyLPCSS 3, by decide⟩ toyLPZOnlySpec with
     | .ok zb => isOk (completeLogicalPauliBasis? ⟨toyLPCSS 3, by decide⟩ zb)
     | .error _ => false) = true := by decide
example :
    (match mkLogicalZBasis? ⟨toyLPCSS 3, by decide⟩ toyLPZOnlySpec with
     | .ok zb => isOk (completeCheckedLogicalPauliBasis? ⟨toyLPCSS 3, by decide⟩ zb)
     | .error _ => false) = true := by decide
example :
    (match mkLogicalZBasis? ⟨toyLPCSS 3, by decide⟩ toyLPZOnlySpec with
     | .ok zb =>
       match completeLogicalPauliBasis? ⟨toyLPCSS 3, by decide⟩ zb with
       | .ok spec =>
           (toyLPCSS 3).logicalXBasisShapeAndCycle spec.pauliBasis.xDualBasis &&
           (toyLPCSS 3).logicalZBasisShapeAndCycle spec.pauliBasis.zBasis &&
           decide (gemmT spec.pauliBasis.xDualBasis spec.pauliBasis.zBasis = identMat 2)
        | .error _ => false
     | .error _ => false) = true := by decide
example :
    (match mkLogicalZBasis? ⟨toyLPCSS 3, by decide⟩ toyLPZOnlySpec with
     | .ok zb =>
       match completeCheckedLogicalPauliBasis? ⟨toyLPCSS 3, by decide⟩ zb with
       | .ok basis =>
           (toyLPCSS 3).logicalXBasisShapeAndCycle basis.xDualBasis &&
           (toyLPCSS 3).logicalZBasisShapeAndCycle basis.zBasis &&
           decide (gemmT basis.xDualBasis basis.zBasis = identMat 2) &&
           basis.zCoordinateClassOk (toyLPZ1 3) &&
           basis.zCoordinateClassOk (vecXor (toyLPZ1 3) (toyLPZ2 3))
       | .error _ => false
     | .error _ => false) = true := by decide

def toyLPQubitSpecs : List LogicalQubitSpec :=
  [ { name := "global_a", z := toyLPZ1 3, x := toyLPX1 3 },
    { name := "bridge_ab", z := toyLPZ2 3, x := toyLPX2 3 } ]

example : isOk (mkLogicalIndexFromQubits? ⟨toyLPCSS 3, by decide⟩ toyLPQubitSpecs) = true := by decide
example :
    (match mkLogicalIndexFromQubits? ⟨toyLPCSS 3, by decide⟩ toyLPQubitSpecs with
     | .ok idx =>
         let basis := idx.toCheckedLogicalPauliBasis
         basis.zCoordinateClassOk (toyLPZ1 3) &&
         basis.zCoordinateClassOk (toyLPZ2 3) &&
         basis.zCoordinateClassOk (vecXor (toyLPZ1 3) (toyLPZ2 3)) &&
         basis.xCoordinateClassOk (toyLPX1 3) &&
         basis.xCoordinateClassOk (toyLPX2 3)
     | .error _ => false) = true := by decide

def dupZSpec : LogicalIndexSpec :=
  { names := ["a", "b"],
    pauliBasis :=
      { zBasis := [toyLPZ1 3, toyLPZ1 3],
        xDualBasis := [toyLPX1 3, toyLPX2 3] } }

example : isOk (mkLogicalIndex? ⟨toyLPCSS 3, by decide⟩ dupZSpec) = false := by decide
example :
    (match mkLogicalIndexDetailed? ⟨toyLPCSS 3, by decide⟩ dupZSpec with
     | .error (.zDependentModuloStabilizers basisCoeffs stabCoeffs) =>
          basisCoeffs.length == 2 &&
          stabCoeffs.length == (toyLPCSS 3).hz.length &&
          basisCoeffs.any (fun b => b) &&
          (xorRowsByCoeffWithWidth 6 basisCoeffs dupZSpec.pauliBasis.zBasis ==
            xorRowsByCoeffWithWidth 6 stabCoeffs (toyLPCSS 3).hz)
     | _ => false) = true := by decide

def partialSpec : LogicalIndexSpec :=
  { names := ["a"],
    pauliBasis :=
      { zBasis := [toyLPZ1 3],
        xDualBasis := [toyLPX1 3] } }

example : isOk (mkLogicalIndex? ⟨toyLPCSS 3, by decide⟩ partialSpec) = false := by decide
example :
    (match mkLogicalIndexDetailed? ⟨toyLPCSS 3, by decide⟩ partialSpec with
     | .error (.nameCountMismatch 1 2) => true
     | _ => false) = true := by decide

def badNameCountSpec : LogicalIndexSpec :=
  { names := ["only_one_name"],
    pauliBasis :=
      { zBasis := [toyLPZ1 3, toyLPZ2 3],
        xDualBasis := [toyLPX1 3, toyLPX2 3] } }

example : isOk (mkLogicalIndex? ⟨toyLPCSS 3, by decide⟩ badNameCountSpec) = false := by decide

def dupNamesSpec : LogicalIndexSpec :=
  { names := ["same", "same"],
    pauliBasis :=
      { zBasis := [toyLPZ1 3, toyLPZ2 3],
        xDualBasis := [toyLPX1 3, toyLPX2 3] } }

example : isOk (mkLogicalIndex? ⟨toyLPCSS 3, by decide⟩ dupNamesSpec) = false := by decide
example :
    (match mkLogicalIndexDetailed? ⟨toyLPCSS 3, by decide⟩ dupNamesSpec with
     | .error (.duplicateName "same") => true
     | _ => false) = true := by decide

def badDualSpec : LogicalIndexSpec :=
  { names := ["global_a", "bridge_ab"],
    pauliBasis :=
      { zBasis := [toyLPZ1 3, toyLPZ2 3],
        xDualBasis := [toyLPX1 3, toyLPX1 3] } }

example : isOk (mkLogicalIndex? ⟨toyLPCSS 3, by decide⟩ badDualSpec) = false := by decide

def swappedDualSpec : LogicalIndexSpec :=
  { names := ["global_a", "bridge_ab"],
    pauliBasis :=
      { zBasis := [toyLPZ1 3, toyLPZ2 3],
        xDualBasis := [toyLPX2 3, toyLPX1 3] } }

example : (toyLPCSS 3).logicalXBasisShapeAndCycle swappedDualSpec.pauliBasis.xDualBasis = true := by decide
example : isOk (mkLogicalIndex? ⟨toyLPCSS 3, by decide⟩ swappedDualSpec) = false := by decide
example :
    (match mkLogicalIndexDetailed? ⟨toyLPCSS 3, by decide⟩ swappedDualSpec with
     | .error (.badDualPairing 0 0 false true) => true
     | _ => false) = true := by decide

def badNonCycleX1 : BoolVec := unitVec 3 1 ++ zeros 3

example : (toyLPCSS 3).logicalX badNonCycleX1 = false := by decide

def badXCycleSpec : LogicalIndexSpec :=
  { names := ["global_a", "bridge_ab"],
    pauliBasis :=
      { zBasis := [toyLPZ1 3, toyLPZ2 3],
        xDualBasis := [badNonCycleX1, toyLPX2 3] } }

example : isOk (mkLogicalIndex? ⟨toyLPCSS 3, by decide⟩ badXCycleSpec) = false := by decide
example :
    (match mkLogicalIndexDetailed? ⟨toyLPCSS 3, by decide⟩ badXCycleSpec with
     | .error (.xNotLogical 0 (.notCycle _)) => true
     | _ => false) = true := by decide

def toyLPZ1PlusStab0 : BoolVec := vecXor (toyLPZ1 3) ((toyLPCSS 3).hz.getD 0 [])

example : (toyLPCSS 3).logicalZ toyLPZ1PlusStab0 = true := by decide

def duplicateCosetZSpec : LogicalIndexSpec :=
  { names := ["global_a", "same_coset"],
    pauliBasis :=
      { zBasis := [toyLPZ1 3, toyLPZ1PlusStab0],
        xDualBasis := [toyLPX1 3, toyLPX2 3] } }

example : isOk (mkLogicalIndex? ⟨toyLPCSS 3, by decide⟩ duplicateCosetZSpec) = false := by decide
example :
    (match mkLogicalIndexDetailed? ⟨toyLPCSS 3, by decide⟩ duplicateCosetZSpec with
     | .error (.zDependentModuloStabilizers basisCoeffs stabCoeffs) =>
          basisCoeffs.length == 2 &&
          stabCoeffs.length == (toyLPCSS 3).hz.length &&
          basisCoeffs.any (fun b => b) &&
          (xorRowsByCoeffWithWidth 6 basisCoeffs duplicateCosetZSpec.pauliBasis.zBasis ==
            xorRowsByCoeffWithWidth 6 stabCoeffs (toyLPCSS 3).hz)
     | _ => false) = true := by decide

def badZOnlyWrongLength : LogicalZBasisSpec :=
  { reps :=
      [ { name := "global_a", z := toyLPZ1 3 ++ [true] },
        { name := "bridge_ab", z := toyLPZ2 3 } ] }

example :
    (match mkLogicalZBasis? ⟨toyLPCSS 3, by decide⟩ badZOnlyWrongLength with
     | .error (.zNotLogical 0 (.wrongLength 7 6)) => true
     | _ => false) = true := by decide

def badZOnlyBoundary : LogicalZBasisSpec :=
  { reps :=
      [ { name := "stab", z := (toyLPCSS 3).hz.getD 0 [] },
        { name := "bridge_ab", z := toyLPZ2 3 } ] }

example :
    (match mkLogicalZBasis? ⟨toyLPCSS 3, by decide⟩ badZOnlyBoundary with
     | .error (.zNotLogical 0 (.isBoundary coeffs)) =>
         xorRowsByCoeffWithWidth 6 coeffs (toyLPCSS 3).hz == ((toyLPCSS 3).hz.getD 0 [])
     | _ => false) = true := by decide

def badZOnlyDuplicateCoset : LogicalZBasisSpec :=
  { reps :=
      [ { name := "global_a", z := toyLPZ1 3 },
        { name := "same_coset", z := toyLPZ1PlusStab0 } ] }

example :
    (match mkLogicalZBasis? ⟨toyLPCSS 3, by decide⟩ badZOnlyDuplicateCoset with
     | .error (.zDependentModuloStabilizers basisCoeffs stabCoeffs) =>
          basisCoeffs.length == 2 &&
          stabCoeffs.length == (toyLPCSS 3).hz.length &&
          basisCoeffs.any (fun b => b) &&
          (xorRowsByCoeffWithWidth 6 basisCoeffs badZOnlyDuplicateCoset.zBasis ==
            xorRowsByCoeffWithWidth 6 stabCoeffs (toyLPCSS 3).hz)
     | _ => false) = true := by decide

end ChainQ
