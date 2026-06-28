/-
  Compiler.LS.Extract — an HONEST extractability classifier for the downstream
  QStab2QClifford pass.

  `Compiler.QStab2QClifford` (see `Scheme.lean`) realises a physical Pauli measurement
  only via its X/Z extraction schemes — every `extractionSpecOk` arm requires
  `orderedSupportOk P order Pauli.X` or `… Pauli.Z`, i.e. a UNIFORM single-letter X or
  Z check.  A `Y`-support (e.g. the Gidney cultivation `Y`-parity observable) or a
  MIXED X/Z support is NOT lowerable by any current scheme.

  This classifier records that honestly: it does NOT claim QClifford / lattice-surgery
  executability for mixed/Y measurements, it emits an explicit `notExtractable`
  obligation instead.  (We mirror the scheme constraint here rather than import the
  downstream pass, to keep the LS layer independent of QStab2QClifford.)  Mathlib-free.
-/
import Compiler.LS.Check

namespace Compiler.LS
open QStab Physical

/-- The extraction class of a dense physical Pauli string w.r.t. the CURRENT
    QStab2QClifford schemes. -/
inductive ExtractClass
  | uniformX     -- all support letters are `X` (a standard/Shor/Knill/flag X-check)
  | uniformZ     -- all support letters are `Z`
  | mixedOrY     -- contains a `Y`, mixes `X` and `Z`, or is empty — NOT lowerable by current schemes
  deriving DecidableEq, Repr

/-- The non-identity support letters of a dense Pauli string. -/
def supportLetters (P : QStab.PauliString) : List Pauli :=
  P.filter (fun p => decide (p ≠ Pauli.I))

/-- Classify a dense physical Pauli measurement by what the current schemes can extract. -/
def extractClass (P : QStab.PauliString) : ExtractClass :=
  let letters := supportLetters P
  if letters.isEmpty then .mixedOrY                              -- identity: nothing to extract
  else if letters.all (fun p => decide (p = Pauli.X)) then .uniformX
  else if letters.all (fun p => decide (p = Pauli.Z)) then .uniformZ
  else .mixedOrY

/-- Is this physical measurement lowerable by the CURRENT QStab2QClifford extraction
    schemes (which realise only uniform single-letter `X` or `Z` checks)? -/
def extractableByCurrentSchemes? (P : QStab.PauliString) : Bool :=
  match extractClass P with
  | .uniformX | .uniformZ => true
  | .mixedOrY             => false

/-- The DEFERRED obligation for a measurement the current schemes cannot extract
    (`none` when it IS extractable). -/
def extractObligation? (P : QStab.PauliString) : Option Obligation :=
  if extractableByCurrentSchemes? P then none
  else some (.notExtractable P
    "current QStab2QClifford schemes realise only uniform X/Z checks; this measurement has a Y or mixed X/Z support")

/-- Collect the non-extractable obligations of a whole QStab dataflow's measurements,
    DEDUPLICATED (identical non-extractable measurements — e.g. the two cultivation
    `Y`-parity rounds — yield a SINGLE obligation). -/
def extractObligations (df : QStab.Prog) : List Obligation :=
  (df.filterMap (fun st => match st with
    | .prop _ P => extractObligation? P
    | .parity _ => none)).eraseDups

/-! ## Checked examples. -/

-- uniform Z / X checks ARE extractable; identity gaps are fine:
example : extractableByCurrentSchemes? (ofString "ZZ") = true := by decide
example : extractableByCurrentSchemes? (ofString "XX") = true := by decide
example : extractClass (ofString "ZIZ") = .uniformZ := by decide
-- a Y-support (the Gidney cultivation Y-parity observable) is NOT extractable:
example : extractableByCurrentSchemes? (ofString "YYY") = false := by decide
example : extractClass (ofString "YYY") = .mixedOrY := by decide
-- a MIXED X/Z support is NOT extractable:
example : extractableByCurrentSchemes? (ofString "XZ") = false := by decide
-- the obligation is emitted exactly when not extractable:
example : (extractObligation? (ofString "YYY")).isSome = true := by decide
example : (extractObligation? (ofString "ZZ")).isNone = true := by decide

end Compiler.LS
