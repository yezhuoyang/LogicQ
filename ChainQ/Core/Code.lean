/-
  ChainQ.Code — the CODE-TYPE layer of the ChainQ front-end type
  system: the two "code kinds" a user can declare,

      code … as CSSCode        -- a GF(2) check-matrix pair (hx, hz)
      code … as StabilizerCode  -- explicit Pauli generators (the README's five_qubit)

  Each is a Lean value with a DECIDABLE well-typedness judgement.  This file
  is independent of any compiler; it fixes the syntax (the structures) and
  the static semantics (validity).  Mathlib-free.

  BNF (the core these structures denote):
      CodeKind ::= 'StabilizerCode' | 'CSSCode' | 'CellComplex' 'over' 'Z2'
      StabBody ::= ('n' '=' Nat ';')? 'generators' '{' (Id '=' PauliLit ';')* '}'
                   ('logical_z' '{' (Id '=' PauliLit ';')* '}')?
      PauliLit ::= ('I'|'X'|'Y'|'Z')+
  (the CellComplex kind is elaborated in `ChainComplex.lean`).
-/
import ChainQ.Algebra.GF2

namespace ChainQ
open ChainQ.GF2

/-! ## §1. CSS codes (the check-matrix code kind, and the elaboration target
        of the chain-complex kind). -/

/-- A CSS code as its GF(2) check-matrix pair.  `hx`/`hz` are the X- and
    Z-stabilizer parity matrices, each a `BoolMat` of rows of length `n`. -/
structure CSSCode where
  n  : Nat
  hx : BoolMat
  hz : BoolMat
  deriving Repr, Inhabited

/-- Every check row has length `n`. -/
def CSSCode.wellShaped (c : CSSCode) : Bool :=
  c.hx.all (fun r => decide (r.length = c.n)) &&
  c.hz.all (fun r => decide (r.length = c.n))

/-- The CSS commutation condition `H_X · H_Zᵀ = 0` — the static
    well-typedness obligation of a CSS code. -/
def CSSCode.cssCondition (c : CSSCode) : Bool := orthogonal c.hx c.hz

/-- A CSS code is **well-typed** iff it is well-shaped and CSS-commuting. -/
def CSSCode.valid (c : CSSCode) : Bool := c.wellShaped && c.cssCondition

/-! ## §2. Stabilizer codes (explicit Pauli generators). -/

/-- A single-qubit Pauli. -/
inductive Pauli
  | I | X | Y | Z
  deriving DecidableEq, Repr, Inhabited

/-- Single-qubit Paulis commute iff one is `I` or they are equal. -/
def Pauli.commutes : Pauli → Pauli → Bool
  | .I, _ => true
  | _, .I => true
  | a,  b => decide (a = b)

/-- A Pauli string (tensor product of single-qubit Paulis; `I` is identity). -/
abbrev PauliString := List Pauli

/-- Two Pauli strings commute iff they anticommute on an even number of
    qubits (the standard symplectic test). -/
def commutes (a b : PauliString) : Bool :=
  decide (((a.zip b).countP (fun p => ! Pauli.commutes p.1 p.2)) % 2 = 0)

/-- Parse a `PauliLit` such as `"XZZXI"` into a `PauliString`. -/
def ofString (s : String) : PauliString :=
  s.toList.map (fun c =>
    match c with
    | 'X' => Pauli.X | 'Y' => Pauli.Y | 'Z' => Pauli.Z | _ => Pauli.I)

/-- A stabilizer code: `n` physical qubits and a list of generator strings. -/
structure StabilizerCode where
  n    : Nat
  gens : List PauliString
  deriving Repr, Inhabited

/-- A stabilizer code is **well-typed** iff every generator has length `n`
    and the generators pairwise commute. -/
def StabilizerCode.valid (c : StabilizerCode) : Bool :=
  c.gens.all (fun g => decide (g.length = c.n)) &&
  c.gens.all (fun g => c.gens.all (fun h => commutes g h))

/-- A Pauli string `p` is a logical operator of `c` iff it commutes with
    every stabilizer generator. -/
def StabilizerCode.commutesWithAll (c : StabilizerCode) (p : PauliString) : Bool :=
  c.gens.all (fun g => commutes g p)

/-! ## §3. The README's five-qubit perfect code. -/

/-- `code five_qubit as StabilizerCode { n = 5; generators { … } }`. -/
def fiveQubit : StabilizerCode :=
  { n := 5,
    gens := [ofString "XZZXI", ofString "IXZZX",
             ofString "XIXZZ", ofString "ZXIXZ"] }

/-- The declared logical-Z operator `LZ0 = "ZZZZZ"`. -/
def fiveQubitLZ : PauliString := ofString "ZZZZZ"

-- The five-qubit code is well-typed (its four generators pairwise commute).
example : fiveQubit.valid = true := by decide
-- `ZZZZZ` is a genuine logical operator: it commutes with every stabilizer.
example : fiveQubit.commutesWithAll fiveQubitLZ = true := by decide

end ChainQ
