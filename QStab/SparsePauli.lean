/-
  QStab.SparsePauli — an EXPLICIT, indexed sparse physical Pauli product, and a CHECKED
  densification to `QStab.PauliString`.

  `QStab.PauliString := List Pauli` is DENSE: list position = physical qubit index, so
  `X[1]X[3]` on 4 qubits must be written `IXIX`, NOT `XX`.  That is easy to misread.  A
  `SparsePauli` lists only the non-identity factors as `(physical qubit, Pauli)` pairs, so
  the same operator is the unambiguous `[(1, X), (3, X)]`.

  This is the PREFERRED human-facing way to write a physical Pauli product.  It does NOT
  replace the dense representation — `toDense?` is a SAFE ADAPTER that builds the dense
  string under a declared device size, REFUSING (never silently identity-defaulting) an
  empty / identity-only / duplicate-qubit / out-of-range measurement.

  Mathlib-free.
-/
import QStab.Syntax

namespace QStab
open Physical

/-- A SPARSE physical Pauli product: `(physical qubit, non-identity Pauli)` factors.
    Sparse (unlike the dense `PauliString`) so the physical indexing is explicit. -/
abbrev SparsePauli := List (Physical.PQubit × Physical.Pauli)

/-- A `Bool` no-duplicates check over physical qubit indices (Mathlib-free). -/
private def nodupPQ : List Physical.PQubit → Bool
  | []        => true
  | q :: rest => !rest.contains q && nodupPQ rest

/-- No identity factor (a sparse Pauli lists only non-`I` letters). -/
def SparsePauli.noIdentity (P : SparsePauli) : Bool := P.all (fun f => decide (f.2 ≠ Pauli.I))

/-- No duplicate qubit. -/
def SparsePauli.nodupQubits (P : SparsePauli) : Bool := nodupPQ (P.map Prod.fst)

/-- Every factor addresses a physical qubit `< n` (in range for an `n`-qubit device). -/
def SparsePauli.inRange (n : Nat) (P : SparsePauli) : Bool := P.all (fun f => decide (f.1 < n))

/-- WELL-FORMED sparse Pauli: no identity factor, no duplicate qubit. -/
def SparsePauli.wf (P : SparsePauli) : Bool := P.noIdentity && P.nodupQubits

/-- A well-formed MEASUREMENT operator: `wf` AND non-empty (an empty / identity-only
    measurement is meaningless). -/
def SparsePauli.wfMeas (P : SparsePauli) : Bool := P.wf && !P.isEmpty

/-- The (UNCHECKED) dense form over physical qubits `0 … n-1` (absent qubit ⇒ identity).
    `PRIVATE` (audit fix): this SILENTLY DROPS out-of-range factors
    (`denseOf 4 [(5, X)] = IIII`), so it is a footgun if public.  It is reachable ONLY via
    the CHECKED `toDense?` (below), which gates well-formedness FIRST.  External modules
    must use `toDense?`. -/
private def SparsePauli.denseOf (n : Nat) (P : SparsePauli) : PauliString :=
  (List.range n).map (fun q => ((P.find? (fun f => f.1 == q)).map Prod.snd).getD Pauli.I)

/-- Why a sparse measurement could not densify (machine-readable, never silent). -/
inductive SparsePauliError
  | empty                          -- an empty / identity-only measurement
  | identityFactor                 -- a factor with an `I` letter
  | duplicateQubit                 -- a qubit listed twice
  | outOfRange (qubit bound : Nat) -- a factor qubit ≥ the declared device size
  deriving Repr, DecidableEq

/-- **CHECKED densification of a MEASUREMENT** sparse Pauli to a dense `PauliString` over a
    declared `numQubits`-qubit device.  REJECTS (never silently defaults to identity) an
    empty, identity-bearing, duplicate-qubit, or out-of-range operator. -/
def SparsePauli.toDense? (numQubits : Nat) (P : SparsePauli) :
    Except SparsePauliError PauliString :=
  if P.isEmpty then .error .empty
  else if !P.noIdentity then .error .identityFactor
  else if !P.nodupQubits then .error .duplicateQubit
  else match P.find? (fun f => decide (numQubits ≤ f.1)) with
    | some f => .error (.outOfRange f.1 numQubits)
    | none   => .ok (P.denseOf numQubits)

/-! ## Checked examples. -/

-- `X[1]X[3]` on 4 qubits densifies to `IXIX` (NOT `XX`):
example : (SparsePauli.toDense? 4 [(1, .X), (3, .X)]).toOption = some (ofString "IXIX") := by decide
-- `X[5]` on 6 qubits densifies to `IIIIIX`:
example : (SparsePauli.toDense? 6 [(5, .X)]).toOption = some (ofString "IIIIIX") := by decide
-- a 2-body `ZZ` on 2 qubits is `ZZ`:
example : (SparsePauli.toDense? 2 [(0, .Z), (1, .Z)]).toOption = some (ofString "ZZ") := by decide

-- DUPLICATE qubit is rejected (specific error):
example : (match SparsePauli.toDense? 4 [(0, .X), (0, .Z)] with | .error .duplicateQubit => true | _ => false) = true := by decide
-- an IDENTITY factor is rejected:
example : (match SparsePauli.toDense? 4 [(0, .I)] with | .error .identityFactor => true | _ => false) = true := by decide
-- an EMPTY measurement is rejected:
example : (match SparsePauli.toDense? 4 ([] : SparsePauli) with | .error .empty => true | _ => false) = true := by decide
-- an OUT-OF-RANGE index is rejected (never silently dropped to identity):
example : (match SparsePauli.toDense? 4 [(5, .X)] with | .error (.outOfRange q b) => q == 5 && b == 4 | _ => false) = true := by decide

-- the well-formedness predicates, directly:
example : SparsePauli.wfMeas [(1, .X), (3, .X)] = true := by decide
example : SparsePauli.wfMeas [(0, .X), (0, .Z)] = false := by decide
example : SparsePauli.wfMeas [(0, .I)] = false := by decide
example : SparsePauli.wfMeas ([] : SparsePauli) = false := by decide
example : SparsePauli.inRange 2 [(5, .X)] = false := by decide

end QStab
