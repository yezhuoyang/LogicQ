/-
  Physical — the shared PHYSICAL-level vocabulary.

  QStab and QClifford operate on PHYSICAL qubits (the data/ancilla qubits of a
  surface-code patch), as opposed to the logical qubits of PPR/PPM.  This
  module fixes the physical qubit address and the 4-element Pauli alphabet
  (`I, X, Y, Z`) used in dense physical Pauli strings (e.g. `ZZI`).

  Mathlib-free (pure `Nat`/`Char`/`List`).
-/

namespace Physical

/-- A physical qubit index. -/
abbrev PQubit := Nat

/-- A single-qubit Pauli, INCLUDING identity (physical Pauli strings are dense,
    e.g. `ZZI = [Z, Z, I]`). -/
inductive Pauli
  | I | X | Y | Z
  deriving DecidableEq, Repr, Inhabited

/-- Parse a Pauli letter (`'X'`/`'Y'`/`'Z'`, anything else `I`). -/
def Pauli.ofChar : Char → Pauli
  | 'X' => .X | 'Y' => .Y | 'Z' => .Z | _ => .I

/-- Parse a dense physical Pauli string, e.g. `"ZZI" ↦ [Z, Z, I]`. -/
def ofString (s : String) : List Pauli := s.toList.map Pauli.ofChar

example : ofString "ZZI" = [.Z, .Z, .I] := by decide
example : ofString "ZZZ" = [.Z, .Z, .Z] := by decide

end Physical
