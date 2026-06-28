/-
  QClifford.Syntax — the final target IR (level L_QClifford).

  A QClifford program is a circuit of PHYSICAL Clifford gates, state
  preparations, computational (`Z`-basis) measurements, classical parity
  assignments, and classically-conditioned Pauli corrections — the executable
  artifact a surface-code device runs.

  PHYSICAL LEVEL: gates act on physical qubits; measurements bind classical
  bits; `ifPauli` applies a feed-forward Pauli conditioned on a measured bit.
  Pure data (Mathlib-free); the operational semantics is in
  `QClifford/Semantics.lean`.

  Standard-PL BNF:

    Gate ::= 'Prep0' q | 'Prep+' q
           | 'H' q | 'S' q | 'X' q | 'Z' q
           | 'CNOT' c t | 'CZ' a b
           | 'Meas' q '->' CBit                 -- Z-basis measurement
           | CBit ':=' 'xor' CBit*               -- classical parity
           | 'If' CBit 'then' Pauli q           -- classically-conditioned Pauli
    Circuit ::= Gate*
-/
import Physical.Basic

namespace QClifford
open Physical

/-- A classical bit (a measurement result). -/
abbrev CBit := Nat

/-- A physical Clifford+measurement gate. -/
inductive Gate
  | prepZero (q : PQubit)
  | prepPlus (q : PQubit)
  | H       (q : PQubit)
  | S       (q : PQubit)
  | X       (q : PQubit)
  | Z       (q : PQubit)
  | CNOT    (c t : PQubit)
  | CZ      (a b : PQubit)
  | meas    (q : PQubit) (r : CBit)              -- `Meas q -> r`
  | parity  (r : CBit) (srcs : List CBit)        -- `r := xor srcs`
  | ifPauli (r : CBit) (p : Pauli) (q : PQubit)  -- `If r then P q`
  deriving DecidableEq, Repr, Inhabited

/-- A QClifford circuit. -/
abbrev Circuit := List Gate

/-- The physical qubits a gate touches. -/
def Gate.qubits : Gate → List PQubit
  | .prepZero q | .prepPlus q | .H q | .S q | .X q | .Z q => [q]
  | .CNOT c t => [c, t]
  | .CZ a b   => [a, b]
  | .meas q _ => [q]
  | .parity _ _ => []
  | .ifPauli _ _ q => [q]

/-- Whether a gate is a two-qubit gate (`CNOT`/`CZ`). -/
def Gate.isTwoQubit : Gate → Bool
  | .CNOT .. | .CZ .. => true
  | _                 => false

/-- Whether a gate is a measurement. -/
def Gate.isMeas : Gate → Bool
  | .meas .. => true
  | _        => false

/-- Whether a gate is a purely classical assignment. -/
def Gate.isClassical : Gate → Bool
  | .parity .. => true
  | _          => false

/-! ## Resource readouts (honest counts on exactly this circuit). -/

/-- Number of physical qubits touched (max index + 1). -/
def Circuit.width (c : Circuit) : Nat :=
  c.foldl (fun w g => max w ((g.qubits.map (· + 1)).foldl max 0)) 0
/-- Total gate count. -/
def Circuit.gateCount (c : Circuit) : Nat := c.length
/-- Number of two-qubit gates. -/
def Circuit.twoQubitCount (c : Circuit) : Nat := (c.filter Gate.isTwoQubit).length
/-- Number of measurements. -/
def Circuit.measCount (c : Circuit) : Nat := (c.filter Gate.isMeas).length
/-- Number of classical parity assignments. -/
def Circuit.parityCount (c : Circuit) : Nat := (c.filter Gate.isClassical).length

/-! ## Example. -/

/-- A `CNOT(c,t)` realized from a `CZ`: `H t; CZ c t; H t`. -/
def cnotFromCZ (c t : PQubit) : Circuit := [.H t, .CZ c t, .H t]

example : (cnotFromCZ 0 1).gateCount = 3 := by decide
example : (cnotFromCZ 0 1).twoQubitCount = 1 := by decide
example : (cnotFromCZ 0 1).width = 2 := by decide

end QClifford
