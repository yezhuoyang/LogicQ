/-
  QStab.Syntax — the physical stabilizer-measurement IR (level L_QStab).

  A QStab program is a dataflow of PHYSICAL Pauli measurements and classical
  parity combinations, binding classical variables in program order (SSA-style,
  `c0, c1, …`).  This is exactly the README form:

      c0 = Prop[r=0, s=0] ZZI       -- measure physical Pauli ZZI at round 0, slot 0
      c1 = Prop[r=0, s=1] IZZ
      d0 = Parity c0 c2             -- classical XOR of earlier outcomes
      c4 = Prop ZZZ                 -- scheduling coords optional
      o0 = Parity c4                -- a decoded/logical output bit

  `Prop[r,s]` is a physical Pauli measurement scheduled at round `r`, slot `s`;
  `Parity` is the XOR of named outcome variables (syndromes / logical readouts).

  PHYSICAL LEVEL: Pauli strings are dense over physical qubits.  Pure data
  (Mathlib-free); the dataflow semantics is in `QStab/Semantics.lean`.

  Standard-PL BNF:

    QVar      ::= c0 | c1 | …                              -- classical variable (SSA)
    PauliStr  ::= ('I'|'X'|'Y'|'Z')+                       -- dense physical Pauli, e.g. ZZI
    Sched     ::= '[' 'r' '=' Nat ',' 's' '=' Nat ']'
    Stmt      ::= QVar '=' 'Prop' Sched? PauliStr          -- physical measurement
                | QVar '=' 'Parity' QVar+                   -- classical XOR
    Prog      ::= Stmt*
-/
import Physical.Basic

namespace QStab
open Physical

/-- A classical variable (a measurement outcome or a parity), bound in program
    order: the `i`-th statement binds variable `i`. -/
abbrev QVar := Nat

/-- A DENSE physical Pauli string over physical qubits `0 … n-1`, INDEXED BY LIST POSITION:
    the `i`-th element is the Pauli on physical qubit `i` (e.g. `ZZI = Z[0]Z[1]I[2]`, and
    `X[1]X[3]` on 4 qubits is `IXIX`, NOT `XX`).  For human-facing construction prefer the
    explicit indexed `QStab.SparsePauli` (`[(1, X), (3, X)]`) + its checked `toDense?`
    (`QStab/SparsePauli.lean`), which makes the physical indexing unambiguous and refuses
    empty / identity / duplicate / out-of-range operators. -/
abbrev PauliString := List Pauli

/-- Scheduling coordinates `[r = round, s = slot]`. -/
structure Sched where
  round : Nat
  slot  : Nat
  deriving DecidableEq, Repr, Inhabited

/-- A QStab statement; each binds the next classical variable. -/
inductive Stmt
  /-- `c = Prop[r,s] P` — MEASURE the physical Pauli product `P` (optionally scheduled at
      round `r`, slot `s`), binding its `±1` outcome.  `.prop` is for physical Pauli
      MEASUREMENT / syndrome extraction ONLY; physical CLIFFORD and PAULI APPLICATIONS
      (`H`/`S`/`X`/`Z`/`CNOT`/`CZ`) are separate stabilizer instructions
      (`QStab.StabilizerInstr`, `QStab/StabilizerProgram.lean`), NOT `.prop`. -/
  | prop   (sched : Option Sched) (P : PauliString)
  /-- `d = Parity c…` — the classical XOR of the listed earlier outcomes. -/
  | parity (srcs : List QVar)
  deriving DecidableEq, Repr, Inhabited

/-- A QStab program. -/
abbrev Prog := List Stmt

/-- Well-formedness from a starting variable count: a `parity` may reference
    only already-bound variables; every statement binds the next one. -/
def Prog.wfFrom : Nat → Prog → Bool
  | _, []                 => true
  | n, .prop _ _   :: t    => Prog.wfFrom (n + 1) t
  | n, .parity srcs :: t   => srcs.all (fun i => decide (i < n)) && Prog.wfFrom (n + 1) t

/-- **Program well-formedness**: variables bind sequentially from `c0`, and
    every parity references only already-bound variables. -/
def Prog.wf (p : Prog) : Bool := Prog.wfFrom 0 p

/-- The README readout program (a distance-3 repetition-style syndrome +
    logical readout).  Variables: `c0..c4` (props) and `d0,d1,o0` (parities). -/
def progReadout : Prog :=
  [ .prop (some ⟨0, 0⟩) (ofString "ZZI"),   -- c0
    .prop (some ⟨0, 1⟩) (ofString "IZZ"),   -- c1
    .prop (some ⟨1, 0⟩) (ofString "ZZI"),   -- c2
    .parity [0, 2],                            -- d0 = c0 ⊕ c2
    .prop (some ⟨1, 1⟩) (ofString "IZZ"),   -- c3
    .parity [1, 4],                            -- d1 = c1 ⊕ c3
    .prop none (ofString "ZZZ"),              -- c4
    .parity [6] ]                              -- o0 = c4

example : progReadout.wf = true := by decide
-- A forward reference (parity before the variable is bound) is rejected:
example : Prog.wf [.parity [0]] = false := by decide

end QStab
