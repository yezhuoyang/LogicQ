/-
  QStab.StabilizerProgram -- stabilizer-formalism instruction shell.

  The original QStab `Prog` is a classical dataflow of physical Pauli-product
  measurements and parities.  Protocol verification often needs a richer
  stabilizer-formalism artifact containing preparations, Clifford gates, and
  feed-forward corrections too.  We keep those quantum instructions explicit
  while projecting the measurement/parity bindings to the existing checked
  dataflow semantics.
-/
import QStab.Semantics

namespace QStab
open Physical

/-- Stabilizer-formalism instructions at the QStab level.

    `.bind stmt` is the only instruction that binds a new QStab classical
    variable.  `ifPauli` may reference a previously-bound variable and is checked
    by `StabilizerProg.wf`. -/
inductive StabilizerInstr
  | bind     (stmt : Stmt)
  | prepZero (q : PQubit)
  | prepPlus (q : PQubit)
  | H        (q : PQubit)
  | S        (q : PQubit)
  | X        (q : PQubit)
  | Z        (q : PQubit)
  | CNOT     (control target : PQubit)
  | CZ       (a b : PQubit)
  | ifPauli  (src : QVar) (p : Pauli) (q : PQubit)
  deriving Repr, Inhabited

abbrev StabilizerProg := List StabilizerInstr

def StabilizerInstr.boundStmt? : StabilizerInstr -> Option Stmt
  | .bind stmt => some stmt
  | _ => none

/-- The classical measurement/parity dataflow contained in a richer stabilizer
    program. -/
def StabilizerProg.dataflow (prog : StabilizerProg) : Prog :=
  prog.filterMap StabilizerInstr.boundStmt?

/-- Well-formedness from an existing variable count.  Quantum Clifford
    instructions do not bind variables; `.bind` does; `ifPauli` can only read an
    earlier variable. -/
def StabilizerProg.wfFrom : Nat -> StabilizerProg -> Bool
  | _, [] => true
  | n, .bind (.prop _ _) :: rest => StabilizerProg.wfFrom (n + 1) rest
  | n, .bind (.parity srcs) :: rest =>
      srcs.all (fun i => decide (i < n)) && StabilizerProg.wfFrom (n + 1) rest
  | n, .ifPauli src _ _ :: rest =>
      decide (src < n) && StabilizerProg.wfFrom n rest
  | n, _ :: rest => StabilizerProg.wfFrom n rest

def StabilizerProg.wf (prog : StabilizerProg) : Bool := StabilizerProg.wfFrom 0 prog

def StabilizerProg.eval (prog : StabilizerProg) (outcomes : Nat -> Bool) : List Bool :=
  QStab.eval prog.dataflow outcomes

def StabilizerProg.evalVar (prog : StabilizerProg) (outcomes : Nat -> Bool) (v : QVar) : Bool :=
  QStab.evalVar prog.dataflow outcomes v

def exampleStabilizerProg : StabilizerProg :=
  [ .prepZero 0,
    .H 0,
    .bind (.prop none (ofString "Z")),
    .ifPauli 0 .X 0,
    .bind (.parity [0]) ]

example : exampleStabilizerProg.wf = true := by decide
example : exampleStabilizerProg.dataflow = [.prop none (ofString "Z"), .parity [0]] := by decide
example : exampleStabilizerProg.evalVar (fun _ => false) 1 = false := by decide
example : (StabilizerProg.wf [.ifPauli 0 .X 0]) = false := by decide

end QStab
