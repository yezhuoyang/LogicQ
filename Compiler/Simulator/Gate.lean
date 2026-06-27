/-
  Compiler.Simulator.Gate — the simulator gate set (`Gate`/`applyGate`/`runGates`)
  and the measurement read-out (`regProb`), split out of Compiler/Simulator.lean.
-/
import Compiler.Simulator.State

namespace Compiler.Sim
open Compiler TypeChecker PPM ChainQ.GF2 Logical

/-! ## §3. Clifford + Pauli gates. -/

/-- Logical gates the simulator understands (a Clifford set + Paulis). -/
inductive Gate
  | H    (i : Nat)
  | S    (i : Nat)
  | X    (i : Nat)
  | Z    (i : Nat)
  | CNOT (c t : Nat)
  | CZ   (c t : Nat)
  deriving Repr, DecidableEq

/-- Apply one gate to the `n`-qubit state (exact, unnormalised). -/
def applyGate (n : Nat) (g : Gate) (s : State) : State :=
  (List.range (2 ^ n)).map (fun x =>
    match g with
    | .H i      => if bit x i then (amp s (flipBit x i)) - (amp s x)
                              else (amp s x) + (amp s (flipBit x i))
    | .S i      => if bit x i then GInt.mulI (amp s x) else amp s x
    | .X i      => amp s (flipBit x i)
    | .Z i      => if bit x i then GInt.neg (amp s x) else amp s x
    | .CNOT c t => amp s (if bit x c then flipBit x t else x)
    | .CZ c t   => if bit x c && bit x t then GInt.neg (amp s x) else amp s x)

/-- Run a gate list left-to-right. -/
def runGates (n : Nat) (gs : List Gate) (s : State) : State :=
  gs.foldl (fun st g => applyGate n g st) s

/-! ## §4. Measurement read-out. -/

/-- Total (unnormalised) probability weight of measuring `qubits` to `pat`. -/
def regProb (n : Nat) (qubits : List Nat) (pat : List Bool) (s : State) : Int :=
  ((List.range (2 ^ n)).filter
      (fun x => (qubits.zip pat).all (fun qp => bit x qp.1 == qp.2))).foldl
    (fun acc x => acc + GInt.normSq (amp s x)) 0

end Compiler.Sim
