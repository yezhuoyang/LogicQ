/-
  Compiler.Simulator.State — (unnormalised) state vectors over `GInt` and the bit
  manipulation helpers (`bit`/`flipBit`/`amp`/`init`), split out of
  Compiler/Simulator.lean.
-/
import Compiler.Simulator.Arithmetic

namespace Compiler.Sim
open Compiler TypeChecker PPM ChainQ.GF2 Logical

/-! ## §2. State vectors and bit manipulation. -/

/-- A (unnormalised) state vector on `n` qubits: `2^n` amplitudes, index = basis
    state as a `Nat`, bit `i` (little-endian) = qubit `i`. -/
abbrev State := List GInt

/-- Bit `i` of `x` (little-endian). -/
def bit (x i : Nat) : Bool := (x / 2 ^ i) % 2 == 1

/-- Flip bit `i` of `x`. -/
def flipBit (x i : Nat) : Nat := if bit x i then x - 2 ^ i else x + 2 ^ i

/-- Amplitude at basis index `x` (0 out of range). -/
def amp (s : State) (x : Nat) : GInt := s.getD x GInt.zero

/-- `|0…0⟩` on `n` qubits. -/
def init (n : Nat) : State := GInt.one :: List.replicate (2 ^ n - 1) GInt.zero

end Compiler.Sim
