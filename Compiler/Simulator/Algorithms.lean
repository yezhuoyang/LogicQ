/-
  Compiler.Simulator.Algorithms — the small Clifford-fragment quantum algorithms
  (`djConstant`/`djBalanced`/`grover2`/`simon2`), split out of
  Compiler/Simulator.lean.
-/
import Compiler.Simulator.Gate

namespace Compiler.Sim
open Compiler TypeChecker PPM ChainQ.GF2 Logical

/-! ## §5. Quantum algorithms (Clifford fragments) + outcome validation.

    HONEST SCOPE (M13 task 6): these run the algorithms as SOURCE-level logical
    `Gate` circuits and validate their OUTCOME distributions.  They are NOT claims
    about the LOWERED Mixed/PPM program — the algorithms are not compiled and then
    re-simulated here (a CNOT lowers to a PPM gadget whose channel is deferred, so
    its emitted form is intentionally NOT decoded; see §6).  The exact source-vs-
    EMITTED equality is established only for the DIRECT transversal fragment (§6). -/

/-- Deutsch–Jozsa, 1-bit query (qubit 0) + phase ancilla (qubit 1).  Constant `f`:
    no oracle. -/
def djConstant : List Gate := [.X 1, .H 0, .H 1, .H 0]
/-- Deutsch–Jozsa, balanced `f(x)=x`: oracle is `CNOT query→ancilla`. -/
def djBalanced : List Gate := [.X 1, .H 0, .H 1, .CNOT 0 1, .H 0]

/-- 2-qubit Grover, one marked item `|11⟩`: oracle `CZ`, then diffusion. -/
def grover2 : List Gate :=
  [.H 0, .H 1, .CZ 0 1, .H 0, .H 1, .X 0, .X 1, .CZ 0 1, .X 0, .X 1, .H 0, .H 1]

/-- Simon, n = 2, secret `s = 11`: input qubits 0,1; output qubits 2,3;
    `f(x) = (x₀⊕x₁, x₀⊕x₁)`. -/
def simon2 : List Gate :=
  [.H 0, .H 1, .CNOT 0 2, .CNOT 1 2, .CNOT 0 3, .CNOT 1 3, .H 0, .H 1]

end Compiler.Sim
