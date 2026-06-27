/-
  Compiler.Demo.Common — SHARED fixtures for the demo-complete pipeline (M15/M16),
  split out of the monolithic `Compiler.Demo` so multiple demo files can reuse them.

  Owns the configs and typed envs used across the §1/§2/§4/§8 demo files:
  `envN`, `tenv2`, `tenv4`, `demoCfg`, `dj2Cfg`, `famCfg`.  See the per-area demo
  files (Direct/Algorithms/Frames/Entangling/Families) for the examples themselves.
-/
import Compiler.MixedSemantics
import Compiler.Simulator
import ChainQ.Checked
import TypeChecker.Core.Elaborate

namespace Compiler.Demo
open Compiler Compiler.Sim TypeChecker ChainQ

/-! ## Shared configs / typed envs. -/

/-- The demo compile configuration (no capabilities, ancilla seed in block 1). -/
def demoCfg : CompileConfig := { caps := [], anc := ⟨1, 0⟩ }

/-- An `n`-block env: `n` bare single-logical qubits (blocks `0..n-1`). -/
def envN : Nat → TypedEnv
  | 0     => ⟨[]⟩
  | n + 1 => ⟨⟨q0, by decide⟩ :: (envN n).blocks⟩

def tenv2 : TypedEnv := envN 2
def tenv4 : TypedEnv := envN 4

/-- The DJ-constant env config (2 blocks, ancilla seed past them). -/
def dj2Cfg : CompileConfig := { caps := [], anc := ⟨2, 0⟩ }

def famCfg : CompileConfig := { caps := [], anc := ⟨1, 0⟩ }

end Compiler.Demo
