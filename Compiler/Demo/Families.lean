/-
  Compiler.Demo.Families — real ChainQ FAMILY codes compile through the compiler (§8):
  surface, toric, HGP, BB, and lifted-product codes on the exact-operational fragment.
-/
import Compiler.Demo.Common

namespace Compiler.Demo
open Compiler Compiler.Sim TypeChecker ChainQ

/-! ## §8. Real ChainQ FAMILY codes compile through the compiler (M18 task 4).

    The full checked pipeline `mk<Family> d → cssToTypedBlock? → TypedEnv → compile? →
    checkLogicalExec`, exercising surface, toric, HGP, BB, and lifted-product codes on
    the EXACT-operational fragment (`xGate`/`zGate`) + legal single-logical measurement.
    Transversal `H`/`S` is generally NOT legal on these codes (`hx ≠ hz`), so the
    direct-Clifford fragment is not used here. -/

/-- Build a single-block `TypedEnv` from a checked CSS family code (the surface-2
    pattern, generalized).  The error branches are unreachable for the instances used
    (proven by the passing `decide` examples — an empty env would reject `⟨0,0⟩`). -/
def envOf : Except ChainQError CheckedCSSCode → TypedEnv
  | .ok cc => match cssToTypedBlock? cc with | .ok tb => ⟨[tb]⟩ | .error _ => ⟨[]⟩
  | .error _ => ⟨[]⟩

-- SURFACE-2 (n=5, k=1) — with explicit structural assertions (no silent empty fallback):
def surfEnv : TypedEnv := envOf (ChainQ.mkSurface 2)
example : surfEnv.blocks.length = 1 := by decide
example : (surfEnv.blocks.head?.map (·.block.n))          = some 5 := by decide   -- n = 5
example : (surfEnv.blocks.head?.map (·.block.lx.length))  = some 1 := by decide   -- k = 1
example : ok? (compile? .executable famCfg surfEnv [.xGate ⟨0, 0⟩]) = true := by decide
example : (match compile? .executable famCfg surfEnv [.xGate ⟨0, 0⟩] with
           | .ok c => ok? (checkLogicalExec [] surfEnv c.prog) | _ => false) = true := by decide
example : ok? (compile? .executable famCfg surfEnv
    [.xGate ⟨0, 0⟩, .zGate ⟨0, 0⟩, .measure 0 [(⟨0, 0⟩, PPM.PLetter.Z)]]) = true := by decide
-- transversal H is (honestly) NOT legal on the surface code (hx ≠ hz):
example : ok? (compile? .executable famCfg surfEnv [.blockTransversal 0 hGate2x2]) = false := by decide

-- TORIC-2 (n=8, k=2): a logical Pauli on a VALID index compiles + emitted type-checks;
-- an OUT-OF-RANGE index ⟨0,2⟩ (k=2) is rejected.
def toricEnv : TypedEnv := envOf (ChainQ.mkToric 2)
example : (toricEnv.blocks.head?.map (·.block.lx.length)) = some 2 := by decide   -- k = 2
example : ok? (compile? .executable famCfg toricEnv [.xGate ⟨0, 1⟩]) = true := by decide
example : (match compile? .executable famCfg toricEnv [.zGate ⟨0, 1⟩, .measure 0 [(⟨0, 1⟩, PPM.PLetter.Z)]] with
           | .ok c => ok? (checkLogicalExec [] toricEnv c.prog) | _ => false) = true := by decide
example : ok? (compile? .executable famCfg toricEnv [.xGate ⟨0, 2⟩]) = false := by decide
example : sourceWellFormed [] toricEnv PPMState.init [.xGate ⟨0, 2⟩] = false := by decide

-- HGP instance (repOpen 3 × repOpen 2, n=8, k=1), genuinely distinct from surface:
def hgpEnv : TypedEnv := envOf (ChainQ.mkHGP (ChainQ.repOpen 3) (ChainQ.repOpen 2) 2 3 1 2)
example : (hgpEnv.blocks.head?.map (·.block.lx.length)) = some 1 := by decide   -- k = 1
example : ok? (compile? .executable famCfg hgpEnv
    [.xGate ⟨0, 0⟩, .zGate ⟨0, 0⟩, .measure 0 [(⟨0, 0⟩, PPM.PLetter.Z)]]) = true := by decide
example : (match compile? .executable famCfg hgpEnv [.xGate ⟨0, 0⟩] with
           | .ok c => ok? (checkLogicalExec [] hgpEnv c.prog) | _ => false) = true := by decide

-- BIVARIATE-BICYCLE (ℓ=m=2, A=1+x, B=1+y, n=8, k=2):
def bbEnv : TypedEnv := envOf (ChainQ.mkBB 2 2 [(0, 0), (1, 0)] [(0, 0), (0, 1)])
example : (bbEnv.blocks.head?.map (·.block.lx.length)) = some 2 := by decide   -- k = 2
example : ok? (compile? .executable famCfg bbEnv [.zGate ⟨0, 1⟩, .measure 0 [(⟨0, 1⟩, PPM.PLetter.Z)]]) = true := by decide
example : ok? (compile? .executable famCfg bbEnv [.xGate ⟨0, 2⟩]) = false := by decide

-- LIFTED-PRODUCT (ℓ=2, A=[1,x], n=10, k=2):
def lpEnv : TypedEnv := envOf (ChainQ.mkLiftedProduct 2 [[[0], [1]]] 1 2)
example : (lpEnv.blocks.head?.map (·.block.lx.length)) = some 2 := by decide   -- k = 2
example : ok? (compile? .executable famCfg lpEnv [.zGate ⟨0, 1⟩, .measure 0 [(⟨0, 1⟩, PPM.PLetter.Z)]]) = true := by decide
example : ok? (compile? .executable famCfg lpEnv [.xGate ⟨0, 2⟩]) = false := by decide

end Compiler.Demo
