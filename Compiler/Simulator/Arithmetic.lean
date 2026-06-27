/-
  Compiler.Simulator.Arithmetic — the Gaussian integers `GInt` (a+bi, Mathlib-free,
  `DecidableEq`) used as the simulator's exact amplitude ring (split out of
  Compiler/Simulator.lean).
-/
import Compiler.Mixed

namespace Compiler.Sim
open Compiler TypeChecker PPM ChainQ.GF2 Logical

/-! ## §1. Gaussian integers. -/

/-- A Gaussian integer `re + im·i`. -/
structure GInt where
  re : Int
  im : Int
  deriving DecidableEq, Repr, Inhabited

namespace GInt
def zero : GInt := ⟨0, 0⟩
def one  : GInt := ⟨1, 0⟩
def add (a b : GInt) : GInt := ⟨a.re + b.re, a.im + b.im⟩
def sub (a b : GInt) : GInt := ⟨a.re - b.re, a.im - b.im⟩
def neg (a : GInt) : GInt := ⟨-a.re, -a.im⟩
/-- Multiply by `i`: `i·(a+bi) = -b + a·i`. -/
def mulI (a : GInt) : GInt := ⟨-a.im, a.re⟩
/-- `|a+bi|² = a² + b²` (the unnormalised measurement weight). -/
def normSq (a : GInt) : Int := a.re * a.re + a.im * a.im
instance : Add GInt := ⟨add⟩
instance : Sub GInt := ⟨sub⟩
instance : Neg GInt := ⟨neg⟩
end GInt

end Compiler.Sim
