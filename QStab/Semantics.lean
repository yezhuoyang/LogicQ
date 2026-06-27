/-
  QStab.Semantics — the classical dataflow semantics of a QStab program.

  A QStab program's classical content is a dataflow over `Bool` outcomes:
  given the `±1` results of the physical measurements (the `prop`s), every
  variable's value is determined — a `prop` variable IS its measurement outcome,
  and a `parity` variable is the XOR of the earlier variables it references.
  `eval` computes the value of every bound variable, in order.

  (The quantum side — how the `prop` outcomes arise from, and back-act on, the
  physical stabilizer state — is the same `proj`-style interface used by
  `PPM.Semantics`; here we fix the back-end-independent classical dataflow,
  which is what carries the syndrome / logical-readout meaning.)
-/
import QStab.Syntax

namespace QStab
open Physical

/-- Evaluate a program, threading the physical measurement outcomes.
    `o k` is the `±1` result (`true = -1`) of the `k`-th `prop`; `acc` holds the
    already-computed variable values (index = variable). -/
def evalAux : Prog → Nat → (Nat → Bool) → List Bool → List Bool
  | [],                 _, _, acc => acc
  | .prop _ _   :: t,   k, o, acc => evalAux t (k + 1) o (acc ++ [o k])
  | .parity srcs :: t,  k, o, acc =>
      evalAux t k o (acc ++ [srcs.foldl (fun b i => xor b (acc.getD i false)) false])

/-- The value of every bound variable, in program order, given the `prop`
    outcomes `o` (indexed by `prop`-occurrence). -/
def eval (p : Prog) (o : Nat → Bool) : List Bool := evalAux p 0 o []

/-- The value of variable `v`. -/
def evalVar (p : Prog) (o : Nat → Bool) (v : QVar) : Bool := (eval p o).getD v false

/-- Every statement binds exactly one variable, so `eval` returns one value per
    statement. -/
theorem evalAux_length (p : Prog) : ∀ (k : Nat) (o : Nat → Bool) (acc : List Bool),
    (evalAux p k o acc).length = acc.length + p.length := by
  induction p with
  | nil => intro k o acc; rfl
  | cons s t ih =>
    intro k o acc
    cases s <;> simp [evalAux, ih, List.length_append] <;> omega

theorem eval_length (p : Prog) (o : Nat → Bool) : (eval p o).length = p.length := by
  simp [eval, evalAux_length]

/-! ## The README readout, evaluated. -/

-- All-`+1` outcomes ⇒ all variables (syndromes + output) are `0`.
example : eval progReadout (fun _ => false)
    = [false, false, false, false, false, false, false, false] := by decide

-- A single flipped check `c0 = -1` flips the syndrome `d0 = c0 ⊕ c2`.
example : evalVar progReadout (fun k => decide (k = 0)) 3 = true := by decide

-- …and leaves the logical output `o0 = c4` untouched.
example : evalVar progReadout (fun k => decide (k = 0)) 7 = false := by decide

end QStab
