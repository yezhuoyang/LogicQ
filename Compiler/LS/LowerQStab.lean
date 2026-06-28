/-
  Compiler.LS.LowerQStab — lower the EXECUTABLE LS ops into a `QStab.StabilizerProg`,
  with the detector/observable/postselection/flow/obligation annotations carried in a
  SIDECAR (the `Check.Checked` summary) — NOT silently erased.

  QStab owns the physical Pauli measurements, the Clifford/prep instructions, and the
  SSA classical parity dataflow.  This pass projects the LS surgery program onto that
  dataflow (1:1 for the executable ops) and keeps every annotation on the side.

  What is checked here: the lowered StabilizerProg's classical DATAFLOW equals the LS
  program's dataflow (the measurement structure is preserved — `lower_dataflow`), and
  the lowered program is well-formed.  No surgery/flow/fault soundness is claimed.
-/
import Compiler.LS.Check
import Compiler.LS.Extract

namespace Compiler.LS
open QStab Physical

/-! ## §1. The executable lowering. -/

/-- Lower one LS op to its `QStab.StabilizerInstr`s.  Executable ops map 1:1; `meas`
    densifies its sparse Pauli to a physical `prop` and `parity` stays a `parity`
    (both bind a QStab var); ANNOTATION/deferred ops produce NO instruction (they live
    in the sidecar). -/
def lowerOp (n : Nat) : LSOp → List QStab.StabilizerInstr
  | .prepZero q   => [.prepZero q]
  | .prepPlus q   => [.prepPlus q]
  | .h q          => [.H q]
  | .s q          => [.S q]
  | .sDag q       => [.S q, .S q, .S q]                  -- S† = S³ (HONEST: QStab has no S†)
  | .x q          => [.X q]
  | .z q          => [.Z q]
  | .cnot c t     => [.CNOT c t]
  | .cz a b       => [.CZ a b]
  | .meas sched P _ => [.bind (.prop sched (SPauli.toDense n P))]
  | .parity srcs  => [.bind (.parity srcs)]
  | .detector _     => []
  | .observable _ _ => []
  | .postselect _   => []
  | .stage _ _      => []
  | .tick           => []
  | .deferred _     => []

/-- Lower the whole LS program to a `QStab.StabilizerProg` (executable part only). -/
def lower (p : Program) : QStab.StabilizerProg := (p.ops.map (lowerOp p.numQubits)).flatten

/-- The lowered QStab dataflow REALISES the given measurement vars: each `v` indexes a real
    physical `prop` (measurement) in `qstab.dataflow`.  This BRIDGES a logical observable's
    readout vars to actual QStab measurements — a STRUCTURAL observable-realisation check (it
    does NOT prove those measurements compose to the logical operator). -/
def readoutVarsAreProps (qstab : QStab.StabilizerProg) (vars : List QVar) : Bool :=
  let df := qstab.dataflow
  vars.all (fun v => match df[v]? with | some (.prop _ _) => true | _ => false)

/-! ## §2. The dataflow-preservation theorem (no silent erasure of measurements). -/

/-- Per-op: the measurement/parity content of `lowerOp` is exactly `toStmt?`. -/
theorem lowerOp_boundStmts (n : Nat) (op : LSOp) :
    (lowerOp n op).filterMap StabilizerInstr.boundStmt? = (LSOp.toStmt? n op).toList := by
  cases op <;> rfl

/-- List-level: the lowered dataflow equals the LS dataflow. -/
theorem lower_dataflow_list (n : Nat) (ops : List LSOp) :
    ((ops.map (lowerOp n)).flatten).filterMap StabilizerInstr.boundStmt?
      = ops.filterMap (LSOp.toStmt? n) := by
  induction ops with
  | nil => rfl
  | cons op rest ih =>
    simp only [List.map_cons, List.flatten_cons, List.filterMap_append,
               lowerOp_boundStmts, ih, List.filterMap_cons]
    cases LSOp.toStmt? n op <;> rfl

/-- **The lowered QStab dataflow IS the LS dataflow.**  The measurement/parity
    structure that the detectors/observables/postselection annotate is preserved by
    the lowering — it is not silently erased. -/
theorem lower_dataflow (p : Program) : (lower p).dataflow = p.dataflow := by
  simp only [lower, StabilizerProg.dataflow, Program.dataflow, lower_dataflow_list]

/-! ## §3. The checked lowering (program + sidecar). -/

/-- The SIDECAR of a lowering is exactly the `Check.Checked` summary: detectors,
    observables, postselection, flows, and deferred obligations. -/
abbrev Sidecar := Checked

/-- **Check then lower.**  Returns the executable `QStab.StabilizerProg` and its
    sidecar (the checked summary) — the annotations are KEPT, never dropped. -/
def lowerChecked (p : Program) : Except LSError (QStab.StabilizerProg × Sidecar) := do
  let c ← check p
  return (lower p, c)

/-- **Check then lower, with extractability surfaced CENTRALLY.**  Like `lowerChecked`,
    but it AUTOMATICALLY adds a `notExtractable` obligation for every physical
    measurement the current QStab2QClifford schemes cannot realise (a `Y` or mixed-X/Z
    support), for ANY LS program — not only chunks that attach them by hand.  The added
    obligations are DEDUPLICATED and merged WITHOUT duplicating any already present in
    the checked summary. -/
def lowerCheckedWithExtract (p : Program) :
    Except LSError (QStab.StabilizerProg × Sidecar) := do
  let (qstab, c) ← lowerChecked p
  let extra := (extractObligations p.dataflow).filter (fun o => !c.obligations.contains o)
  return (qstab, { c with obligations := c.obligations ++ extra })

/-! ## §4. Checked examples. -/

-- the lowered program is WELL-FORMED, and its dataflow equals the LS dataflow:
example : (lower goodProg).wf = true := by decide
example : (lower goodProg).dataflow = goodProg.dataflow := by decide
example : (lowerChecked goodProg).toOption.isSome = true := by decide

-- the lowering preserves the two `ZZ` measurements as physical `prop`s; the `detector`
-- is a SIDECAR annotation, NOT a QStab `parity`, so it does not appear in the dataflow
-- (checked via the dataflow, since `StabilizerInstr` has no `DecidableEq`):
example : (lower goodProg).dataflow =
    [ .prop (some ⟨0, 0⟩) (ofString "ZZ")
    , .prop (some ⟨1, 0⟩) (ofString "ZZ") ] := by decide
-- exactly 2 executable instructions (2 props; the detector/observable/postselect drop to the sidecar):
example : (lower goodProg).length = 2 := by decide
-- a `parity` op (a decoded classical XOR), by contrast, DOES lower to a QStab `parity` bind:
example : (lower { numQubits := 1, ops := [ .meas none [(0, .Z)], .parity [0] ] }).dataflow
    = [ .prop none (ofString "Z"), .parity [0] ] := by decide

-- the sidecar retains the detector (name + tags), observable, and postselection annotations:
example : (lowerChecked goodProg).toOption.map (fun pc => pc.2.detectors.map (·.name)) = some ["d0"] := by decide
example : (lowerChecked goodProg).toOption.map (fun pc => pc.2.detectors.map (·.tags)) = some [["color"]] := by decide
example : (lowerChecked goodProg).toOption.map (fun pc => pc.2.postselects)
    = some [PostPolicy.byDetector "d0", PostPolicy.byTag "color"] := by decide

-- a program that FAILS the check does not lower (the check gates the lowering):
example : (lowerChecked { numQubits := 1, ops := [ .meas none [] ] }).toOption.isSome = false := by decide

-- `sDag` lowers HONESTLY to three `S` (S³ = S†), preserving the dataflow (no QStab var bound):
example : lowerOp 1 (.sDag 0) = [.S 0, .S 0, .S 0] := by rfl
example : (lower { numQubits := 1, ops := [ .sDag 0, .meas none [(0, .X)] ] }).dataflow
    = [ .prop none (ofString "X") ] := by decide

-- a `tick` is a pure scheduling annotation: it binds no QStab var and produces no instruction:
example : lowerOp 1 .tick = [] := by rfl
example : (lower { numQubits := 1, ops := [ .meas none [(0, .Z)], .tick, .parity [0] ] }).dataflow
    = [ .prop none (ofString "Z"), .parity [0] ] := by decide

-- CENTRALIZED extractability: lowering a program with a `Y` measurement AUTOMATICALLY
-- surfaces a `notExtractable` obligation; a uniform-`Z` program surfaces none:
example : (lowerCheckedWithExtract { numQubits := 2, ops := [ .meas none [(0, .Y), (1, .Y)] ] }).toOption.map
    (fun pc => pc.2.obligations.any (fun o => match o with | .notExtractable _ _ => true | _ => false)) = some true := by decide
example : (lowerCheckedWithExtract { numQubits := 2, ops := [ .meas none [(0, .Z), (1, .Z)] ] }).toOption.map
    (fun pc => pc.2.obligations.any (fun o => match o with | .notExtractable _ _ => true | _ => false)) = some false := by decide

end Compiler.LS
