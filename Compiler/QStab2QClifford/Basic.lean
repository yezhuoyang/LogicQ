/-
  Compiler.QStab2QClifford — QStab → QClifford syndrome-extraction pass (AGGREGATE).

  Lowers a QStab program (physical Pauli measurements + classical parities) to a
  concrete QClifford circuit, choosing a per-`Prop` extraction scheme:

    standard X/Z · destructive X/Z · Shor (cat+verifier) · Knill (transversal) ·
    flag (single) · flag2 (double)

  A DIRECT scheme binds its syndrome with one measurement into the result var; a
  MULTI-measurement scheme emits several physical measurements into FRESH aux bits
  and a final classical `parity` of the syndrome subset (verifier/flag bits stay
  separate).  `compile?_trace_correct` proves the emitted circuit, under the
  measurement-trace host, realises the QStab SSA classical dataflow into the
  QClifford store — the COMPILER / classical-dataflow contract ONLY.  Fault
  tolerance, the verifier/flag weight bounds, hook detection, and the physical
  stabilizer channel are NOT proven here (they are LeanQEC's Heisenberg layer, a
  different semantics).
-/
import Compiler.QStab2QClifford.Trace
import Compiler.QStab2QClifford.Scheme
import Compiler.QStab2QClifford.Standard
import Compiler.QStab2QClifford.Shor
import Compiler.QStab2QClifford.Knill
import Compiler.QStab2QClifford.Flag
import Compiler.QStab2QClifford.Compile

namespace Compiler.QStab2QClifford
open Physical

/-! ## Smart constructors. -/

def stdX (anc : PQubit) (order : List PQubit) : ExtractionSpec := .standardX order anc
def stdZ (anc : PQubit) (order : List PQubit) : ExtractionSpec := .standardZ order anc
def destX (q : PQubit) : ExtractionSpec := .destructiveX q
def destZ (q : PQubit) : ExtractionSpec := .destructiveZ q
def shorXSpec (order cats : List PQubit) (ver : PQubit) : ExtractionSpec := .shorX order cats ver
def shorZSpec (order cats : List PQubit) (ver : PQubit) : ExtractionSpec := .shorZ order cats ver
def knillZSpec (order ancs : List PQubit) : ExtractionSpec := .knillZ order ancs
def knillXSpec (order ancs : List PQubit) : ExtractionSpec := .knillX order ancs
def flagXSpec (order : List PQubit) (anc flag : PQubit) : ExtractionSpec := .flagX order anc flag
def flag2XSpec (order : List PQubit) (anc flag1 flag2 : PQubit) : ExtractionSpec :=
  .flag2X order anc flag1 flag2

/-! ## §1. Standard X/Z — still compile EXACTLY as before (M23 baseline). -/

def repetitionReadoutCfg : CompileConfig :=
  { specOf := fun k =>
      match k with
      | 0 => stdZ 3 [0, 1]
      | 1 => stdZ 3 [1, 2]
      | 2 => stdZ 3 [1, 0]
      | 3 => stdZ 3 [2, 1]
      | _ => stdZ 3 [0, 1, 2] }

example : specsOk repetitionReadoutCfg QStab.progReadout = true := by decide
example : (compile repetitionReadoutCfg QStab.progReadout).measCount = 5 := by decide
example : (compile repetitionReadoutCfg QStab.progReadout).parityCount = 3 := by decide

-- The standard-Z gadget circuit is byte-identical to the pre-M23 pass:
example : compileProp (stdZ 3 [1, 0]) 7 0 =
    [.prepZero 3, .CNOT 1 3, .CNOT 0 3, .meas 3 7] := by decide

example : extractionSpecOk (Physical.ofString "ZZI") (stdZ 3 [1, 0]) = true := by decide
example : extractionSpecOk (Physical.ofString "ZZI") (stdZ 3 [0]) = false := by decide
example : extractionSpecOk (Physical.ofString "ZYI") (stdZ 3 [0, 1]) = false := by decide
example : extractionSpecOk (Physical.ofString "Z") (destZ 0) = true := by decide
example : extractionSpecOk (Physical.ofString "ZZ") (destZ 0) = false := by decide

example : ok? (compile? repetitionReadoutCfg QStab.progReadout) = true := by decide
example : err? .sourceMalformed (compile? repetitionReadoutCfg [.parity [0]]) = true := by decide
example :
    err? .badExtractionSchedule
      (compile? { specOf := fun _ => stdZ 3 [0] } [.prop none (Physical.ofString "ZZI")]) = true := by
  decide

-- Trace-host dataflow: a single flipped check (`c0 = -1`) sets the syndrome `d0`
-- (var 3 = c0 ⊕ c2) and leaves the logical output `o0` (var 7) at 0.
example :
    (QClifford.run (traceHost (fun k => decide (k = 0)))
      (compile repetitionReadoutCfg QStab.progReadout) { next := 0 } QClifford.Store.empty).2 3
      = true := by decide
example :
    (QClifford.run (traceHost (fun k => decide (k = 0)))
      (compile repetitionReadoutCfg QStab.progReadout) { next := 0 } QClifford.Store.empty).2 7
      = false := by decide

/-! ## §2. Shor (cat-state + verifier), weights 2 and 4. -/

def shorX2 : ExtractionSpec := shorXSpec [0, 1] [2, 3] 4
def shorX2Cfg : CompileConfig := { specOf := fun _ => shorX2 }
def shorX2Prog : QStab.Prog := [.prop none (Physical.ofString "XX")]

example : extractionSpecOk (Physical.ofString "XX") shorX2 = true := by decide
example : ok? (compile? shorX2Cfg shorX2Prog) = true := by decide
example : (compile shorX2Cfg shorX2Prog).measCount = 3 := by decide   -- verifier + 2 cats
example : (compile shorX2Cfg shorX2Prog).parityCount = 1 := by decide  -- the syndrome parity

-- Trace dataflow: a flip on cat-measurement slot 1 (cat₀) sets the syndrome (var 0);
-- the verifier bit (aux 1) reads slot 0 and stays 0.
example :
    (QClifford.run (traceHost (fun k => decide (k = 1)))
      (compile shorX2Cfg shorX2Prog) { next := 0 } QClifford.Store.empty).2 0 = true := by decide
example :
    (QClifford.run (traceHost (fun k => decide (k = 1)))
      (compile shorX2Cfg shorX2Prog) { next := 0 } QClifford.Store.empty).2 1 = false := by decide

def shorX4 : ExtractionSpec := shorXSpec [0, 1, 2, 3] [4, 5, 6, 7] 8
example : extractionSpecOk (Physical.ofString "XXXX") shorX4 = true := by decide
example : ok? (compile? { specOf := fun _ => shorX4 } [.prop none (Physical.ofString "XXXX")]) = true := by decide
example : (compile { specOf := fun _ => shorX4 } [.prop none (Physical.ofString "XXXX")]).measCount = 5 := by decide

def shorZ2 : ExtractionSpec := shorZSpec [0, 1] [2, 3] 4
example : extractionSpecOk (Physical.ofString "ZZ") shorZ2 = true := by decide
example : ok? (compile? { specOf := fun _ => shorZ2 } [.prop none (Physical.ofString "ZZ")]) = true := by decide
example : (compile { specOf := fun _ => shorZ2 } [.prop none (Physical.ofString "ZZ")]).measCount = 3 := by decide

/-! ## §3. Knill (transversal CNOT). -/

def knillZ2 : ExtractionSpec := knillZSpec [0, 1] [2, 3]
def knillZ2Cfg : CompileConfig := { specOf := fun _ => knillZ2 }
def knillZ2Prog : QStab.Prog := [.prop none (Physical.ofString "ZZ")]

example : extractionSpecOk (Physical.ofString "ZZ") knillZ2 = true := by decide
example : ok? (compile? knillZ2Cfg knillZ2Prog) = true := by decide
example : (compile knillZ2Cfg knillZ2Prog).measCount = 2 := by decide  -- one per data qubit
example : (compile knillZ2Cfg knillZ2Prog).parityCount = 1 := by decide

-- Trace dataflow: flipping ancilla slot 0 sets the syndrome (parity of both ancillas).
example :
    (QClifford.run (traceHost (fun k => decide (k = 0)))
      (compile knillZ2Cfg knillZ2Prog) { next := 0 } QClifford.Store.empty).2 0 = true := by decide

/-! ## §4. Flag and Flag2 (weight 4). -/

def flagX4 : ExtractionSpec := flagXSpec [0, 1, 2, 3] 4 5
example : extractionSpecOk (Physical.ofString "XXXX") flagX4 = true := by decide
example : ok? (compile? { specOf := fun _ => flagX4 } [.prop none (Physical.ofString "XXXX")]) = true := by decide
example : (compile { specOf := fun _ => flagX4 } [.prop none (Physical.ofString "XXXX")]).measCount = 2 := by decide  -- syndrome + flag

def flag2X4 : ExtractionSpec := flag2XSpec [0, 1, 2, 3] 4 5 6
example : extractionSpecOk (Physical.ofString "XXXX") flag2X4 = true := by decide
example : ok? (compile? { specOf := fun _ => flag2X4 } [.prop none (Physical.ofString "XXXX")]) = true := by decide
example : (compile { specOf := fun _ => flag2X4 } [.prop none (Physical.ofString "XXXX")]).measCount = 3 := by decide  -- syndrome + 2 flags

/-! ## §5. Bad schedules are REJECTED. -/

-- wrong support (order is not the support of P)
example : extractionSpecOk (Physical.ofString "XX") (stdX 3 [0]) = false := by decide
-- wrong Pauli basis (standardX wants X, P is Z)
example : extractionSpecOk (Physical.ofString "ZZ") (stdX 3 [0, 1]) = false := by decide
-- duplicate support
example : extractionSpecOk (Physical.ofString "XX") (shorXSpec [0, 0] [2, 3] 4) = false := by decide
-- wrong ancilla count (|cats| ≠ |order|)
example : extractionSpecOk (Physical.ofString "XX") (shorXSpec [0, 1] [2] 4) = false := by decide
-- ancilla overlaps data
example : extractionSpecOk (Physical.ofString "XX") (shorXSpec [0, 1] [1, 3] 4) = false := by decide
-- Knill wrong ancilla count
example : extractionSpecOk (Physical.ofString "ZZ") (knillZSpec [0, 1] [2]) = false := by decide
-- flag2 out of scope (support weight > 4)
example : extractionSpecOk (Physical.ofString "XXXXX") (flag2XSpec [0, 1, 2, 3, 4] 5 6 7) = false := by decide
-- whole-program rejection of a bad Shor schedule
example :
    err? .badExtractionSchedule
      (compile? { specOf := fun _ => shorXSpec [0, 1] [2] 4 } [.prop none (Physical.ofString "XX")])
      = true := by decide

/-! ### M23 review fix: helpers must live OUTSIDE the data register `[0, P.length)`.

    A helper aliasing a data qubit that carries `I` in `P` (so it is absent from the
    measured `order`) was previously accepted; it is now REJECTED.  Here `P = "XIX"`
    has `P.length = 3`, so qubit `1` is a live (identity) data qubit. -/
example : extractionSpecOk (Physical.ofString "XIX") (.standardX [0, 2] 1) = false := by decide
example : extractionSpecOk (Physical.ofString "XIX") (.shorX [0, 2] [1, 3] 4) = false := by decide
example : extractionSpecOk (Physical.ofString "XIX") (.knillX [0, 2] [1, 4]) = false := by decide
-- the same schedules with helpers ≥ P.length (= 3) are accepted:
example : extractionSpecOk (Physical.ofString "XIX") (.standardX [0, 2] 3) = true := by decide
example : extractionSpecOk (Physical.ofString "XIX") (.shorX [0, 2] [3, 4] 5) = true := by decide

/-! ## §6. Source-semantics bridge (M23): compiled store agrees with `QStab.evalVar`.

    On a Knill multi-measurement prop (`ZZ`) followed by a `Parity`, the compiled
    store matches the QStab source semantics under the extraction-induced outcome
    stream (each prop's syndrome = the XOR of its physical measurements).  Classical
    dataflow only. -/

def bridgeCfg : CompileConfig := { specOf := fun _ => knillZSpec [0, 1] [2, 3] }
def bridgeProg : QStab.Prog := [.prop none (Physical.ofString "ZZ"), .parity [0]]

-- The prop var (0) and the parity var (1) both equal `QStab.evalVar` under the
-- extraction-induced stream (verified for a concrete physical trace):
example :
    (QClifford.run (traceHost (fun k => decide (k = 0)))
      (compile bridgeCfg bridgeProg) { next := 0 } QClifford.Store.empty).2 0
      = QStab.evalVar bridgeProg (extractedOutcome bridgeCfg (fun k => decide (k = 0))) 0 := by decide
example :
    (QClifford.run (traceHost (fun k => decide (k = 0)))
      (compile bridgeCfg bridgeProg) { next := 0 } QClifford.Store.empty).2 1
      = QStab.evalVar bridgeProg (extractedOutcome bridgeCfg (fun k => decide (k = 0))) 1 := by decide

-- The general bridge theorem, instantiated at this program (every source var, ANY trace):
example (outcome : Nat → Bool) (c : Circuit) (h : compile? bridgeCfg bridgeProg = .ok c)
    (w : Nat) (hw : w < bridgeProg.length) :
    (QClifford.run (traceHost outcome) c { next := 0 } QClifford.Store.empty).2 w
      = QStab.evalVar bridgeProg (extractedOutcome bridgeCfg outcome) w :=
  compile?_trace_evalVar h outcome w hw

end Compiler.QStab2QClifford
