/-
  Compiler.LS.SyndromeRounds — a GENERIC repeated-syndrome-extraction LS chunk.

  Repeated rounds of stabilizer measurement are the backbone of every QEC memory /
  growth / idling stage.  This module builds them GENERICALLY (NOT hardcoded for Gidney):
  given a patch size, a list of stabilizer supports, and a round count, it emits ACTUAL LS
  `meas` ops (one per stabilizer per round) — which lower 1:1 to real QStab `prop`
  instructions — plus REPEAT DETECTORS that compare each stabilizer's outcome between
  ADJACENT rounds (the `rec[-1] ⊕ rec[-1-k]` Stim pattern).

  HONESTY: the stabilizer supports / layout are SUPPLIED by the caller; this module does
  NOT claim they are Gidney's exact growth/escape rounds (that needs supports sourced from
  the paper/code).  No fault-distance / decoder soundness is claimed.  Mathlib-free.
-/
import Compiler.LS.Chunk

namespace Compiler.LS
open QStab Physical

/-- The specification of a repeated syndrome-extraction block: the patch size, the
    stabilizer supports to measure each round, the round count, a detector-name prefix, and
    the measurement kind (`mpp` product vs `destructive` — usually `mpp` for non-demolition
    stabilizer rounds). -/
structure SyndromeRoundSpec where
  numQubits   : Nat
  stabilizers : List SPauli
  rounds      : Nat
  namePrefix  : String   := "synd"
  measKind    : MeasKind := .mpp
  deriving Repr

/-- The LS ops of `spec`: per round, one `meas` per stabilizer (binding the next QVar), then
    — for every round after the first — a REPEAT DETECTOR per stabilizer comparing this
    round's outcome var `r·k+i` to the previous round's `(r-1)·k+i`.  Detector coordinates
    are `(stabilizer-index, round)`. -/
def syndromeRoundOps (spec : SyndromeRoundSpec) : List LSOp :=
  let k := spec.stabilizers.length
  (List.range spec.rounds).flatMap (fun r =>
    spec.stabilizers.map (fun s => LSOp.meas none s spec.measKind)
    ++ (if r == 0 then [] else
        (List.range k).map (fun i =>
          LSOp.detector { name   := s!"{spec.namePrefix}-r{r}-s{i}"
                          srcs   := [r * k + i, (r - 1) * k + i]
                          coords := [⟨Int.ofNat i, 1⟩, ⟨Int.ofNat r, 1⟩] })))

/-- **The generic repeated-syndrome-extraction CHUNK.**  Its program performs
    `rounds × |stabilizers|` real stabilizer measurements (→ QStab `prop`s) with adjacent-round
    repeat detectors.  Carries an explicit deferred contract noting the supports are SUPPLIED,
    not Gidney-sourced. -/
def syndromeRoundsChunk (spec : SyndromeRoundSpec) : LSChunk :=
  { name        := s!"{spec.namePrefix}-rounds-{spec.rounds}"
    source      := "generic LS syndrome-extraction rounds (supports SUPPLIED; not sourced from Gidney growth/escape)"
    stage       := "stabilize"
    program     := { numQubits := spec.numQubits, ops := syndromeRoundOps spec, flows := [] }
    obligations := [ .contract ⟨.custom "syndrome-rounds",
        s!"{spec.rounds} generic syndrome-extraction rounds over {spec.stabilizers.length} stabilizers; supports/layout are SUPPLIED, NOT proven to be a specific code's growth/escape rounds"⟩ ] }

/-! ## Tests — generic stabilizers (a 2-stabilizer repetition-style block on 3 qubits). -/

def zzA : SPauli := [(0, .Z), (1, .Z)]
def zzB : SPauli := [(1, .Z), (2, .Z)]

-- 0 rounds → an EMPTY checked chunk (no measurements, trivially checks):
def rounds0 : LSChunk := syndromeRoundsChunk { numQubits := 3, stabilizers := [zzA, zzB], rounds := 0 }
example : rounds0.measurements = [] := by decide
example : rounds0.checks? = true := by decide
example : (lower rounds0.program).dataflow.length = 0 := by decide

-- 1 round → one measurement per stabilizer (2), no repeat detectors, and it checks:
def rounds1 : LSChunk := syndromeRoundsChunk { numQubits := 3, stabilizers := [zzA, zzB], rounds := 1 }
example : rounds1.measurements.length = 2 := by decide
example : rounds1.detectors.length = 0 := by decide
example : rounds1.checks? = true := by decide
example : (lower rounds1.program).dataflow.length = 2 := by decide

-- 2 rounds → 4 real `prop` measurements + 2 repeat detectors comparing ADJACENT rounds:
def rounds2 : LSChunk := syndromeRoundsChunk { numQubits := 3, stabilizers := [zzA, zzB], rounds := 2 }
example : rounds2.measurements.length = 4 := by decide
example : rounds2.measurements = [zzA, zzB, zzA, zzB] := by decide
example : rounds2.detectors.length = 2 := by decide
-- the repeat detectors compare round 1's var to round 0's var for each stabilizer (k=2):
example : rounds2.detectors.map (·.srcs) = [[2, 0], [3, 1]] := by decide
example : rounds2.checks? = true := by decide
-- the lowered QStab dataflow contains the expected number of REAL `.prop` instructions (4):
example : (lower rounds2.program).dataflow.length = 4 := by decide
example : (lower rounds2.program).dataflow = [ .prop none (ofString "ZZI"), .prop none (ofString "IZZ")
                                             , .prop none (ofString "ZZI"), .prop none (ofString "IZZ") ] := by decide
-- 3 rounds → 6 props + 4 repeat detectors (2 per inter-round seam):
def rounds3 : LSChunk := syndromeRoundsChunk { numQubits := 3, stabilizers := [zzA, zzB], rounds := 3 }
example : (lower rounds3.program).dataflow.length = 6 := by decide
example : rounds3.detectors.length = 4 := by decide
example : rounds3.checks? = true := by decide

end Compiler.LS
