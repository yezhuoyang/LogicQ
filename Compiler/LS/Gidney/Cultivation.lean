/-
  Compiler.LS.Gidney.Cultivation — the d=3 double-cat / H_XY cultivation check chunk.

  IMPORTANT (semantic correction): Gidney builds the chunk with
  `gen.Chunk.from_circuit_with_mpp_boundaries` (cultivation_stage.py:12), which SPLITS the
  leading/trailing boundary `MPP`s into FLOWS / interfaces and keeps only the BODY circuit
  (gen/_chunk/_chunk.py:265).  So the real `gen.Chunk` is NOT the raw 21-measurement Stim
  text — it has **7 body measurements** (the `MX` cat readouts), **6 detectors**, and
  **8 flows** (the boundary `Y`/`X`/`Z` stabilizers + the logical `Y` observable).

  This module therefore provides TWO things, kept distinct:
    * `d3DoubleCatRawProgram` — the RAW Stim transcription (pre-chunk; 21 measurements
      incl. the boundary MPPs).  Faithful to the circuit TEXT, NOT to the gen.Chunk.
    * `d3DoubleCatCheck : LSChunk` — the REAL `gen.Chunk`: the 7-measurement body + its 6
      detectors + the 8 flows, ALL extracted from the local `gen` ORACLE
      (`PYTHONPATH=…/src; make_chunk_d3_double_cat_check()`), not hand-guessed.

  HONESTY: the body measurements are all `MX` (single-`X`, extractable) — the non-Pauli
  `Y`-parity is a FLOW boundary, not a body measurement.  Flow STABILIZER-soundness is
  deferred (`flowSemantics`); centres/obs_key/sign are preserved as metadata.  No
  flow/fault/decoder correctness is claimed.  Mathlib-free.
-/
import Compiler.LS.Gidney.Basic
import Compiler.LS.Extract
import Compiler.LS.LowerQStab

namespace Compiler.LS.Gidney
open Compiler.LS QStab Physical

set_option maxRecDepth 6000

/-! ## §1. Pauli supports (13 qubits, 0–12; cat qubit = 5). -/

def yParity  : SPauli := [(0, .Y), (8, .Y), (11, .Y), (10, .Y), (7, .Y), (5, .Y), (3, .Y)]
def xCheck1  : SPauli := [(8, .X), (0, .X), (3, .X), (5, .X)]       -- support {0,3,5,8}
def xCheck2  : SPauli := [(3, .X), (5, .X), (10, .X), (7, .X)]      -- support {3,5,7,10}
def xCheck2R : SPauli := [(7, .X), (10, .X), (5, .X), (3, .X)]      -- line 122 source order (same support)
def xCheck3  : SPauli := [(11, .X), (8, .X), (5, .X), (10, .X)]     -- support {5,8,10,11}
def zCheck1  : SPauli := [(8, .Z), (0, .Z), (3, .Z), (5, .Z)]
def zCheck2  : SPauli := [(7, .Z), (10, .Z), (5, .Z), (3, .Z)]
def zCheck3  : SPauli := [(11, .Z), (8, .Z), (5, .Z), (10, .Z)]

/-- The dense Y-parity Pauli string over the 13-qubit patch (Y on {0,3,5,7,8,10,11}). -/
def yParityDense : QStab.PauliString := ofString "YIIYIYIYYIYYI"

/-- The patch GEOMETRY: `QUBIT_COORDS` (lines 13–25) + the three `POLYGON` tiles
    (lines 26–28).  Metadata only — no geometry semantics are claimed. -/
def d3Geometry : Geometry :=
  { coords :=
      [ ⟨0, 0, 0⟩, ⟨1, 0, 1⟩, ⟨2, 1, 0⟩, ⟨3, 1, 1⟩, ⟨4, 2, 0⟩, ⟨5, 2, 1⟩, ⟨6, 2, 2⟩,
        ⟨7, 2, 3⟩, ⟨8, 3, 0⟩, ⟨9, 3, 1⟩, ⟨10, 3, 2⟩, ⟨11, 4, 0⟩, ⟨12, 4, 1⟩ ]
    polygons :=
      [ ⟨"POLYGON(0,0,1,0.25)", [8, 11, 10, 5]⟩
      , ⟨"POLYGON(0,1,0,0.25)", [7, 10, 5, 3]⟩
      , ⟨"POLYGON(1,0,0,0.25)", [3, 5, 8, 0]⟩ ] }

/-! ## §2. The RAW Stim circuit (PRE-CHUNK — NOT the gen.Chunk). -/

/-- RAW first-round ops (lines 30–77): 7 boundary MPPs + cat round.  PRE-CHUNK. -/
def rawPrefixOps : List LSOp :=
  [ .meas none yParity, .meas none xCheck1, .meas none xCheck2, .meas none xCheck3      -- vars 0–3
  , .meas none zCheck1, .meas none zCheck2, .meas none zCheck3                          -- vars 4–6
  , .prepPlus 12, .prepPlus 9, .prepPlus 4, .prepPlus 2, .prepPlus 6, .prepPlus 1
  , .sDag 0, .sDag 3, .sDag 5, .sDag 7, .sDag 8, .sDag 10, .sDag 11
  , .cnot 1 0, .cnot 9 8, .cnot 6 7, .cnot 4 5, .cnot 2 3, .cnot 12 11
  , .cnot 3 1, .cnot 5 6, .cnot 9 12, .cnot 5 3, .cnot 9 10, .cnot 5 9
  , .meas none [(5, .X)] .destructive                                                   -- var 7
  , .detector { name := "cat-check", srcs := [7, 0], coords := [0, 0, 0] } ]

/-- RAW second-round ops (lines 78–138): reverse round + repeat syndromes + observable. PRE-CHUNK. -/
def rawSecondRoundOps : List LSOp :=
  [ .prepPlus 5, .cnot 5 9, .cnot 5 3, .cnot 9 10, .cnot 3 1, .cnot 5 6, .cnot 9 12
  , .cnot 1 0, .cnot 9 8, .cnot 6 7, .cnot 12 11, .cnot 4 5, .cnot 2 3
  , .s 5, .s 10, .s 11, .s 8, .s 7, .s 3, .s 0
  , .meas none [(12, .X)] .destructive, .meas none [(9, .X)] .destructive               -- vars 8,9
  , .meas none [(4, .X)] .destructive, .meas none [(2, .X)] .destructive                -- vars 10,11
  , .meas none [(6, .X)] .destructive, .meas none [(1, .X)] .destructive                -- vars 12,13
  , .detector { name := "d-4-1-1", srcs := [8] }, .detector { name := "d-3-1-1", srcs := [9] }
  , .detector { name := "d-2-1-1", srcs := [10, 7] }, .detector { name := "d-1-0-1", srcs := [11] }
  , .detector { name := "d-2-2-1", srcs := [12] }, .detector { name := "d-0-1-1", srcs := [13] }
  , .meas none xCheck1,  .detector { name := "r-3-0-2", srcs := [14, 7, 1] }            -- var 14
  , .meas none xCheck2R, .detector { name := "r-1-1-3", srcs := [15, 7, 2] }            -- var 15
  , .meas none xCheck3,  .detector { name := "r-4-0-4", srcs := [16, 7, 3] }            -- var 16
  , .meas none zCheck1,  .detector { name := "r-3-0-5", srcs := [17, 4] }               -- var 17
  , .meas none zCheck2,  .detector { name := "r-2-3-6", srcs := [18, 5] }               -- var 18
  , .meas none zCheck3,  .detector { name := "r-4-0-7", srcs := [19, 6] }               -- var 19
  , .meas none yParity, .observable "raw-Y-parity" [20, 13, 12, 9, 8] ]                 -- var 20

/-- The RAW Stim transcription (PRE-CHUNK): 21 measurements incl. boundary MPPs. -/
def d3DoubleCatRawProgram : Program :=
  { numQubits := 13, ops := rawPrefixOps ++ rawSecondRoundOps }

/-! ## §3. The REAL `gen.Chunk` body (7 measurements + 6 detectors), from the oracle. -/

/-- The gen.Chunk BODY ops (the cat-state circuit; the boundary MPPs are NOT here — they
    are flows).  Body measurements: `MX 5`=var 0, then `MX 12 9 4 2 6 1`=vars 1–6. -/
def bodyOps : List LSOp :=
  [ .prepPlus 12, .prepPlus 9, .prepPlus 4, .prepPlus 2, .prepPlus 6, .prepPlus 1, .tick   -- RX 12 9 4 2 6 1
  , .sDag 0, .sDag 3, .sDag 5, .sDag 7, .sDag 8, .sDag 10, .sDag 11, .tick                 -- S_DAG 0 3 5 7 8 10 11
  , .cnot 1 0, .cnot 9 8, .cnot 6 7, .cnot 4 5, .cnot 2 3, .cnot 12 11, .tick              -- CX 1 0 9 8 6 7 4 5 2 3 12 11
  , .cnot 3 1, .cnot 5 6, .cnot 9 12, .tick                                                -- CX 3 1 5 6 9 12
  , .cnot 5 3, .cnot 9 10, .tick                                                           -- CX 5 3 9 10
  , .cnot 5 9, .tick                                                                       -- CX 5 9
  , .meas none [(5, .X)] .destructive, .tick                                               -- MX 5   → body var 0
  , .prepPlus 5, .tick                                                                     -- RX 5
  , .cnot 5 9, .tick                                                                       -- CX 5 9
  , .cnot 5 3, .cnot 9 10, .tick                                                           -- CX 5 3 9 10
  , .cnot 3 1, .cnot 5 6, .cnot 9 12, .tick                                                -- CX 3 1 5 6 9 12
  , .cnot 1 0, .cnot 9 8, .cnot 6 7, .cnot 12 11, .cnot 4 5, .cnot 2 3, .tick              -- CX 1 0 9 8 6 7 12 11 4 5 2 3
  , .s 5, .s 10, .s 11, .s 8, .s 7, .s 3, .s 0, .tick                                      -- S 5 10 11 8 7 3 0
  , .meas none [(12, .X)] .destructive                                                     -- MX 12  → var 1
  , .meas none [(9, .X)]  .destructive                                                     -- MX 9   → var 2
  , .meas none [(4, .X)]  .destructive                                                     -- MX 4   → var 3
  , .meas none [(2, .X)]  .destructive                                                     -- MX 2   → var 4
  , .meas none [(6, .X)]  .destructive                                                     -- MX 6   → var 5
  , .meas none [(1, .X)]  .destructive                                                     -- MX 1   → var 6
    -- the 6 body detectors (rec → body-var: rec[-6]=1, rec[-5]=2, rec[-4]=3, rec[-7]=0, rec[-3]=4, rec[-2]=5, rec[-1]=6)
  , .detector { name := "d-4-1-1", srcs := [1],    coords := [4, 1, 1] }
  , .detector { name := "d-3-1-1", srcs := [2],    coords := [3, 1, 1] }
  , .detector { name := "d-2-1-1", srcs := [3, 0], coords := [2, 1, 1] }
  , .detector { name := "d-1-0-1", srcs := [4],    coords := [1, 0, 1] }
  , .detector { name := "d-2-2-1", srcs := [5],    coords := [2, 2, 1] }
  , .detector { name := "d-0-1-1", srcs := [6],    coords := [0, 1, 1] } ]

/-- The 8 flows, EXACTLY as the gen oracle reports them (`stage=cultivation` on all):
    the incoming `Y`-parity (consumed by the cat measurement, body var 0); the three
    `X`-checks passing through (also using body var 0); the three `Z`-checks passing
    through (no body measurement); and the outgoing logical `Y`-parity observable
    (`obs_key=0`, body vars [1,2,5,6]).  Centres are the exact rational centroids. -/
def cultFlag : List String := ["stage=cultivation"]

def d3DoubleCatFlows : List Flow :=
  [ { tag := "in:Y-parity",  input := yParity, output := [],      vars := [0],       flags := cultFlag, center := some (⟨15, 7⟩, ⟨1, 1⟩), status := .structural }
  , { tag := "X1-passthru",  input := xCheck1, output := xCheck1, vars := [0],       flags := cultFlag, center := some (⟨3, 2⟩, ⟨1, 2⟩),  status := .structural }
  , { tag := "X2-passthru",  input := xCheck2, output := xCheck2, vars := [0],       flags := cultFlag, center := some (⟨2, 1⟩, ⟨7, 4⟩),  status := .structural }
  , { tag := "X3-passthru",  input := xCheck3, output := xCheck3, vars := [0],       flags := cultFlag, center := some (⟨3, 1⟩, ⟨3, 4⟩),  status := .structural }
  , { tag := "Z1-passthru",  input := zCheck1, output := zCheck1, vars := [],        flags := cultFlag, center := some (⟨3, 2⟩, ⟨1, 2⟩),  status := .structural }
  , { tag := "Z2-passthru",  input := zCheck2, output := zCheck2, vars := [],        flags := cultFlag, center := some (⟨2, 1⟩, ⟨7, 4⟩),  status := .structural }
  , { tag := "Z3-passthru",  input := zCheck3, output := zCheck3, vars := [],        flags := cultFlag, center := some (⟨3, 1⟩, ⟨3, 4⟩),  status := .structural }
  , { tag := "out:Y-parity", input := [],      output := yParity, vars := [1, 2, 5, 6], flags := cultFlag, obsKey := some 0, center := some (⟨15, 7⟩, ⟨1, 1⟩), status := .structural } ]

/-- The gen.Chunk BODY program: 7-measurement body + 6 detectors + 8 flows. -/
def d3DoubleCatBodyProgram : Program :=
  { numQubits := 13, ops := bodyOps, flows := d3DoubleCatFlows }

/-- **The REAL d=3 double-cat check `gen.Chunk`** (7 body measurements, 6 detectors,
    8 flows), extracted from the local gen oracle. -/
def d3DoubleCatCheck : LSChunk :=
  { name        := "d3-double-cat-check"
    source      := "make_chunk_d3_double_cat_check → from_circuit_with_mpp_boundaries (cultivation_stage.py:11-140; arXiv 2409.17595); flows from the local gen oracle"
    stage       := "cultivation"
    program     := d3DoubleCatBodyProgram
    geometry    := d3Geometry
    obligations :=
      -- the body is all-MX (single-X, EXTRACTABLE) ⇒ no `notExtractable`; the non-Pauli
      -- Y-parity is a FLOW boundary, not a body measurement.  Flow soundness is deferred.
      extractObligations d3DoubleCatBodyProgram.dataflow
      ++ [ .contract ⟨.stageChunk "cultivation.double-cat-check",
             "the d3 double-cat CHECK chunk only — injection/growth/stabilization/escape chunks are separate; flow stabilizer-soundness is deferred (flowSemantics)"⟩ ] }

/-! ## §4. Tests — the chunk matches the gen ORACLE facts. -/

-- ORACLE: 7 body measurements, 6 detectors, 8 flows; the chunk checks:
example : d3DoubleCatCheck.checks? = true := by decide
example : d3DoubleCatCheck.measurements.length = 7 := by decide
example : d3DoubleCatCheck.detectors.length = 6 := by decide
example : d3DoubleCatCheck.flows.length = 8 := by decide

-- the body measurements are all single-qubit `MX` (X-basis) readouts at {5,12,9,4,2,6,1}:
example : d3DoubleCatCheck.measurements = [[(5, .X)], [(12, .X)], [(9, .X)], [(4, .X)], [(2, .X)], [(6, .X)], [(1, .X)]] := by decide
-- the 6 body detectors reference the body measurement vars (NOT the raw circuit indices):
example : d3DoubleCatCheck.detectors.map (·.srcs) = [[1], [2], [3, 0], [4], [5], [6]] := by decide

-- every flow carries `stage=cultivation` (matching `with_flag_added_to_all_flows`, line 140):
example : d3DoubleCatCheck.flows.all (fun f => f.flags.contains "stage=cultivation") = true := by decide
-- the INCOMING Y-parity flow: start = Y-parity, end = ∅, measured by body var 0:
example : (d3DoubleCatCheck.flows.filter (fun f => f.tag == "in:Y-parity")).map (fun f => (f.input, f.output, f.vars))
    = [(yParity, [], [0])] := by decide
-- the OUTGOING logical Y-parity OBSERVABLE flow: obs_key 0, end = Y-parity, body vars [1,2,5,6]:
example : (d3DoubleCatCheck.flows.filter (fun f => f.obsKey == some 0)).map (fun f => (f.output, f.vars))
    = [(yParity, [1, 2, 5, 6])] := by decide
-- the X-checks pass through (start = end), using body var 0; the Z-checks use no body var:
example : (d3DoubleCatCheck.flows.filter (fun f => f.tag == "X1-passthru")).map (fun f => (f.input, f.output, f.vars))
    = [(xCheck1, xCheck1, [0])] := by decide
example : (d3DoubleCatCheck.flows.filter (fun f => f.tag == "Z1-passthru")).map (fun f => f.vars) = [[]] := by decide
-- the exact rational flow CENTRE is preserved (the incoming Y-parity centroid is 15/7 + 1·i):
example : (d3DoubleCatCheck.flows.filter (fun f => f.tag == "in:Y-parity")).map (fun f => f.center)
    = [some (⟨15, 7⟩, ⟨1, 1⟩)] := by decide

-- LOWERING preserves the chunk's dataflow (the proven `lower_dataflow`, applied):
example : (lower d3DoubleCatBodyProgram).dataflow = d3DoubleCatBodyProgram.dataflow := lower_dataflow _
example : (lower d3DoubleCatBodyProgram).wf = true := by decide

-- MEAS-KIND through the lowering sidecar: all 7 body measurements are DESTRUCTIVE `MX`, 0 MPP:
example : (lowerChunkCheckedWithExtract d3DoubleCatCheck).toOption.map (fun lc => lc.sidecar.countMeasKind .destructive) = some 7 := by decide
example : (lowerChunkCheckedWithExtract d3DoubleCatCheck).toOption.map (fun lc => lc.sidecar.countMeasKind .mpp) = some 0 := by decide

-- EXTRACTABILITY (corrected): the body has NO non-extractable measurement (all single-X);
-- the non-Pauli Y-parity is a FLOW boundary, not a body measurement:
example : (lowerChunkCheckedWithExtract d3DoubleCatCheck).toOption.map
    (fun lc => lc.obligations.any (fun o => match o with | .notExtractable _ _ => true | _ => false)) = some false := by decide
-- …and every flow still emits its explicit (deferred) semantic-flow obligation:
example : (lowerChunkCheckedWithExtract d3DoubleCatCheck).toOption.map
    (fun lc => lc.obligations.any (fun o => match o with | .flowSemantics _ => true | _ => false)) = some true := by decide
-- …and the chunk-level CHECK-only contract is merged in:
example : (lowerChunkCheckedWithExtract d3DoubleCatCheck).toOption.map
    (fun lc => lc.obligations.any (fun o => match o with
      | .contract c => decide (c.kind = .stageChunk "cultivation.double-cat-check") | _ => false)) = some true := by decide

-- GEOMETRY preserved (13 coords; qubit 7 at (2,3); 3 polygon tiles):
example : d3DoubleCatCheck.geometry.numCoords = 13 := by decide
example : d3DoubleCatCheck.geometry.coordOf? 7 = some (2, 3) := by decide
example : d3DoubleCatCheck.geometry.polygons.length = 3 := by decide

/-! ## §5. The RAW transcription is DISTINCT from the chunk (21 vs 7 measurements). -/

-- the raw Stim text has 21 measurements (incl. the boundary MPPs) and checks as a circuit…
example : d3DoubleCatRawProgram.measurements.length = 21 := by decide
example : (checks? d3DoubleCatRawProgram) = true := by decide
-- …but it is NOT the gen.Chunk (the chunk has 7 body measurements + 8 flows):
example : d3DoubleCatRawProgram.measurements.length ≠ d3DoubleCatCheck.measurements.length := by decide
example : d3DoubleCatRawProgram.flows.length = 0 := by decide

end Compiler.LS.Gidney
