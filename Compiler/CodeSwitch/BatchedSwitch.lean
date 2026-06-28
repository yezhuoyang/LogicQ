/-
  Compiler.CodeSwitch.BatchedSwitch — the BATCH AXIS for high-rate batched operations
  (2510.06159).

  Batched code switching routes the i-th logical of the j-th Q1 source block to the j-th
  logical of the i-th Q2 target block:

        P̄_i(Q1^(j))  ⟶  P̄_j(Q2^(i))      i.e.  (block j, logical i) ↦ (block i, logical j)

  — a literal (block-index, logical-index) TRANSPOSE.  Inactive Q2 targets are filled with
  DUMMY blocks.  This module models the route as a `LocMap` over `LQubit` names and PROVES
  that a well-formed batched switch routes every active source logical to its transpose
  (the carrier/name lookup changes exactly as `(j,i) ↦ (i,j)`).

  HONEST SCOPE: this is the ADDRESSING/routing layer (structural, recomputed).  The
  subsystem fault-distance `d ≥ min(d₁,d₂)` (2510.06159 Supp. II) is NOT GF(2)-recomputable
  and stays a deferred obligation; the feedback CNOT/CZ pattern is typed by
  `Compiler.ChainQ2Mixed.Frame` (operational rule deferred).
-/
import Compiler.Mixed.Lower.LocMap
import TypeChecker.Core.Error
import TypeChecker.Core.Block

namespace Compiler.CodeSwitch
open Compiler TypeChecker Logical

/-! ## §BCS.1. The transpose route. -/

/-- The batched-code-switch route on a logical address: `(block j, logical i) ↦
    (block i, logical j)` — swap the block index and the logical index. -/
def routeLQubit (q : LQubit) : LQubit := ⟨q.idx, q.blk⟩

/-- The route is the literal `(j,i) ↦ (i,j)` transpose. -/
theorem routeLQubit_transpose (j i : Nat) : routeLQubit ⟨j, i⟩ = ⟨i, j⟩ := rfl

/-- The route is an involution (transposing twice returns the original address). -/
theorem routeLQubit_involutive (q : LQubit) : routeLQubit (routeLQubit q) = q := rfl

/-! ## §BCS.2. The batched-code-switch spec + its route LocMap. -/

/-- A batched code switch: `k2` source blocks of `Q1` (each with `k1` logicals) routed to
    `k1` target blocks of `Q2`; `sources` are the ACTIVE source logical addresses and
    `dummies` are the inactive Q2 blocks filled with dummy codes. -/
structure BatchedCodeSwitchSpec where
  k1      : Nat
  k2      : Nat
  sources : List LQubit
  dummies : List Logical.BlockId
  deriving Repr

/-- The route as a `LocMap`: every active source `⟨j,i⟩` relocates to its transpose
    `⟨i,j⟩` (so later name/carrier lookups resolve through the route). -/
def BatchedCodeSwitchSpec.routeMap (s : BatchedCodeSwitchSpec) : LocMap :=
  s.sources.map (fun q => (q, routeLQubit q))

/-- The active SOURCE block ids (`Q1^j`) a route touches. -/
def BatchedCodeSwitchSpec.sourceBlocks (s : BatchedCodeSwitchSpec) : List Logical.BlockId :=
  s.sources.map (fun q => q.blk)

/-- Well-formed: exactly `k1·k2` active source logicals, all distinct, each `⟨j,i⟩` in range
    (`j < k2` source block, `i < k1` logical); the route is COLLISION-FREE (no two sources map
    to the same target `⟨i,j⟩`); and the DUMMY/inactive blocks are distinct, out of the active
    source-block range (`≥ k2`), and disjoint from every active source data block. -/
def BatchedCodeSwitchSpec.wf (s : BatchedCodeSwitchSpec) : Bool :=
  decide (s.sources.length = s.k1 * s.k2) &&
  s.sources.Nodup &&
  (s.sources.map routeLQubit).Nodup &&
  s.sources.all (fun q => decide (q.blk < s.k2) && decide (q.idx < s.k1)) &&
  s.dummies.Nodup &&
  s.dummies.all (fun d => decide (d ≥ s.k2)) &&
  s.dummies.all (fun d => ! s.sourceBlocks.contains d)

structure CheckedBatchedCodeSwitch where
  spec : BatchedCodeSwitchSpec
  wf   : spec.wf = true

/-- **Check a batched code switch** (structural routing well-formedness). -/
def checkBatchedCodeSwitch? (s : BatchedCodeSwitchSpec) :
    Except TypeError CheckedBatchedCodeSwitch :=
  if h : s.wf = true then .ok { spec := s, wf := h }
  else .error (.certFailed "batched code switch: route is not a well-formed k1·k2 reindex")

/-! ## §BCS.3. Routing preservation. -/

/-- **Routing preservation.**  Every active source logical `q = ⟨j,i⟩` is routed by the
    `LocMap` to its transpose `⟨i,j⟩` (the pair is in the route map). -/
theorem batchRoute_maps_transpose (s : BatchedCodeSwitchSpec) {q : LQubit} (hq : q ∈ s.sources) :
    (q, routeLQubit q) ∈ s.routeMap :=
  List.mem_map.mpr ⟨q, hq, rfl⟩

/-- **A checked batched switch preserves the batch logical routing**: every active source
    `⟨j,i⟩` maps to `⟨i,j⟩` in the route. -/
theorem checkBatchedCodeSwitch?_preservesRoute {s : BatchedCodeSwitchSpec}
    {c : CheckedBatchedCodeSwitch} (_h : checkBatchedCodeSwitch? s = .ok c)
    {q : LQubit} (hq : q ∈ s.sources) : (q, ⟨q.idx, q.blk⟩) ∈ s.routeMap :=
  batchRoute_maps_transpose s hq

/-! ## §BCS.4. Tests. -/

-- a 2×2 batched switch: k1 = k2 = 2; sources = {⟨0,0⟩,⟨0,1⟩,⟨1,0⟩,⟨1,1⟩}.
def bcs22 : BatchedCodeSwitchSpec :=
  { k1 := 2, k2 := 2, sources := [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], dummies := [] }
example : bcs22.wf = true := by decide
example : ok? (checkBatchedCodeSwitch? bcs22) = true := by decide

-- the carrier lookup changes EXACTLY as (j,i) ↦ (i,j):
example : bcs22.routeMap.loc ⟨0, 1⟩ = ⟨1, 0⟩ := by decide      -- block 0, logical 1 ↦ block 1, logical 0
example : bcs22.routeMap.loc ⟨1, 0⟩ = ⟨0, 1⟩ := by decide      -- block 1, logical 0 ↦ block 0, logical 1
example : bcs22.routeMap.loc ⟨1, 1⟩ = ⟨1, 1⟩ := by decide      -- diagonal fixed
-- the route is the transpose, definitionally:
example (j i : Nat) : routeLQubit ⟨j, i⟩ = ⟨i, j⟩ := rfl

-- NEGATIVE — a malformed batched switch (wrong active count k1·k2) is REJECTED:
def bcsBadCount : BatchedCodeSwitchSpec := { bcs22 with sources := [⟨0, 0⟩] }   -- 1 ≠ 2·2
example : ok? (checkBatchedCodeSwitch? bcsBadCount) = false := by decide
-- NEGATIVE — an out-of-range source (block index ≥ k2) is REJECTED:
def bcsOOR : BatchedCodeSwitchSpec := { bcs22 with sources := [⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨5, 1⟩] }
example : ok? (checkBatchedCodeSwitch? bcsOOR) = false := by decide
-- dummy/inactive blocks are representable (out of the active source-block range, distinct):
def bcsDummy : BatchedCodeSwitchSpec := { bcs22 with dummies := [2, 3] }
example : ok? (checkBatchedCodeSwitch? bcsDummy) = true := by decide

-- NEGATIVE — DUPLICATE dummy ids are REJECTED:
example : ok? (checkBatchedCodeSwitch? { bcs22 with dummies := [2, 2] }) = false := by decide
-- NEGATIVE — a dummy COLLIDING with an active source data block (id < k2) is REJECTED:
example : ok? (checkBatchedCodeSwitch? { bcs22 with dummies := [0] }) = false := by decide
example : ok? (checkBatchedCodeSwitch? { bcs22 with dummies := [1, 2] }) = false := by decide  -- 1 is a source block
-- NEGATIVE — a ROUTE COLLISION (two distinct sources mapping to the same target ⟨i,j⟩) is
-- REJECTED.  ⟨0,1⟩↦⟨1,0⟩ and ⟨1,0⟩↦⟨0,1⟩ are fine; but a NON-transpose-consistent set with a
-- collision fails the `(sources.map routeLQubit).Nodup` guard:
def bcsCollide : BatchedCodeSwitchSpec :=
  { k1 := 2, k2 := 2, sources := [⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], dummies := [] }  -- ⟨0,0⟩ twice
example : ok? (checkBatchedCodeSwitch? bcsCollide) = false := by decide

-- the post-switch loc map RELOCATES each ChainQ logical (j,i) to its target carrier (i,j):
example : bcs22.routeMap.loc ⟨0, 1⟩ = ⟨1, 0⟩ := by decide

/-! ## §BCS.5. ENV-BOUND batched code switch — the route must resolve in a `TypedEnv`.

    A raw `BatchedCodeSwitchSpec` is just a reindex; a GENUINE batched switch additionally
    requires the `k2` source blocks `Q1^j` and `k1` target blocks `Q2^i` to EXIST, be LIVE,
    and carry the right logical counts in the current `TypedEnv`, and the dummy blocks to
    exist + be live.  This rejects a "huge route with no env behind it". -/

/-- Block `bid` exists in `Γ`, is live, and has at least `k` logical qubits. -/
def liveWithLogicals (Γ : TypedEnv) (bid : Nat) (k : Nat) : Bool :=
  match Γ.block? bid with
  | some tb => tb.block.live && decide (k ≤ tb.block.lx.length)
  | none    => false

/-- A batched code switch BOUND to `Γ`: structurally well-formed, and the `k2` source +
    `k1` target blocks exist/live with the right logical counts, dummies exist/live. -/
structure BatchedCodeSwitchFor (Γ : TypedEnv) where
  spec    : BatchedCodeSwitchSpec
  specWf  : spec.wf = true
  srcLive : (List.range spec.k2).all (fun j => liveWithLogicals Γ j spec.k1) = true
  tgtLive : (List.range spec.k1).all (fun i => liveWithLogicals Γ i spec.k2) = true
  dumLive : spec.dummies.all (fun d => liveWithLogicals Γ d 0) = true

/-- **Check an env-bound batched code switch.**  Rejects a route whose source/target blocks
    are missing/dead/under-sized in `Γ` (a "raw route with no env"). -/
def checkBatchedCodeSwitchFor? (Γ : TypedEnv) (s : BatchedCodeSwitchSpec) :
    Except TypeError (BatchedCodeSwitchFor Γ) :=
  if h1 : s.wf = true then
    if h2 : (List.range s.k2).all (fun j => liveWithLogicals Γ j s.k1) = true then
      if h3 : (List.range s.k1).all (fun i => liveWithLogicals Γ i s.k2) = true then
        if h4 : s.dummies.all (fun d => liveWithLogicals Γ d 0) = true then
          .ok { spec := s, specWf := h1, srcLive := h2, tgtLive := h3, dumLive := h4 }
        else .error (.certFailed "batched code switch: a dummy block is missing or DEAD in the env")
      else .error (.certFailed "batched code switch: a target block Q2^i is missing/dead/under-sized")
    else .error (.certFailed "batched code switch: a source block Q1^j is missing/dead/under-sized")
  else .error (.certFailed "batched code switch: route is not a well-formed k1·k2 reindex")

/-- **An env-bound checked switch relocates each named logical `(Q1^j, i)` to `(Q2^i, j)`**
    in the post-switch route map. -/
theorem checkBatchedCodeSwitchFor?_preservesRoute {Γ : TypedEnv} {s : BatchedCodeSwitchSpec}
    {c : BatchedCodeSwitchFor Γ} (_h : checkBatchedCodeSwitchFor? Γ s = .ok c)
    {q : LQubit} (hq : q ∈ s.sources) : (q, ⟨q.idx, q.blk⟩) ∈ s.routeMap :=
  batchRoute_maps_transpose s hq

-- a 2-block env (each block has 2 logicals) backs a 2×2 batched switch:
def b2 : Block :=
  { n := 2, stab := [], lx := [[true, false, false, false], [false, true, false, false]],
    lz := [[false, false, true, false], [false, false, false, true]] }
def bcsEnv : TypedEnv :=
  match TypedEnv.ofEnv? { blocks := [b2, b2] } with | .ok Γ => Γ | .error _ => { blocks := [] }

example : ok? (checkBatchedCodeSwitchFor? bcsEnv bcs22) = true := by decide
-- NEGATIVE — a RAW route with NO env behind it (empty env) is REJECTED:
example : ok? (checkBatchedCodeSwitchFor? { blocks := [] } bcs22) = false := by decide
-- NEGATIVE — a MISSING target/source block (env has only 1 block, route needs 2) is REJECTED:
example : ok? (checkBatchedCodeSwitchFor? (match TypedEnv.ofEnv? { blocks := [b2] } with | .ok Γ => Γ | .error _ => { blocks := [] }) bcs22) = false := by decide
-- NEGATIVE — a dummy block missing in the env is REJECTED:
example : ok? (checkBatchedCodeSwitchFor? bcsEnv { bcs22 with dummies := [7] }) = false := by decide
-- NEGATIVE — a DEAD dummy block (exists but `live := false`) is REJECTED:
def b2dead : Block := { b2 with live := false }
def bcsEnvDead : TypedEnv :=
  match TypedEnv.ofEnv? { blocks := [b2, b2, b2dead] } with | .ok Γ => Γ | .error _ => { blocks := [] }
example : ok? (checkBatchedCodeSwitchFor? bcsEnvDead { bcs22 with dummies := [2] }) = false := by decide

end Compiler.CodeSwitch
