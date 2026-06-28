/-
  Compiler.LS.ChunkCompose — GENERIC sequential composition of `List LSChunk`.

  Composes chunks acting on a SHARED physical patch into one LS program: the executable
  body ops are concatenated, and every later chunk's classical-VAR references (detector /
  observable / parity sources, and flow `vars`) are OFFSET by the binding-var count of all
  preceding chunks (so the composed SSA dataflow is consistent).  Geometries and deferred
  obligations are merged; measurement KINDS are preserved (the `meas` ops are copied
  verbatim); and the composed program is run through `LS.check` / chunk-aware lowering.

  Flow interfaces between EVERY adjacent pair are matched STRUCTURALLY (§1): same Pauli
  support, compatible `obsKey`.  This runs on the AUTOMATIC path (`composeChunks` itself),
  so any UNMATCHED interface is recorded as an explicit `flowCompositionDeferred` obligation
  — never silently accepted.  SEMANTIC stabilizer-flow soundness across a seam is NEVER
  claimed (a generic seam obligation is always present too).  Generic over the QEC code /
  layout / protocol.  Mathlib-free.
-/
import Compiler.LS.Chunk

namespace Compiler.LS
open QStab Physical

/-! ## §1a. Var-offsetting primitives. -/

/-- Shift an op's classical-VAR REFERENCES by `off` (the binding sites — `meas`/`parity`
    — are positional and need no rewrite; postselect/stage refer to names, not vars). -/
def LSOp.shiftSrcs (off : Nat) : LSOp → LSOp
  | .detector ann      => .detector { ann with srcs := ann.srcs.map (· + off) }
  | .observable n srcs => .observable n (srcs.map (· + off))
  | .parity srcs       => .parity (srcs.map (· + off))
  | op                 => op

/-- Shift a flow's measurement-index `vars` by `off` (its Pauli support is over shared
    physical qubits and does NOT shift). -/
def Flow.shiftVars (off : Nat) (fl : Flow) : Flow := { fl with vars := fl.vars.map (· + off) }

/-- Merge two patch geometries: union the coordinates (keeping the first placement of each
    qubit) and concatenate the polygon tiles. -/
def Geometry.merge (g1 g2 : Geometry) : Geometry :=
  { coords   := g1.coords ++ g2.coords.filter (fun c => !(g1.coords.any (fun d => d.qubit == c.qubit)))
    polygons := g1.polygons ++ g2.polygons }

/-! ## §1b. Structural flow-INTERFACE matching across a seam. -/

/-- An OUTGOING boundary flow (`∅ → output`): a stabilizer the chunk exports. -/
def Flow.isOutgoing (fl : Flow) : Bool := fl.input.isEmpty && !fl.output.isEmpty
/-- An INCOMING boundary flow (`input → ∅`): a stabilizer the chunk imports. -/
def Flow.isIncoming (fl : Flow) : Bool := !fl.input.isEmpty && fl.output.isEmpty

/-- Membership of a sparse-Pauli factor (qubit + letter), Mathlib-free. -/
def spauliMem (f : PQubit × Pauli) (Q : SPauli) : Bool :=
  Q.any (fun g => g.1 == f.1 && decide (g.2 = f.2))

/-- Two sparse Paulis have the SAME support (same set of `(qubit, letter)` factors).
    Both are duplicate-free, so equal length + mutual inclusion is set equality. -/
def sameSupport (P Q : SPauli) : Bool :=
  P.length == Q.length && P.all (fun f => spauliMem f Q) && Q.all (fun g => spauliMem g P)

/-- **Structural interface match**: an OUTGOING flow of chunk A matches an INCOMING flow of
    the next chunk B iff their boundary Pauli supports are equal and their observable keys
    are compatible (equal — both `none`, or the same logical index).  This is STRUCTURAL
    only; stabilizer-flow SEMANTIC soundness across the seam stays deferred. -/
def Flow.interfaceMatches (aOut bIn : Flow) : Bool :=
  aOut.isOutgoing && bIn.isIncoming &&
  sameSupport aOut.output bIn.input &&
  (aOut.obsKey == bIn.obsKey)

/-- The structural interface report between adjacent chunks `a` (left) and `b` (right):
    which of A's outgoing flows match a B incoming flow, and which are unmatched. -/
structure FlowInterface where
  matched      : List (String × String)   -- (A-outgoing tag, B-incoming tag) structurally matched
  unmatchedOut : List String               -- A outgoing flows with NO B incoming match
  unmatchedIn  : List String               -- B incoming flows with NO A outgoing match
  deriving Repr, DecidableEq

/-- Compute the structural flow interface between adjacent chunks `a` and `b`. -/
def matchInterfaces (a b : LSChunk) : FlowInterface :=
  let aOuts := a.program.flows.filter Flow.isOutgoing
  let bIns  := b.program.flows.filter Flow.isIncoming
  let matched := aOuts.filterMap (fun ao =>
    match bIns.find? (fun bi => Flow.interfaceMatches ao bi) with
    | some bi => some (ao.tag, bi.tag)
    | none    => none)
  let mOut := matched.map Prod.fst
  let mIn  := matched.map Prod.snd
  { matched      := matched
    unmatchedOut := (aOuts.filter (fun ao => !mOut.contains ao.tag)).map (·.tag)
    unmatchedIn  := (bIns.filter (fun bi => !mIn.contains bi.tag)).map (·.tag) }

/-- Are ALL of A's outgoing flows matched by a B incoming flow (and vice-versa)? -/
def interfacesFullyMatched (a b : LSChunk) : Bool :=
  let r := matchInterfaces a b
  r.unmatchedOut.isEmpty && r.unmatchedIn.isEmpty

/-- An explicit deferred obligation for any UNMATCHED interface across a seam — so a flow
    mismatch is RECORDED, never silently accepted. -/
def unmatchedInterfaceObligations (a b : LSChunk) : List Obligation :=
  let r := matchInterfaces a b
  (r.unmatchedOut.map (fun t => Obligation.flowCompositionDeferred
      s!"outgoing flow '{t}' of chunk '{a.name}' has NO structural match in chunk '{b.name}' (recorded, not accepted)"))
  ++ (r.unmatchedIn.map (fun t => Obligation.flowCompositionDeferred
      s!"incoming flow '{t}' of chunk '{b.name}' has NO structural match in chunk '{a.name}' (recorded, not accepted)"))

/-- The unmatched-interface obligations for EVERY adjacent pair in a chunk list (the
    automatic-path interface check). -/
def allAdjacentUnmatchedObligations : List LSChunk → List Obligation
  | a :: b :: rest => unmatchedInterfaceObligations a b ++ allAdjacentUnmatchedObligations (b :: rest)
  | _              => []

/-! ## §2. Generic composition (the automatic path — interface-checked). -/

/-- The running accumulator of a composition fold. -/
structure ComposeAcc where
  offset : Nat            := 0     -- binding vars of all chunks composed so far
  ops    : List LSOp      := []
  flows  : List Flow      := []
  geo    : Geometry       := {}
  obs    : List Obligation := []
  deriving Inhabited

/-- Fold one chunk into the accumulator, offsetting its var references by the running
    binding-var count. -/
def composeStep (acc : ComposeAcc) (c : LSChunk) : ComposeAcc :=
  { offset := acc.offset + c.program.numBindingVars
    ops    := acc.ops   ++ c.program.ops.map (LSOp.shiftSrcs acc.offset)
    flows  := acc.flows ++ c.program.flows.map (Flow.shiftVars acc.offset)
    geo    := acc.geo.merge c.geometry
    obs    := acc.obs   ++ c.obligations }

/-- **Generic chunk composition (interface-checked automatic path).**  Concatenate `cs`
    onto one SHARED patch (`numQubits = max`), offsetting later chunks' var references,
    merging geometries and obligations.  Measurement kinds are preserved (the `meas` ops are
    copied verbatim).  Records a generic `flowCompositionDeferred` seam obligation AND, for
    EVERY adjacent pair, an explicit `flowCompositionDeferred` for each UNMATCHED flow
    interface (`allAdjacentUnmatchedObligations`) — mismatches are surfaced, not dropped. -/
def composeChunks (name source stage : String) (cs : List LSChunk) : LSChunk :=
  let acc := cs.foldl composeStep {}
  let numQubits := cs.foldl (fun m c => max m c.program.numQubits) 0
  { name := name, source := source, stage := stage
    program := { numQubits := numQubits, ops := acc.ops, flows := acc.flows }
    geometry := acc.geo
    obligations := (acc.obs
      ++ [Obligation.flowCompositionDeferred
           s!"composed {cs.length} chunks on a shared patch; flow interfaces matched structurally only — semantic flow soundness across the seam(s) is deferred"]
      ++ allAdjacentUnmatchedObligations cs).eraseDups }

/-- **Compose then check + lower.**  Runs `LS.check` on the composed program and lowers it
    to QStab via the existing chunk-aware lowering (extractability + merged obligations).
    The merged obligations include the per-adjacent-pair unmatched-interface obligations. -/
def composeChunksChecked (name source stage : String) (cs : List LSChunk) :
    Except LSError LoweredChunk :=
  lowerChunkCheckedWithExtract (composeChunks name source stage cs)

/-- Compose exactly two chunks (the interface check is already in `composeChunks`). -/
def composePairWithInterfaceCheck (name source stage : String) (a b : LSChunk) : LSChunk :=
  composeChunks name source stage [a, b]

/-! ## §3. Tests — GENERIC chunks (not Gidney-specific). -/

/-- Does an obligation tag a flow-composition (interface/seam) caveat? -/
def isFlowCompObligation : Obligation → Bool
  | .flowCompositionDeferred _ => true
  | _                          => false

-- two trivial single-measurement chunks on a shared 2-qubit patch, with matching flows:
def chunkA : LSChunk :=
  { name := "A", source := "test", stage := "test"
    program := { numQubits := 2, ops := [ .meas none [(0, .Z)], .detector { name := "dA", srcs := [0] } ],
                 flows := [ { tag := "A-out", input := [], output := [(0, .Z)], vars := [0], status := .structural } ] } }
def chunkB : LSChunk :=
  { name := "B", source := "test", stage := "test"
    program := { numQubits := 2, ops := [ .meas none [(0, .Z)], .detector { name := "dB", srcs := [0] } ],
                 flows := [ { tag := "B-in", input := [(0, .Z)], output := [], vars := [0], status := .structural } ] } }
-- a variant of B whose incoming flow has a DIFFERENT support (qubit 1, not 0):
def chunkBmismatch : LSChunk :=
  { name := "Bx", source := "test", stage := "test"
    program := { numQubits := 2, ops := [ .meas none [(1, .Z)], .detector { name := "dBx", srcs := [0] } ],
                 flows := [ { tag := "Bx-in", input := [(1, .Z)], output := [], vars := [0], status := .structural } ] } }

def composedAB : LSChunk := composeChunks "AB" "test" "compose" [chunkA, chunkB]

-- the composed program CHECKS (and lowers): chunk B's var reference was offset past chunk A:
example : composedAB.checks? = true := by decide
example : composedAB.lowers? = true := by decide
-- QVAR OFFSET: chunk A's detector keeps src 0; chunk B's detector is shifted to src 1:
example : composedAB.detectors.map (·.srcs) = [[0], [1]] := by decide
-- the flow `vars` were offset the same way (A-out at var 0, B-in at var 1):
example : composedAB.flows.map (·.vars) = [[0], [1]] := by decide
-- both measurements are preserved with their kinds (2 MPP products, 0 destructive):
example : composedAB.measurements.length = 2 := by decide
example : (composeChunksChecked "AB" "test" "compose" [chunkA, chunkB]).toOption.map
    (fun lc => lc.sidecar.countMeasKind .mpp) = some 2 := by decide
example : (composeChunksChecked "AB" "test" "compose" [chunkA, chunkB]).toOption.map
    (fun lc => lc.sidecar.countMeasKind .destructive) = some 0 := by decide

-- §1b STRUCTURAL INTERFACE: A's outgoing flow matches B's incoming flow…
example : Flow.interfaceMatches
    { tag := "A-out", input := [], output := [(0, .Z)], vars := [0] }
    { tag := "B-in",  input := [(0, .Z)], output := [], vars := [0] } = true := by decide
-- …but NOT B-mismatch's incoming flow (different support):
example : Flow.interfaceMatches
    { tag := "A-out", input := [], output := [(0, .Z)], vars := [0] }
    { tag := "Bx-in", input := [(1, .Z)], output := [], vars := [0] } = false := by decide
-- a matching pair is fully matched; the report records the matched pair:
example : interfacesFullyMatched chunkA chunkB = true := by decide
example : (matchInterfaces chunkA chunkB).matched = [("A-out", "B-in")] := by decide
-- a MISMATCHED pair is NOT fully matched, and the unmatched interface is recorded:
example : interfacesFullyMatched chunkA chunkBmismatch = false := by decide
example : (matchInterfaces chunkA chunkBmismatch).unmatchedOut = ["A-out"] := by decide
example : unmatchedInterfaceObligations chunkA chunkB = [] := by decide
example : (unmatchedInterfaceObligations chunkA chunkBmismatch).length = 2 := by decide

-- AUTOMATIC PATH HONESTY: a MATCHED composition carries exactly 1 flow-composition obligation
-- (the generic seam), while a MISMATCHED composition carries 3 (1 generic + 2 unmatched) —
-- the unmatched-interface obligations are on `composeChunks`/`composeChunksChecked` itself,
-- NOT only on the pair helper.  These FAIL if the automatic interface-check is removed:
example : ((composeChunks "AB" "test" "compose" [chunkA, chunkB]).obligations.filter isFlowCompObligation).length = 1 := by decide
example : ((composeChunks "ABx" "test" "compose" [chunkA, chunkBmismatch]).obligations.filter isFlowCompObligation).length = 3 := by decide
example : (composeChunksChecked "ABx" "test" "compose" [chunkA, chunkBmismatch]).toOption.map
    (fun lc => (lc.obligations.filter isFlowCompObligation).length) = some 3 := by decide
-- the pair helper agrees with the automatic path (it IS the automatic path now):
example : ((composePairWithInterfaceCheck "ABx" "test" "compose" chunkA chunkBmismatch).obligations.filter isFlowCompObligation).length = 3 := by decide

end Compiler.LS
