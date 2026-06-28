/-
  Compiler.Verification.Compile — a MixedIR → QStab COMPILER that TARGETS the verifier.

  This is NOT a parallel, unchecked lowering.  Every artifact the compiler emits is
  produced by the SAME functions `Compiler.Verification.Basic` uses to VERIFY
  (`expectedDirectMixedQStab` / `expectedDirectMixedProgQStab`), so a compiled artifact is
  verifier-accepted BY CONSTRUCTION — and the `compileAndVerify*` / chunked APIs make that
  round-trip machine-checked.

  HONEST SCOPE.  The compiler emits a QStab artifact ONLY for the verified fragment:
    * STRUCTURAL (synthesized directly): transversal H/S, transversalCNOT(+Batch), `.pauli`,
      straight-line `.ppm`;
    * SEMANTIC (assembled from SUPPLIED chunk witnesses, then verified): general
      `.transversal` and `.automorphism`.
  For `.switch`, magic, non-straight-line PPM, and external QGPU/GPPM/batched protocols it
  returns an EXPLICIT unsupported obligation — never a fake empty artifact.  Semantic chunk
  witnesses cannot bypass type checking (the chunked verifier runs `checkInstr` first).
-/
import Compiler.Verification.Basic

namespace Compiler.Verification
open Compiler TypeChecker PPM QStab

/-! ## §1. Compile classification. -/

/-- How the compiler can produce a QStab artifact for a `MixedInstr`. -/
inductive CompileClass
  | structural       -- the compiler SYNTHESIZES the canonical QStab artifact directly
  | witnessRequired  -- semantic (`.automorphism` / general `.transversal`): needs a supplied chunk witness
  | deferred         -- no QStab compilation (`.switch` / magic / control-PPM / external)
  deriving DecidableEq, Repr

/-- The compile class of each `MixedInstr` (mirrors the verifier's `mixedInstrStatus`). -/
def mixedInstrCompileClass : MixedInstr → CompileClass
  | .transversal _ g =>
      if decide (g = hGate2x2) || decide (g = sGate2x2) then .structural else .witnessRequired
  | .transversalCNOT _      => .structural
  | .transversalCNOTBatch _ => .structural
  | .pauli _ _              => .structural
  | .ppm stmt               => match straightLineMeas? stmt with | some _ => .structural | none => .deferred
  | .automorphism _ _       => .witnessRequired
  | .switch _ _ _           => .deferred
  | .magic _                => .deferred

/-! ## §2. Structural compiler (SYNTHESIZES the artifact, reusing the verifier's lowering). -/

/-- Compile ONE structural Mixed instruction to its QStab artifact, SYNTHESIZED by the
    verifier's own lowering (`expectedDirectMixedQStab`), so it is verifier-accepted by
    construction.  Witness-required / unsupported instructions return an explicit error —
    never a fake artifact. -/
def compileMixedInstrQStab (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (instr : MixedInstr) : Except VerificationError StabilizerProg :=
  if !L.wf then .error (.layoutError "physical layout is malformed (duplicate block id or destination)")
  else expectedDirectMixedQStab Gamma caps L instr

/-- Compile a whole STRUCTURAL program to the concatenated QStab artifact (threading
    env/state via the verifier's `expectedDirectMixedProgQStab`).  Any instruction outside
    the structural fragment yields an explicit error (no fake artifact). -/
def compileDirectMixedProgQStab (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (prog : LogicalExec) : Except VerificationError StabilizerProg :=
  if !L.wf then .error (.layoutError "physical layout is malformed (duplicate block id or destination)")
  else expectedDirectMixedProgQStab caps L Gamma PPMState.init prog

/-- **Compile AND verify** a structural program: synthesize the artifact, then run the
    verifier on it, returning the artifact ONLY if the verifier accepts.  A machine-checked
    round-trip — the compiler emits exactly the verifier's expected lowering, so success
    witnesses that the compiled artifact passes the wall. -/
def compileAndVerifyDirectMixedProgQStab (Gamma : TypedEnv) (caps : List Capability)
    (L : PhysLayout) (prog : LogicalExec) (spec : QStabVerificationSpec := {}) :
    Except VerificationError StabilizerProg :=
  match compileDirectMixedProgQStab Gamma caps L prog with
  | .error e => .error e
  | .ok artifact =>
    match verifyDirectMixedProgQStab Gamma caps L prog artifact spec with
    | .ok _    => .ok artifact
    | .error e => .error e

/-! ## §3. Chunked compiler (assembles SUPPLIED semantic witnesses, then verifies). -/

/-- **(Lower level) ASSEMBLE-AND-VERIFY the GIVEN chunks.**  This takes ONLY the chunk
    list, so the "source program" is implicitly `chunks.map (·.instr)`.  It soundly verifies
    THESE chunks, but it cannot catch a caller who meant to compile some external
    `LogicalExec` and supplied omitted / reordered / extra chunks — for that, prefer
    `compileAndVerifyChunkedMixedProgQStab` (which checks the chunk instructions against the
    source program FIRST).  Returns the concatenation on success.  The compiler does NOT
    synthesize general-Clifford slices here — those must be supplied as chunk witnesses — but
    a witness cannot bypass type checking (`checkInstr` runs first), and a witness that does
    not induce the claimed map is rejected. -/
def compileChunkedMixedProgQStab (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (chunks : List MixedQStabChunk) (mode : CliffordCheck := .symplectic)
    (spec : QStabVerificationSpec := {}) : Except VerificationError StabilizerProg :=
  let artifact := (chunks.map (fun c => c.artifact)).flatten
  match verifyChunkedMixedProgQStab Gamma caps L chunks artifact mode spec with
  | .ok _    => .ok artifact
  | .error e => .error e

/-! ## §3b. Source-program-checked chunked compiler (the PREFERRED chunked API). -/

/-- Bool structural equality on `PPM.Stmt` (which has no `DecidableEq`). -/
def samePPMStmt : PPM.Stmt → PPM.Stmt → Bool
  | .meas r1 P1, .meas r2 P2       => decide (r1 = r2) && decide (P1 = P2)
  | .frame q1 p1, .frame q2 p2     => decide (q1 = q2) && decide (p1 = p2)
  | .discard q1, .discard q2       => decide (q1 = q2)
  | .ite r1 a1 b1, .ite r2 a2 b2   => decide (r1 = r2) && samePPMStmt a1 a2 && samePPMStmt b1 b2
  | .forLoop n1 b1, .forLoop n2 b2 => decide (n1 = n2) && samePPMStmt b1 b2
  | .skip, .skip                   => true
  | .seq a1 b1, .seq a2 b2         => samePPMStmt a1 a2 && samePPMStmt b1 b2
  | .abort, .abort                 => true
  | _, _                           => false

/-- Bool structural equality on `MixedInstr` (`MixedInstr` has no `DecidableEq` — it carries
    `PPM.Stmt`/`Block`/`SwitchCert` which lack it — so we compare structurally, like
    `sameStabilizerInstr`).  Faithful on the compilable fragment; `.switch` compares only its
    block id (deferred and rejected downstream regardless). -/
def sameMixedInstr : MixedInstr → MixedInstr → Bool
  | .transversal b1 g1, .transversal b2 g2             => decide (b1 = b2) && decide (g1 = g2)
  | .transversalCNOT s1, .transversalCNOT s2           => decide (s1 = s2)
  | .transversalCNOTBatch s1, .transversalCNOTBatch s2 => decide (s1 = s2)
  | .automorphism b1 M1, .automorphism b2 M2           => decide (b1 = b2) && decide (M1 = M2)
  | .pauli q1 p1, .pauli q2 p2                         => decide (q1 = q2) && decide (p1 = p2)
  | .ppm s1, .ppm s2                                    => samePPMStmt s1 s2
  | .magic o1, .magic o2                               => decide (o1 = o2)
  | .switch b1 _ _, .switch b2 _ _                     => decide (b1 = b2)
  | _, _                                               => false

/-- Bool structural equality on a `LogicalExec` (positional). -/
def sameMixedProg : LogicalExec → LogicalExec → Bool
  | [], []           => true
  | i :: is, j :: js => sameMixedInstr i j && sameMixedProg is js
  | _, _             => false

/-- **The PREFERRED chunked compiler API.**  Compile a GIVEN source program `prog` from a
    chunk list: FIRST require `chunks.map (·.instr)` to match `prog` (catching omitted /
    reordered / extra chunks), THEN delegate to `compileChunkedMixedProgQStab` (which
    verifies each chunk).  No duplicated lowering/verifier logic. -/
def compileAndVerifyChunkedMixedProgQStab (Gamma : TypedEnv) (caps : List Capability)
    (L : PhysLayout) (prog : LogicalExec) (chunks : List MixedQStabChunk)
    (mode : CliffordCheck := .symplectic) (spec : QStabVerificationSpec := {}) :
    Except VerificationError StabilizerProg :=
  if sameMixedProg (chunks.map (fun c => c.instr)) prog then
    compileChunkedMixedProgQStab Gamma caps L chunks mode spec
  else
    .error (.certFailed "chunk instructions do not match the source program (omitted / reordered / extra chunk)")

/-! ## §3c. First semantic WITNESS SYNTHESIS — single-qubit H/S transversal Cliffords. -/

/-- A single-qubit Clifford generator. -/
inductive Clifford1 | H | S
  deriving DecidableEq, Repr

/-- The QStab gate a generator emits on a physical qubit. -/
def Clifford1.toInstr : Clifford1 → Physical.PQubit → StabilizerInstr
  | .H, q => .H q
  | .S, q => .S q

/-- The H/S gate sequence whose single-qubit symplectic action (under the verifier's
    simulator; program order = left-to-right matrix product) equals `g`, for `g` in the
    6-element single-qubit symplectic group `Sp(2,𝔽₂)`; `none` otherwise.  This is only a
    CANDIDATE — soundness is re-checked by the verifier when the synthesized chunk is
    compiled, so a table mistake can never produce an unverified artifact. -/
def singleQubitCliffordSeq? (g : ChainQ.GF2.BoolMat) : Option (List Clifford1) :=
  if decide (g = [[true, false], [false, true]]) then some []               -- I
  else if decide (g = hGate2x2) then some [.H]                              -- H  = [[F,T],[T,F]]
  else if decide (g = sGate2x2) then some [.S]                              -- S  = [[T,T],[F,T]]
  else if decide (g = [[false, true], [true, true]]) then some [.H, .S]     -- HS = [[F,T],[T,T]]
  else if decide (g = [[true, true], [true, false]]) then some [.S, .H]     -- SH = [[T,T],[T,F]]
  else if decide (g = [[true, false], [true, true]]) then some [.H, .S, .H] -- the 6th element
  else none

/-- Synthesize a chunk witness for `.transversal b g` when `g` is a single-qubit H/S
    Clifford: apply that gate sequence to EVERY physical qubit of `b` (per-qubit order).
    `none` if `g` is outside the synthesizable set or the layout has no placement for `b`. -/
def synthTransversalChunk? (L : PhysLayout) (b : Nat) (g : ChainQ.GF2.BoolMat) :
    Option MixedQStabChunk :=
  match L.blockQubits? b, singleQubitCliffordSeq? g with
  | some qs, some seq =>
      some { instr := .transversal b g,
             artifact := qs.flatMap (fun q => seq.map (fun gk => gk.toInstr q)) }
  | _, _ => none

/-- Compile `.transversal b g` by SYNTHESIZING its witness (single-qubit H/S Clifford only),
    then verifying through the source-program-checked chunked compiler.  A `g` outside the
    synthesizable set returns an explicit witness-required error (no fake artifact); an
    ILLEGAL transversal still fails at the type checker inside the verifier. -/
def compileSynthTransversalQStab (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (b : Nat) (g : ChainQ.GF2.BoolMat) (mode : CliffordCheck := .symplectic) :
    Except VerificationError StabilizerProg :=
  match synthTransversalChunk? L b g with
  | none => .error (.unsupportedMixed
      "transversal g is not a synthesizable single-qubit H/S Clifford (or the block has no layout); supply a chunk witness")
  | some chunk => compileAndVerifyChunkedMixedProgQStab Gamma caps L [.transversal b g] [chunk] mode

/-! ## §3d. Unified program compiler: structural first, then single-qubit H/S synthesis. -/

/-- Build the QStab chunk for ONE instruction: a `.transversal` is SYNTHESIZED (single-qubit
    H/S Cliffords only — `synthTransversalChunk?`, which also covers H/S); everything else
    structural (`directMixedQStabLowering`: CNOT/batch/`.pauli`/straight-line PPM); a general
    `.automorphism`, a non-synthesizable transversal, or a deferred instruction
    (switch/magic/control-PPM) is an explicit error (no fake artifact).  Type checking and
    semantic verification happen later, in the chunked verifier. -/
def buildMixedChunk? (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout) :
    MixedInstr → Except VerificationError MixedQStabChunk
  | .transversal b g =>
      match synthTransversalChunk? L b g with
      | some chunk => .ok chunk
      | none => .error (.unsupportedMixed
          "transversal g is not a synthesizable single-qubit H/S Clifford; supply a chunk witness")
  | .automorphism _ _ => .error (.unsupportedMixed "automorphism requires a supplied chunk witness (no synthesis yet)")
  | instr =>
      match directMixedQStabLowering Gamma caps L instr with
      | .ok art  => .ok { instr := instr, artifact := art }
      | .error e => .error e

/-- Build chunks for a whole program (fails on the first unsupported instruction). -/
def buildMixedChunks? (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout) :
    LogicalExec → Except VerificationError (List MixedQStabChunk)
  | []        => .ok []
  | i :: rest =>
      match buildMixedChunk? Gamma caps L i with
      | .error e => .error e
      | .ok c =>
        match buildMixedChunks? Gamma caps L rest with
        | .error e => .error e
        | .ok cs => .ok (c :: cs)

/-- **The unified public compiler.**  Compile a whole MixedIR program to QStab: structural
    instructions are synthesized directly, single-qubit H/S `.transversal`s are synthesized,
    and everything else (general `.automorphism`, `.switch`, magic, non-straight-line PPM,
    external protocols) is an explicit unsupported/witness-required error.  The result is
    returned ONLY after passing the verifier (it routes through
    `compileAndVerifyChunkedMixedProgQStab` → `verifyChunkedMixedProgQStab`), so no QStab is
    emitted without verification, and `.prop` stays measurement-only. -/
def compileAndVerifyMixedProgQStab (Gamma : TypedEnv) (caps : List Capability) (L : PhysLayout)
    (prog : LogicalExec) (mode : CliffordCheck := .symplectic) (spec : QStabVerificationSpec := {}) :
    Except VerificationError StabilizerProg :=
  match buildMixedChunks? Gamma caps L prog with
  | .error e  => .error e
  | .ok chunks => compileAndVerifyChunkedMixedProgQStab Gamma caps L prog chunks mode spec

/-! ## §4. Regression examples. -/

/-! ### Compiled SUPPORTED programs compile and verify. -/

-- a structural program compiles AND verifies (machine-checked round-trip):
example : ok? (compileAndVerifyDirectMixedProgQStab tenvQ [] bareLayout1
    [.transversal 0 hGate2x2, .pauli ⟨0, 0⟩ .Z]) = true := by decide
-- the compiled artifact is exactly the expected `[.H 0, .Z 0]`:
example : (compileDirectMixedProgQStab tenvQ [] bareLayout1 [.transversal 0 hGate2x2, .pauli ⟨0, 0⟩ .Z]).toOption.map
    (fun a => sameStabilizerProg a [.H 0, .Z 0]) = some true := by decide
-- transversal CNOT and straight-line PPM compile + verify:
example : ok? (compileAndVerifyDirectMixedProgQStab tenv2Q [] twoLayout [.transversalCNOT cnotSpec2]) = true := by decide
example : ok? (compileAndVerifyDirectMixedProgQStab tenvQ [] bareLayout1 [.ppm (.meas 0 [(⟨0, 0⟩, PLetter.Z)])]) = true := by decide
-- single-instruction structural compile:
example : ok? (compileMixedInstrQStab tenvQ [] bareLayout1 (.transversal 0 sGate2x2)) = true := by decide

/-! ### Wrong layouts fail (no artifact emitted). -/

-- a malformed layout (duplicate physical destination) → compile fails:
example : ok? (compileDirectMixedProgQStab tenv2Q [] badLayout [.transversalCNOT cnotSpec2]) = false := by decide
-- a partial layout (a touched block is not fully covered) → compile fails:
example : ok? (compileDirectMixedProgQStab vEnv22 [] partialLayout22 [.transversalCNOT cnotSparseSpec]) = false := by decide

/-! ### Unsupported primitives do NOT produce QStab (explicit obligations). -/

-- magic → explicit `unsupportedMixed`, NOT an artifact:
example : (match compileMixedInstrQStab tenvQ [] bareLayout1 (.magic { kind := .tGate, target := ⟨0, 0⟩ }) with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide
-- non-straight-line PPM (a frame effect) → unsupported (never silently erased):
example : ok? (compileDirectMixedProgQStab tenvQ [] bareLayout1 [.ppm (.frame ⟨0, 0⟩ .X)]) = false := by decide
-- the STRUCTURAL compiler refuses an automorphism (witness-required, not synthesizable here):
example : mixedInstrCompileClass (.automorphism 0 idMat4) = .witnessRequired := by decide
example : (match compileMixedInstrQStab tenvQ [] bareLayout1 (.automorphism 0 [[false, true], [true, false]]) with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide
-- classification: switch / magic deferred; H/S transversal & CNOT structural:
example : mixedInstrCompileClass (.switch 0 vBare2 { kind := .teleport, f := [] }) = .deferred := by decide
example : mixedInstrCompileClass (.magic { kind := .tGate, target := ⟨0, 0⟩ }) = .deferred := by decide
example : mixedInstrCompileClass (.transversal 0 hGate2x2) = .structural := by decide
example : mixedInstrCompileClass (.transversalCNOT cnotSpec2) = .structural := by decide

/-! ### Semantic chunks compile (with witnesses) and cannot bypass type checking. -/

-- an automorphism+pauli program compiles via SUPPLIED chunk witnesses + chunked verify:
example : ok? (compileChunkedMixedProgQStab tenvQ [] bareLayout1 [chunkAutoH, chunkPauliX]) = true := by decide
example : (compileChunkedMixedProgQStab tenvQ [] bareLayout1 [chunkAutoH, chunkPauliX]).toOption.map
    (fun a => sameStabilizerProg a [.H 0, .X 0]) = some true := by decide
-- a chunk with a SHAPE-INVALID automorphism is rejected by the verifier's `checkInstr`
-- (a semantic chunk CANNOT bypass type checking):
example : (match compileChunkedMixedProgQStab tenvQ [] bareLayout1 [{ instr := .automorphism 0 [[true]], artifact := [] }] with
           | .error (.typeError _) => true | _ => false) = true := by decide
-- a chunk whose witness does NOT induce the claimed map is rejected:
example : ok? (compileChunkedMixedProgQStab tenvQ [] bareLayout1
    [{ instr := .automorphism 0 [[false, true], [true, false]], artifact := [.S 0] }]) = false := by decide
-- a deferred-instruction chunk (magic) is unsupported, not silently compiled:
example : (match compileChunkedMixedProgQStab tenvQ [] bareLayout1
            [{ instr := .magic { kind := .tGate, target := ⟨0, 0⟩ }, artifact := [] }] with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide

/-! ### §4b. Source-program-checked chunked compiler (the preferred chunked API). -/

-- the CORRECT chunk list for `[automorphism H ; pauli X]` compiles + verifies:
example : ok? (compileAndVerifyChunkedMixedProgQStab tenvQ [] bareLayout1
    [.automorphism 0 [[false, true], [true, false]], .pauli ⟨0, 0⟩ .X] [chunkAutoH, chunkPauliX]) = true := by decide
-- REORDERED chunks are rejected by the source-program equality check (certFailed):
example : (match compileAndVerifyChunkedMixedProgQStab tenvQ [] bareLayout1
            [.automorphism 0 [[false, true], [true, false]], .pauli ⟨0, 0⟩ .X] [chunkPauliX, chunkAutoH] with
           | .error (.certFailed _) => true | _ => false) = true := by decide
-- an OMITTED chunk is rejected:
example : ok? (compileAndVerifyChunkedMixedProgQStab tenvQ [] bareLayout1
    [.automorphism 0 [[false, true], [true, false]], .pauli ⟨0, 0⟩ .X] [chunkAutoH]) = false := by decide
-- an EXTRA chunk is rejected:
example : ok? (compileAndVerifyChunkedMixedProgQStab tenvQ [] bareLayout1
    [.automorphism 0 [[false, true], [true, false]]] [chunkAutoH, chunkPauliX]) = false := by decide
-- a semantically WRONG witness is still rejected by the chunked verifier (not the source check):
example : ok? (compileAndVerifyChunkedMixedProgQStab tenvQ [] bareLayout1
    [.automorphism 0 [[false, true], [true, false]]]
    [{ instr := .automorphism 0 [[false, true], [true, false]], artifact := [.S 0] }]) = false := by decide
-- a TYPE-INVALID chunk is still rejected by `checkInstr`:
example : (match compileAndVerifyChunkedMixedProgQStab tenvQ [] bareLayout1
            [.automorphism 0 [[true]]] [{ instr := .automorphism 0 [[true]], artifact := [] }] with
           | .error (.typeError _) => true | _ => false) = true := by decide
-- a deferred instruction (magic) remains unsupported:
example : (match compileAndVerifyChunkedMixedProgQStab tenvQ [] bareLayout1
            [.magic { kind := .tGate, target := ⟨0, 0⟩ }]
            [{ instr := .magic { kind := .tGate, target := ⟨0, 0⟩ }, artifact := [] }] with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide

/-! ### §4c. Synthesized semantic transversal chunks (single-qubit H/S Cliffords). -/

-- a non-H/S valid transversal `g = HS` SYNTHESIZES to `[.H 0, .S 0]` and verifies:
example : ok? (compileSynthTransversalQStab tenvQ [] bareLayout1 0 [[false, true], [true, true]]) = true := by decide
example : (compileSynthTransversalQStab tenvQ [] bareLayout1 0 [[false, true], [true, true]]).toOption.map
    (fun a => sameStabilizerProg a [.H 0, .S 0]) = some true := by decide
-- H and S synthesize to their canonical single gate (and verify):
example : (compileSynthTransversalQStab tenvQ [] bareLayout1 0 hGate2x2).toOption.map
    (fun a => sameStabilizerProg a [.H 0]) = some true := by decide
example : (compileSynthTransversalQStab tenvQ [] bareLayout1 0 sGate2x2).toOption.map
    (fun a => sameStabilizerProg a [.S 0]) = some true := by decide
-- a NON-synthesizable (non-symplectic) `g` returns an explicit witness-required error:
example : (match compileSynthTransversalQStab tenvQ [] bareLayout1 0 [[true, false], [true, false]] with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide
-- an ILLEGAL transversal (H on the repetition code) still fails at the TYPE CHECKER:
example : (match compileSynthTransversalQStab tenvR [] repLayout 0 hGate2x2 with
           | .error (.typeError _) => true | _ => false) = true := by decide

/-! ## §5. Hardened `.prop` construction from an EXPLICIT indexed sparse Pauli.

    `.prop` measurements are easy to misread as raw dense strings (`X[1]X[3]` ≠ `"XX"`, it is
    `"IXIX"`).  These constructors take a `QStab.SparsePauli` (`[(1, X), (3, X)]`) and the
    declared device size, and build the `.prop` via the CHECKED `toDense?` — rejecting empty
    / identity / duplicate / out-of-range, never silently identity-defaulting. -/

/-- Build a QStab `.prop` MEASUREMENT statement from an explicit indexed sparse Pauli,
    checked-densified under `numQubits`. -/
def mkPropFromSparse? (sched : Option Sched) (numQubits : Nat) (P : QStab.SparsePauli) :
    Except VerificationError QStab.Stmt :=
  match QStab.SparsePauli.toDense? numQubits P with
  | .ok dense => .ok (.prop sched dense)
  | .error _  => .error (.certFailed
      "sparse Pauli for .prop is malformed (empty / identity factor / duplicate qubit / out-of-range)")

/-- Build a QStab `.bind (.prop …)` stabilizer instruction from an explicit sparse Pauli. -/
def mkBindPropFromSparse? (sched : Option Sched) (numQubits : Nat) (P : QStab.SparsePauli) :
    Except VerificationError StabilizerInstr :=
  match mkPropFromSparse? sched numQubits P with
  | .ok stmt => .ok (.bind stmt)
  | .error e => .error e

/-! ### §5b. Verifier-facing regression tests for explicit physical indexing. -/

-- the sparse constructor makes the indexing explicit: `[(5, X)]` on 6 qubits → `"IIIIIX"`:
example : (mkPropFromSparse? none 6 [(5, .X)]).toOption = some (.prop none (Physical.ofString "IIIIIX")) := by decide
-- the hardened constructor REJECTS malformed sparse Paulis (no fake `.prop`):
example : ok? (mkPropFromSparse? none 6 [(5, .X), (5, .Z)]) = false := by decide   -- duplicate qubit
example : ok? (mkPropFromSparse? none 6 [(0, .I)]) = false := by decide            -- identity factor
example : ok? (mkPropFromSparse? none 6 ([] : QStab.SparsePauli)) = false := by decide  -- empty
example : ok? (mkPropFromSparse? none 6 [(9, .X)]) = false := by decide            -- out of range

-- a PPM logical `X̄` on a layout with block OFFSET 5 corresponds to sparse `[(5, X)]`,
-- dense `"IIIIIX"`, and an ACCEPTED `.prop` (built via the hardened constructor):
example : (match mkBindPropFromSparse? none 6 [(5, .X)] with
           | .ok bp => ok? (verifyPPMMeasurementQStabLayout tenvQ [] offsetLayout1 none
                              [(⟨0, 0⟩, PLetter.X)] [bp, .bind (.parity [0])])
           | .error _ => false) = true := by decide
-- the COMPACT / WRONG sparse `[(0, X)]` (qubit 0, not the layout's qubit 5 → `"XIIIII"`) is
-- REJECTED when verifying the SAME logical target:
example : ok? (verifyPPMMeasurementQStabLayout tenvQ [] offsetLayout1 none [(⟨0, 0⟩, PLetter.X)]
    [.bind (.prop none (Physical.ofString "XIIIII")), .bind (.parity [0])]) = false := by decide

-- logical `.pauli` application STILL compiles to `.X 5` (a Pauli APPLICATION), NEVER a `.prop`:
example : (compileMixedInstrQStab tenvQ [] offsetLayout1 (.pauli ⟨0, 0⟩ .X)).toOption.map
    (fun a => sameStabilizerProg a [.X 5]) = some true := by decide
-- transversal Clifford SYNTHESIS still emits `.H`/`.S` gates, NEVER a `.prop`:
example : (compileSynthTransversalQStab tenvQ [] bareLayout1 0 hGate2x2).toOption.map
    (fun a => sameStabilizerProg a [.H 0]) = some true := by decide
example : (compileSynthTransversalQStab tenvQ [] bareLayout1 0 [[false, true], [true, true]]).toOption.map
    (fun a => sameStabilizerProg a [.H 0, .S 0]) = some true := by decide

/-! ## §6. The unified compiler `compileAndVerifyMixedProgQStab` (structural ▸ synth ▸ error). -/

-- a STRUCTURAL program compiles + verifies:
example : ok? (compileAndVerifyMixedProgQStab tenvQ [] bareLayout1
    [.transversal 0 hGate2x2, .pauli ⟨0, 0⟩ .Z]) = true := by decide
-- a non-H/S transversal `HS` compiles via SYNTHESIS and verifies:
example : ok? (compileAndVerifyMixedProgQStab tenvQ [] bareLayout1 [.transversal 0 [[false, true], [true, true]]]) = true := by decide
-- a MIXED structural + synthesized-transversal program compiles IN ORDER (`[.X 0, .H 0, .S 0]`):
example : (compileAndVerifyMixedProgQStab tenvQ [] bareLayout1
    [.pauli ⟨0, 0⟩ .X, .transversal 0 [[false, true], [true, true]]]).toOption.map
    (fun a => sameStabilizerProg a [.X 0, .H 0, .S 0]) = some true := by decide
-- a transversal CNOT program compiles + verifies:
example : ok? (compileAndVerifyMixedProgQStab tenv2Q [] twoLayout [.transversalCNOT cnotSpec2]) = true := by decide
-- unsupported MAGIC rejects (no synthesis, no fake artifact):
example : ok? (compileAndVerifyMixedProgQStab tenvQ [] bareLayout1 [.magic { kind := .tGate, target := ⟨0, 0⟩ }]) = false := by decide
example : (match compileAndVerifyMixedProgQStab tenvQ [] bareLayout1 [.magic { kind := .tGate, target := ⟨0, 0⟩ }] with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide
-- a general AUTOMORPHISM is witness-required (the unified compiler does NOT synthesize it):
example : (match compileAndVerifyMixedProgQStab tenvQ [] bareLayout1 [.automorphism 0 [[false, true], [true, false]]] with
           | .error (.unsupportedMixed _) => true | _ => false) = true := by decide
-- a WRONG (malformed) layout rejects:
example : ok? (compileAndVerifyMixedProgQStab tenv2Q [] badLayout [.transversalCNOT cnotSpec2]) = false := by decide
-- an ILLEGAL transversal (H on the repetition code) rejects at the TYPE CHECKER:
example : (match compileAndVerifyMixedProgQStab tenvR [] repLayout [.transversal 0 hGate2x2] with
           | .error (.typeError _) => true | _ => false) = true := by decide

end Compiler.Verification
