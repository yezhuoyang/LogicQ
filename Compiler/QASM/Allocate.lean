/-
  Compiler.QASM.Allocate — QASM → LogicQ LOGICAL-QUBIT ALLOCATION + typed MixIR
  emission.

  HONEST SCOPE.  This is a name-level ALLOCATION layer on top of the existing,
  verified `Compiler.ChainQ2Mixed` compiler — NOT a new lowering.  It (1) maps QASM
  virtual qubits to user-declared ChainQ logical qubits by first-fit, (2) validates
  the user's basis-tagged logical ancilla pool, (3) translates the supported QASM
  instruction subset to `ChainQPrimOp`s, and (4) hands the result to
  `compileChainQToMixIR?`, which does ALL the real legality checking (addressing,
  ancilla basis/consumption, PPM/transversal/magic typing) and produces the proof-carrying
  `CompiledMixIR`.  We do NOT duplicate gate-legality logic, and we do NOT emit
  QStab/QClifford — the deferred physical obligations of the underlying compiler are
  preserved verbatim (`QASMArtifact.compiled.obligations`).

  ANCILLA RULE.  The underlying compiler uses an `AncillaPool`: each scratch logical
  qubit is declared with the basis it is prepared in (`.zero`, `.plus`, ...), and a
  gadget consumes one matching, valid, live entry.  The QASM layer checks the structural
  resource invariants it owns — named resources resolve, data and ancillas are disjoint,
  and no logical qubit is declared twice.  Basis availability and exact gadget
  consumption remain checked by `compileChainQToMixIR?`.

  FRESH MEASUREMENT OUTCOMES.  PPM outcome variables are SSA: a measurement may not
  bind an already-bound `CVar`.  `compileGo` uses `3·i .. 3·i+2` as the gadget outcome
  vars of op `i`, so all gadget vars lie in `[0, 3·N)`.  We therefore give the `j`-th
  QASM measurement the fresh `CVar = 3·N + j`, which is disjoint from every gadget var
  and distinct across measurements — so repeated writes to one QASM classical bit never
  collide (the QASM `creg` bit ↦ fresh `CVar` mapping is recorded in `measMap`).

  NOTE on `caps`.  Capabilities only affect the *checking* step, not allocation, so —
  unlike the sketch in the design note — they are a parameter of the compile entry
  point (`compileQASMToMixIR?`), not of the (cap-independent) `AllocationRequest`.
-/
import Compiler.QASM.Syntax
import Compiler.ChainQ2Mixed.Compile

namespace Compiler.QASM

open Compiler Compiler.ChainQ2Mixed TypeChecker PPM ChainQ.GF2 Logical Compiler.CodeSwitch

/-! ## §1. Named logical resources + the allocation request/result. -/

/-- A LogicQ logical-qubit resource addressed the ChainQ way: by `(codeName, logicalName)`. -/
structure NamedLogical where
  code    : String
  logical : String
  deriving DecidableEq, Repr, Inhabited

/-- The allocation inputs the user supplies (cap-independent — see the `caps` note).
    `dataLogicals` are the logical qubits QASM virtual qubits may occupy (consumed
    first-fit, in declaration order); `ancillas` are basis-tagged scratch logicals
    reserved for gadget lowering; `cnotIncidence`, when supplied, enables a `cx` to realize
    as a verified transversal CNOT.  `cnotMode` is QASM's EXPLICIT CNOT strategy — the
    default (`preferTransversalWithPPMFallback`) tries the transversal CNOT first and falls
    back to the PPM gadget; set `strictTransversal` to REQUIRE the transversal (no fallback),
    or `ppmOnly` to force the gadget. -/
structure AllocationRequest where
  decls           : List ChainQ.NamedCodeDecl
  dataLogicals    : List NamedLogical
  ancillas        : List NamedAnc
  cnotMode        : CNOTMode := .preferTransversalWithPPMFallback
  cnotIncidence   : Option BoolMat := none

/-- Errors the QASM front-end can raise (the lowering error wraps the underlying
    `TypeError` from `compileChainQToMixIR?` verbatim — nothing is hidden). -/
inductive QASMError where
  | unsupportedGate      (name : String)          -- an out-of-contract instruction (rx/u3/reset/custom)
  | duplicateQReg        (name : String)          -- duplicate qreg declaration
  | duplicateCReg        (name : String)          -- duplicate creg declaration
  | badQubitRef          (reg : String) (idx : Nat) -- a virtual qubit outside its declared qreg
  | badCbitRef           (reg : String) (idx : Nat) -- a virtual classical bit outside its declared creg
  | tooFewDataLogicals   (needed available : Nat)  -- not enough data logicals for the virtual qubits
  | duplicateLogical     (msg : String)            -- two virtual qubits alias one logical
  | duplicateAncilla     (msg : String)            -- two ancilla entries alias one logical
  | dataAncillaOverlap   (msg : String)            -- an ancilla aliases a data logical (or repeats)
  | nameResolution       (e : TypeError)           -- a code/logical name failed to resolve
  | lowering             (e : TypeError)           -- the underlying ChainQ→MixIR compile rejected it
  deriving Repr

/-- A resolved allocation: the first-fit virtual→named map, the per-measurement
    `creg`-bit ↦ fresh-`CVar` map, the generated named ChainQ program, the resolved
    strategy config. -/
structure Allocation where
  qubitMap : List (VQubit × NamedLogical)
  measMap  : List (VCBit × CVar)
  prog     : ChainQPrimProgram
  cfg      : StrategyConfig

/-- The end-to-end artifact: the allocation plus the proof-carrying compiled MixIR.  Indexed
    by `CapabilityWitness`es (the public, witness-safe boundary), converted internally. -/
structure QASMArtifact (ws : List CapabilityWitness) where
  alloc    : Allocation
  compiled : CompiledMixIR (ws.map CapabilityWitness.toCapability)

/-- All deferred physical obligations of the compiled program (preserved verbatim). -/
def QASMArtifact.obligations {ws : List CapabilityWitness} (a : QASMArtifact ws) :
    List PrimitiveObligation :=
  a.compiled.obligations

/-! ## §2. Resource resolution + the structural guards. -/

/-- Resolve a `(codeName, logicalName)` to its canonical `LQubit` through the ChainQ
    addressing pipeline (reused, not re-implemented). -/
def resolveNamed? (ctx : ChainQAddrCtx) (nl : NamedLogical) : Except QASMError LQubit :=
  match ctx.qubit? nl.code nl.logical with
  | .ok q    => .ok q
  | .error e => .error (.nameResolution e)

/-- Resolve a list of named logicals. -/
def resolveNamedList? (ctx : ChainQAddrCtx) (ls : List NamedLogical) :
    Except QASMError (List LQubit) :=
  ls.mapM (resolveNamed? ctx)

/-- Forget the basis tag of a `ChainQ2Mixed` ancilla declaration. -/
def namedOfAnc (na : NamedAnc) : NamedLogical :=
  { code := na.code, logical := na.logical }

/-- Logical-qubit equality (field-wise, to avoid a `BEq` dependency on `LQubit`). -/
def lqEq (a b : LQubit) : Bool := a.blk == b.blk && a.idx == b.idx

/-- No duplicate logical qubits in the list. -/
def noDupLQ : List LQubit → Bool
  | []      => true
  | q :: qs => ! qs.any (lqEq q) && noDupLQ qs

/-! ## §3. Reference validation + instruction translation. -/

/-- The first virtual qubit referenced by an instruction that no `qreg` declares. -/
def firstBadQ (p : QASMProgram) : Option VQubit :=
  (p.instrs.flatMap Instr.qubitRefs).find? (fun q => ! p.declaresQ q)

/-- The first virtual classical bit referenced that no `creg` declares. -/
def firstBadC (p : QASMProgram) : Option VCBit :=
  (p.instrs.flatMap Instr.cbitRefs).find? (fun c => ! p.declaresC c)

/-- Look the named logical up for a virtual qubit in the first-fit map. -/
def lookupV (vmap : List (VQubit × NamedLogical)) (q : VQubit) : Except QASMError NamedLogical :=
  match vmap.find? (fun p => p.1.reg == q.reg && p.1.idx == q.idx) with
  | some p => .ok p.2
  | none   => .error (.badQubitRef q.reg q.idx)

/-- Translate the QASM instructions (in order) to named `ChainQPrimOp`s, dropping
    barriers, rejecting out-of-contract gates, and assigning each measurement the
    fresh outcome `CVar = 3·N + j` (`mi` is the running measurement index `j`).  Also
    returns the `creg`-bit ↦ `CVar` measurement map.

    The pass is tail-recursive because normalized QASMBench/Qiskit outputs can contain
    hundreds of thousands of primitive gates. -/
def genOps (vmap : List (VQubit × NamedLogical)) (N : Nat) :
    Nat → List Instr → Except QASMError (List ChainQPrimOp × List (VCBit × CVar))
  | mi0, instrs =>
      let rec go (mi : Nat) (opsAcc : List ChainQPrimOp) (msAcc : List (VCBit × CVar)) :
          List Instr → Except QASMError (List ChainQPrimOp × List (VCBit × CVar))
        | [] => .ok (opsAcc.reverse, msAcc.reverse)
        | .barrier _ :: rest => go mi opsAcc msAcc rest
        | .unsupported nm :: _ => .error (.unsupportedGate nm)
        | .h q :: rest => do
            let nl ← lookupV vmap q
            go mi (.hGate nl.code nl.logical :: opsAcc) msAcc rest
        | .s q :: rest => do
            let nl ← lookupV vmap q
            go mi (.sGate nl.code nl.logical :: opsAcc) msAcc rest
        | .x q :: rest => do
            let nl ← lookupV vmap q
            go mi (.xGate nl.code nl.logical :: opsAcc) msAcc rest
        | .z q :: rest => do
            let nl ← lookupV vmap q
            go mi (.zGate nl.code nl.logical :: opsAcc) msAcc rest
        | .t q :: rest => do
            let nl ← lookupV vmap q
            go mi (.tGate nl.code nl.logical :: opsAcc) msAcc rest
        | .cx c tgt :: rest => do
            let cnl ← lookupV vmap c
            let tnl ← lookupV vmap tgt
            go mi (.cnotGate cnl.code cnl.logical tnl.code tnl.logical :: opsAcc) msAcc rest
        | .cz c tgt :: rest => do
            let cnl ← lookupV vmap c
            let tnl ← lookupV vmap tgt
            go mi (.czGate cnl.code cnl.logical tnl.code tnl.logical :: opsAcc) msAcc rest
        | .measure q cb :: rest => do
            let nl ← lookupV vmap q
            let r : CVar := 3 * N + mi
            go (mi + 1) (.measure r [(nl.code, nl.logical, PLetter.Z)] :: opsAcc) ((cb, r) :: msAcc) rest
      go mi0 [] [] instrs

/-! ## §4. The allocator + the public compile entry point. -/

/-- **First-fit logical allocation + conservative ancilla reservation.**  Validates
    references, resolves the code/logical names, maps virtual qubits to data logicals
    in order, checks data/ancilla disjointness, and translates the program.  This step
    does NO gate-legality checking —
    that is `compileChainQToMixIR?`'s job. -/
def allocate? (prog : QASMProgram) (req : AllocationRequest) : Except QASMError Allocation := do
  if let some name := prog.firstDuplicateQReg? then
    Except.error (.duplicateQReg name)
  if let some name := prog.firstDuplicateCReg? then
    Except.error (.duplicateCReg name)
  if let some q := firstBadQ prog then
    Except.error (.badQubitRef q.reg q.idx)
  if let some c := firstBadC prog then
    Except.error (.badCbitRef c.reg c.idx)
  let ctx ← match mkAddrCtx? req.decls with
    | .ok c    => pure c
    | .error e => Except.error (.nameResolution e)
  let vqs := prog.flatQubits
  if req.dataLogicals.length < vqs.length then
    Except.error (.tooFewDataLogicals vqs.length req.dataLogicals.length)
  let usedData := req.dataLogicals.take vqs.length
  let vmap := vqs.zip usedData
  let allDataQ ← resolveNamedList? ctx req.dataLogicals
  let ancQ     ← resolveNamedList? ctx (req.ancillas.map namedOfAnc)
  if ! noDupLQ allDataQ then
    Except.error (.duplicateLogical "dataLogicals contains a duplicate logical resource")
  if ! noDupLQ ancQ then
    Except.error (.duplicateAncilla "ancillas contains a duplicate logical resource")
  if ! noDupLQ (allDataQ ++ ancQ) then
    Except.error (.dataAncillaOverlap "an ancilla logical aliases a supplied data logical")
  let N := prog.opCount
  let (ops, ms) ← genOps vmap N 0 prog.instrs
  return {
    qubitMap := vmap,
    measMap  := ms,
    prog     := { decls := req.decls, ops := ops },
    cfg      := { ancillas := req.ancillas, cnotMode := req.cnotMode, cnotIncidence := req.cnotIncidence } }

/-- **The public QASM → MixIR compiler.**  Allocate logical qubits, then hand the generated
    named program to the WITNESS-SAFE `compileChainQToMixIR?` (which takes `CapabilityWitness`es,
    so a raw `.productSurgery` capability can never enter) for all legality checking.  Returns
    the allocation + the proof-carrying compiled MixIR. -/
def compileQASMToMixIR? (ws : List CapabilityWitness) (prog : QASMProgram) (req : AllocationRequest) :
    Except QASMError (QASMArtifact ws) := do
  let alloc ← allocate? prog req
  match compileChainQToMixIR? ws alloc.cfg alloc.prog with
  | .ok c    => .ok { alloc := alloc, compiled := c }
  | .error e => .error (.lowering e)

/-! ## §5. Test fixtures — bare register codes (identity logical bases). -/

/-- 2×2 / 3×3 identity logical-Pauli bases (each logical = one physical qubit), the
    same shape as the existing `regDecl` / `bareTwoQubitIndexSpec` fixtures. -/
def id2 : BoolMat := [[true, false], [false, true]]
def id3 : BoolMat := [[true, false, false], [false, true, false], [false, false, true]]

/-- A bare `n=2` register: 1 data logical `d0` + 1 ancilla logical `a0`. -/
def reg2Decl : ChainQ.NamedCodeDecl :=
  { name := "reg", decl := .css { n := 2, hx := [], hz := [] },
    logicalIndex := some { names := ["d0", "a0"], pauliBasis := { zBasis := id2, xDualBasis := id2 } } }

/-- A bare `n=3` register: 1 data logical `d0` + 2 ancilla logicals `a0`, `a1`. -/
def reg3Decl : ChainQ.NamedCodeDecl :=
  { name := "reg", decl := .css { n := 3, hx := [], hz := [] },
    logicalIndex := some { names := ["d0", "a0", "a1"], pauliBasis := { zBasis := id3, xDualBasis := id3 } } }

/-- A bare `n=3` register: 2 data logicals `d0`, `d1` + 1 ancilla logical `a0`. -/
def cx3Decl : ChainQ.NamedCodeDecl :=
  { name := "reg", decl := .css { n := 3, hx := [], hz := [] },
    logicalIndex := some { names := ["d0", "d1", "a0"], pauliBasis := { zBasis := id3, xDualBasis := id3 } } }

/-- 4×4 identity basis + a bare `n=4` register: 2 data + 2 ancilla logicals. -/
def id4 : BoolMat :=
  [[true, false, false, false], [false, true, false, false],
   [false, false, true, false], [false, false, false, true]]
def mm4Decl : ChainQ.NamedCodeDecl :=
  { name := "reg", decl := .css { n := 4, hx := [], hz := [] },
    logicalIndex := some { names := ["d0", "d1", "a0", "a1"], pauliBasis := { zBasis := id4, xDualBasis := id4 } } }

/-- Build a source logical-index spec from a checked/derived CSS logical basis. -/
def indexSpecFromBasis (names : List String) (b : ChainQ.CSSLogicalBasis) :
    ChainQ.LogicalIndexSpec :=
  { names := names, pauliBasis := { zBasis := b.lz, xDualBasis := b.lx } }

/-- Derive an index spec for a CSS code, preserving the caller's chosen logical names. -/
def derivedIndexSpec? (names : List String) (code : ChainQ.CSSCode) :
    Option ChainQ.LogicalIndexSpec :=
  match ChainQ.deriveLogicalBasis? code with
  | some b => some (indexSpecFromBasis names b)
  | none   => none

/-- Surface-code declarations with theorem-backed exact distance profiles. -/
def surfaceDecl (name : String) (d : Nat) (logicalNames : List String) :
    ChainQ.NamedCodeDecl :=
  { name := name,
    decl := .surface d,
    claimedParams := some { n := (ChainQ.surface d).n, k := (ChainQ.surface d).k, d := d },
    distanceProfile := ChainQ.surfaceDistanceBounds? d,
    logicalIndex := derivedIndexSpec? logicalNames (ChainQ.surface d) }

/-- Toric-code declarations with theorem-backed exact distance profiles. -/
def toricDecl (name : String) (d : Nat) (logicalNames : List String) :
    ChainQ.NamedCodeDecl :=
  { name := name,
    decl := .toric d,
    claimedParams := some { n := (ChainQ.toric d).n, k := (ChainQ.toric d).k, d := d },
    distanceProfile := ChainQ.toricDistanceBounds? d,
    logicalIndex := derivedIndexSpec? logicalNames (ChainQ.toric d) }

def surface2Decl : ChainQ.NamedCodeDecl := surfaceDecl "surf2" 2 ["data"]
def surface3Decl : ChainQ.NamedCodeDecl := surfaceDecl "surf3" 3 ["data"]
def toric2Decl : ChainQ.NamedCodeDecl := toricDecl "toric2" 2 ["a", "b"]

/-- A toy lifted-product-style CSS declaration from ChainQ's logical-index fixtures. -/
def toyLP3Decl : ChainQ.NamedCodeDecl :=
  { name := "lp3", decl := .css (ChainQ.toyLPCSS 3),
    logicalIndex := some (ChainQ.toyLPIndexSpec 3) }

example : ok? reg2Decl.checkLogicalIndex? = true := by decide
example : ok? reg3Decl.checkLogicalIndex? = true := by decide
example : ok? cx3Decl.checkLogicalIndex? = true := by decide
example : ok? mm4Decl.checkLogicalIndex? = true := by decide
example : ok? surface2Decl.checkLogicalIndex? = true := by decide
example : ok? surface3Decl.checkLogicalIndex? = true := by decide
example : ok? toric2Decl.checkLogicalIndex? = true := by decide
example : ok? toyLP3Decl.checkLogicalIndex? = true := by decide

/-! ## §6. Tests — POSITIVE (programs that allocate + compile). -/

-- Single qubit `H; measure` — the data logical sits on a multi-logical block, so `H`
-- teleports through the reserved ancilla `a0` (exactly the existing `regDecl` pattern):
def progHM : QASMProgram :=
  { qregs := [⟨"q", 1⟩], cregs := [⟨"c", 1⟩],
    instrs := [.h ⟨"q", 0⟩, .measure ⟨"q", 0⟩ ⟨"c", 0⟩] }
def reqHM : AllocationRequest :=
  { decls := [reg3Decl], dataLogicals := [⟨"reg", "d0"⟩],
    ancillas := [{ code := "reg", logical := "a0", basis := .zero },
                 { code := "reg", logical := "a1", basis := .plus }] }
example : ok? (compileQASMToMixIR? [] progHM reqHM) = true := by decide

-- Single qubit Paulis `X; Z` (no ancilla consumed, but reservation is still required):
def progXZ : QASMProgram :=
  { qregs := [⟨"q", 1⟩], cregs := [],
    instrs := [.x ⟨"q", 0⟩, .z ⟨"q", 0⟩] }
example : ok? (compileQASMToMixIR? [] progXZ reqHM) = true := by decide

-- Single qubit `S; measure` (S teleports through the ancilla as well):
def progSM : QASMProgram :=
  { qregs := [⟨"q", 1⟩], cregs := [⟨"c", 1⟩],
    instrs := [.s ⟨"q", 0⟩, .measure ⟨"q", 0⟩ ⟨"c", 0⟩] }
example : ok? (compileQASMToMixIR? [] progSM reqHM) = true := by decide

-- Two qubit `CX` via a PPM gadget (control/target two data logicals, scratch `a0`):
def progCX : QASMProgram :=
  { qregs := [⟨"q", 2⟩], cregs := [],
    instrs := [.cx ⟨"q", 0⟩ ⟨"q", 1⟩] }
def reqCX : AllocationRequest :=
  { decls := [cx3Decl], dataLogicals := [⟨"reg", "d0"⟩, ⟨"reg", "d1"⟩],
    ancillas := [{ code := "reg", logical := "a0", basis := .plus }] }
example : ok? (compileQASMToMixIR? [] progCX reqCX) = true := by decide

-- Two qubit `CZ` via a PPM gadget:
def progCZ : QASMProgram :=
  { qregs := [⟨"q", 2⟩], cregs := [],
    instrs := [.cz ⟨"q", 0⟩ ⟨"q", 1⟩] }
example : ok? (compileQASMToMixIR? [] progCZ reqCX) = true := by decide

-- `T` produces a (typed, deferred) magic obligation:
def progT : QASMProgram :=
  { qregs := [⟨"q", 1⟩], cregs := [], instrs := [.t ⟨"q", 0⟩] }
def reqT : AllocationRequest :=
  { decls := [reg2Decl], dataLogicals := [⟨"reg", "d0"⟩], ancillas := [] }
example : ok? (compileQASMToMixIR? [] progT reqT) = true := by decide
example :
    (match compileQASMToMixIR? [] progT reqT with
     | .ok a    => a.obligations.contains .magicStateDeferred
     | .error _ => false) = true := by decide

-- Two qubits, two measurements: each gets a FRESH outcome CVar = 3·N + j (here N = 2),
-- disjoint from the gadget vars `[0, 3·N)` and distinct per measurement:
def progMM : QASMProgram :=
  { qregs := [⟨"q", 2⟩], cregs := [⟨"c", 2⟩],
    instrs := [.measure ⟨"q", 0⟩ ⟨"c", 0⟩, .measure ⟨"q", 1⟩ ⟨"c", 1⟩] }
def reqMM : AllocationRequest :=
  { decls := [mm4Decl], dataLogicals := [⟨"reg", "d0"⟩, ⟨"reg", "d1"⟩],
    ancillas := [] }
example : ok? (compileQASMToMixIR? [] progMM reqMM) = true := by decide
example : (match allocate? progMM reqMM with | .ok a => a.measMap | .error _ => []) = [(⟨"c", 0⟩, 6), (⟨"c", 1⟩, 7)] := by decide

-- The SSA payoff: writing the SAME classical bit twice gets two DISTINCT CVars, so the
-- repeated write does NOT violate PPM single-assignment (compiles, distinct outcomes):
def progDup : QASMProgram :=
  { qregs := [⟨"q", 1⟩], cregs := [⟨"c", 1⟩],
    instrs := [.measure ⟨"q", 0⟩ ⟨"c", 0⟩, .measure ⟨"q", 0⟩ ⟨"c", 0⟩] }
example : ok? (compileQASMToMixIR? [] progDup reqHM) = true := by decide
example : (match allocate? progDup reqHM with | .ok a => a.measMap | .error _ => []) = [(⟨"c", 0⟩, 6), (⟨"c", 0⟩, 7)] := by decide

-- Barriers are dropped (the program still compiles, op count unchanged):
example : ok? (compileQASMToMixIR? []
    { progXZ with instrs := .barrier [⟨"q", 0⟩] :: progXZ.instrs } reqHM) = true := by decide

-- `CX` via a VERIFIED transversal CNOT (incidence supplied) on two separate code blocks;
-- the conservative rule still reserves one (here unused) ancilla, in its own block:
def ctrlD : ChainQ.NamedCodeDecl := { ChainQ.indexedBareDecl with name := "ctrl" }
def tgtD  : ChainQ.NamedCodeDecl := { ChainQ.indexedBareDecl with name := "tgt" }
def ancD  : ChainQ.NamedCodeDecl := { ChainQ.indexedBareDecl with name := "anc" }
def reqTCX : AllocationRequest :=
  { decls := [ctrlD, tgtD, ancD],
    dataLogicals := [⟨"ctrl", "data"⟩, ⟨"tgt", "data"⟩],
    ancillas := [],
    cnotIncidence := some [[true]] }
example : ok? (compileQASMToMixIR? [] progCX reqTCX) = true := by decide
example :
    (match compileQASMToMixIR? [] progCX reqTCX with
     | .ok a => a.compiled.rules = [.transversalCNOT]
     | .error _ => false) = true := by decide

-- Surface-code distance-2 and distance-3 declarations: logical Pauli plus readout
-- compiles with no gadget ancillas.
def progPauliReadout : QASMProgram :=
  { qregs := [⟨"q", 1⟩], cregs := [⟨"c", 1⟩],
    instrs := [.x ⟨"q", 0⟩, .measure ⟨"q", 0⟩ ⟨"c", 0⟩] }
def reqSurface2 : AllocationRequest :=
  { decls := [surface2Decl], dataLogicals := [⟨"surf2", "data"⟩], ancillas := [] }
def reqSurface3 : AllocationRequest :=
  { decls := [surface3Decl], dataLogicals := [⟨"surf3", "data"⟩], ancillas := [] }
example : ok? (compileQASMToMixIR? [] progPauliReadout reqSurface2) = true := by decide
example : ok? (compileQASMToMixIR? [] progPauliReadout reqSurface3) = true := by decide

-- Toric distance-2: two logicals in one block, using only Paulis/readout (no gadget).
def progTwoReadout : QASMProgram :=
  { qregs := [⟨"q", 2⟩], cregs := [⟨"c", 2⟩],
    instrs := [.x ⟨"q", 0⟩, .z ⟨"q", 1⟩,
               .measure ⟨"q", 0⟩ ⟨"c", 0⟩, .measure ⟨"q", 1⟩ ⟨"c", 1⟩] }
def reqToric2 : AllocationRequest :=
  { decls := [toric2Decl],
    dataLogicals := [⟨"toric2", "a"⟩, ⟨"toric2", "b"⟩],
    ancillas := [] }
example : ok? (compileQASMToMixIR? [] progTwoReadout reqToric2) = true := by decide

-- Toy LP code: same allocator surface over a different ChainQ code family/view.
def reqToyLP3 : AllocationRequest :=
  { decls := [toyLP3Decl],
    dataLogicals := [⟨"lp3", "global_a"⟩, ⟨"lp3", "bridge_ab"⟩],
    ancillas := [] }
example : ok? (compileQASMToMixIR? [] progTwoReadout reqToyLP3) = true := by decide

/-! ## §7. Tests — NEGATIVE (rejected as honest "not compatible" results). -/

-- too few data logicals (2 virtual qubits, 1 data logical):
example : ok? (compileQASMToMixIR? [] progCX { reqCX with dataLogicals := [⟨"reg", "d0"⟩] }) = false := by decide
-- duplicate data logical (two virtual qubits alias one logical):
example : ok? (compileQASMToMixIR? [] progCX
    { reqCX with dataLogicals := [⟨"reg", "d0"⟩, ⟨"reg", "d0"⟩] }) = false := by decide
-- data / ancilla overlap (an ancilla aliases the data logical):
example : ok? (compileQASMToMixIR? [] progHM
    { reqHM with ancillas := [{ code := "reg", logical := "d0", basis := .zero },
                              { code := "reg", logical := "a1", basis := .plus }] }) = false := by decide
-- wrong basis: H needs a `.zero` ancilla, not `.plus`:
example : ok? (compileQASMToMixIR? [] progHM
    { reqHM with ancillas := [{ code := "reg", logical := "a0", basis := .plus }] }) = false := by decide
-- unsupported (out-of-contract) gate:
example : ok? (compileQASMToMixIR? []
    { qregs := [⟨"q", 1⟩], cregs := [], instrs := [.unsupported "rx(0.3)"] } reqT) = false := by decide
-- invalid virtual qubit reference (index out of range of its qreg):
example : ok? (compileQASMToMixIR? []
    { qregs := [⟨"q", 1⟩], cregs := [], instrs := [.h ⟨"q", 5⟩] } reqT) = false := by decide
-- invalid virtual qubit reference inside a barrier is still rejected:
example : ok? (compileQASMToMixIR? []
    { qregs := [⟨"q", 1⟩], cregs := [], instrs := [.barrier [⟨"q", 5⟩]] } reqT) = false := by decide
-- invalid classical bit reference:
example : ok? (compileQASMToMixIR? []
    { qregs := [⟨"q", 1⟩], cregs := [⟨"c", 1⟩],
      instrs := [.measure ⟨"q", 0⟩ ⟨"c", 4⟩] } reqT) = false := by decide
-- duplicate qreg/creg names are rejected before allocation can become ambiguous:
example : ok? (compileQASMToMixIR? []
    { qregs := [⟨"q", 1⟩, ⟨"q", 1⟩], cregs := [], instrs := [.x ⟨"q", 0⟩] }
    { reqCX with dataLogicals := [⟨"reg", "d0"⟩, ⟨"reg", "d1"⟩] }) = false := by decide
example : ok? (compileQASMToMixIR? []
    { qregs := [⟨"q", 1⟩], cregs := [⟨"c", 1⟩, ⟨"c", 1⟩],
      instrs := [.measure ⟨"q", 0⟩ ⟨"c", 0⟩] } reqT) = false := by decide
-- unsupported gates are rejected even when they are not first in the instruction stream:
example : ok? (compileQASMToMixIR? []
    { qregs := [⟨"q", 1⟩], cregs := [], instrs := [.x ⟨"q", 0⟩, .unsupported "reset"] }
    reqT) = false := by decide
-- extra supplied data resources are also checked for duplicates/overlap/resolution:
example : ok? (compileQASMToMixIR? [] progHM
    { reqHM with dataLogicals := [⟨"reg", "d0"⟩, ⟨"reg", "d0"⟩] }) = false := by decide
example : ok? (compileQASMToMixIR? [] progHM
    { reqHM with dataLogicals := [⟨"reg", "d0"⟩, ⟨"reg", "a0"⟩] }) = false := by decide
example : ok? (compileQASMToMixIR? [] progHM
    { reqHM with dataLogicals := [⟨"reg", "d0"⟩, ⟨"ghost", "d0"⟩] }) = false := by decide
-- duplicate ancilla declarations are rejected even if the basis tags differ:
example : ok? (compileQASMToMixIR? [] progHM
    { reqHM with ancillas := [{ code := "reg", logical := "a0", basis := .zero },
                              { code := "reg", logical := "a0", basis := .plus }] }) = false := by decide
-- STRICT mode (explicit): an inapplicable transversal rule must FAIL, never fall back:
example : ok? (compileQASMToMixIR? [] progCX
    { reqCX with cnotMode := .strictTransversal, cnotIncidence := some [[true]] }) = false := by decide
-- DEFAULT FALLBACK mode: the same inapplicable transversal falls back to the PPM gadget and
-- the CNOT still compiles (the incidence is a HINT, not an all-or-nothing requirement):
example : ok? (compileQASMToMixIR? [] progCX { reqCX with cnotIncidence := some [[true]] }) = true := by decide
-- unknown code name (name resolution fails):
example : ok? (compileQASMToMixIR? [] progHM { reqHM with dataLogicals := [⟨"ghost", "d0"⟩] }) = false := by decide

end Compiler.QASM
