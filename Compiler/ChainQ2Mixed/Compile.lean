/-
  Compiler.ChainQ2Mixed.Compile — the ChainQ-facing source → MixIR compiler.

  Compiles a NAMED ChainQ logical program to checked MixIR primitives, preserving ChainQ
  logical addressing and WITHOUT cheating around PPM teleportation, ancillas, block-level
  resource transformations, or rule completeness.

    * NAMED ADDRESSING + LOCATION MAP.  Source ops address a code block by CODE NAME and a
      logical qubit by LOGICAL NAME.  Names resolve to a CANONICAL `LQubit`; a `LocMap`
      tracks where each canonical name's logical state CURRENTLY lives.  An H/S PPM
      teleportation gadget discards the carrier and moves the state to an ancilla, so it
      RELOCATES the canonical name (reusing `Compiler.LocMap`); later ops resolve operands
      through `loc`.  The final map is preserved in `CompiledMixIR.locOut`.

    * NAMED, BASIS-CHECKED ANCILLA POOL.  PPM teleportation gadgets need a PREPARED ancilla
      (`progHAt` needs `|0⟩`, `progSAt`/`progCNOTAt`/`progCZAt` need `|+⟩`).  The source
      DECLARES ancilla resources by `(codeName, logicalName, basis)` (`StrategyConfig.ancillas`,
      a `List NamedAnc`), resolved to a checked `AncillaPool`.  Each gadget ALLOCATES the
      basis it requires via `AncillaPool.alloc` (which checks valid / live / available /
      basis-match and marks the entry CONSUMED), so the wrong basis, a consumed ancilla, a
      dead ancilla, or running out is REJECTED.  HONESTY: the basis is a DECLARED
      consistency fact, not an operational |0⟩/|+⟩ proof — every gadget records a
      `logicalAncillaDeferred` obligation (the preparation is assumed, not modeled).

    * BLOCK-LEVEL RESOURCE DISCIPLINE.  A block-level op (`automorphism` / `blockTransversal`
      / `transversalBatch` / `codeSwitch`) transforms a whole block, so any reserved ancilla
      in that block is no longer in its declared basis.  `compileGo` POISONS the pool's
      entries in a touched block (marks them `discarded`); a later gadget that needs one of
      them then fails to allocate.  Block-level ops on UNRELATED blocks do not poison
      unrelated ancillas.

    * ENTRY DISJOINTNESS.  At entry, `ancDeclDisjoint` requires the declared ancillas to be
      disjoint from every logical the program addresses as a DATA operand — declaring a
      logical as an ancilla is allowed only if it is never read as data.

  SCOPE (honest): LOGICAL-LEGALITY + ADDRESSING + RESOURCE (SSA / ancilla-basis-declaration /
  use-after-discard / consumption) soundness only.  NOT operational equivalence, NOT QStab
  lowering, NOT fault tolerance, NOT ancilla-STATE (preparation) soundness.  `measure`
  compiles to NATIVE one- or two-body PPM with NO witness; a HIGH-WEIGHT (>2-body) measure
  compiles ONLY through a `CapabilityWitness` whose merged-code certificate (recomputed by
  `checkPPM`) proves the target is measured — the public boundary `compileChainQToMixIR?`
  takes `List CapabilityWitness`, so a RAW `.productSurgery` capability can never be supplied.
  The chain-cert homomorphic-CNOT/GPPM protocols remain unverified `Primitive.ExternalClaim`s;
  the verified (homomorphic) logical CNOT is `transversalCNOT`/`transversalBatch`.
-/
import Compiler.ChainQ2Mixed.Primitive

namespace Compiler.ChainQ2Mixed

open Compiler TypeChecker PPM ChainQ.GF2 Logical Compiler.CodeSwitch

/-! ## §C.1. ChainQ addressing context (preserves code/logical names). -/

/-- The named code declarations, their elaborated typed interfaces (the name tables), and
    the current typed environment (updated by a `codeSwitch`). -/
structure ChainQAddrCtx where
  decls  : List ChainQ.NamedCodeDecl
  ifaces : List TypedLogicalInterface
  env    : TypedEnv

/-- Build an addressing context from named ChainQ declarations (reuses `elabDecls?`). -/
def mkAddrCtx? (decls : List ChainQ.NamedCodeDecl) : Except TypeError ChainQAddrCtx := do
  let ifaces ← elabDecls? decls
  return { decls := decls, ifaces := ifaces, env := { blocks := ifaces.map (·.block) } }

/-- Resolve `(codeName, logicalName)` to its CANONICAL `LQubit` (reuses `resolveLQubit?`). -/
def ChainQAddrCtx.qubit? (ctx : ChainQAddrCtx) (code logical : String) : Except TypeError LQubit :=
  resolveLQubit? ctx.decls ctx.ifaces code logical

/-- Resolve a code name to its block id (reuses `resolveBlock?`). -/
def ChainQAddrCtx.block? (ctx : ChainQAddrCtx) (code : String) : Except TypeError Nat :=
  resolveBlock? ctx.decls code

/-- Reverse map: the code name of a block id (round-trip / diagnostics). -/
def ChainQAddrCtx.codeName? (ctx : ChainQAddrCtx) (b : Nat) : Option String :=
  (ctx.decls[b]?).map (·.name)

/-- Reverse map: the logical name of a CANONICAL `LQubit` (round-trip / diagnostics). -/
def ChainQAddrCtx.logicalName? (ctx : ChainQAddrCtx) (q : LQubit) : Option String :=
  (ctx.ifaces[q.blk]?).bind (fun iface => iface.names[q.idx]?)

/-- Elaborate a named ChainQ code declaration to its target `Block` (for code switching). -/
def resolveTargetBlock? (decl : ChainQ.NamedCodeDecl) : Except TypeError Block :=
  match decl.checkLogicalIndex? with
  | .error _ => .error (.other s!"ChainQ2Mixed.Compile: code-switch target '{decl.name}' failed to elaborate/index")
  | .ok idx  => (checkedIndexToTypedInterface? idx).map (fun iface => iface.block.block)

/-! ## §C.2. Named source ops (LOC-aware resolution). -/

/-- A named logical Pauli factor: `(codeName, logicalName, letter)`. -/
abbrev NamedFactor := String × String × PLetter

/-- Resolve a named factor to `(carrier × letter)` THROUGH the location map. -/
def ChainQAddrCtx.factorLoc? (ctx : ChainQAddrCtx) (loc : LocMap) (f : NamedFactor) :
    Except TypeError (LQubit × PLetter) :=
  (ctx.qubit? f.1 f.2.1).map (fun q => (loc.loc q, f.2.2))

/-- Resolve a named measurement target to an `MTarget` (operands at their current carriers). -/
def ChainQAddrCtx.mtargetLoc? (ctx : ChainQAddrCtx) (loc : LocMap) (factors : List NamedFactor) :
    Except TypeError MTarget :=
  factors.mapM (ctx.factorLoc? loc)

/-- Resolve a named parallel schedule to a `Schedule`. -/
def ChainQAddrCtx.scheduleLoc? (ctx : ChainQAddrCtx) (loc : LocMap)
    (layers : List (List (CVar × List NamedFactor))) : Except TypeError Schedule :=
  layers.mapM (fun layer => layer.mapM (fun rf => (ctx.mtargetLoc? loc rf.2).map (fun P => (rf.1, P))))

/-- The ChainQ-facing logical operation, addressed by CODE / LOGICAL NAMES. -/
inductive ChainQPrimOp
  | measure          (r : CVar) (factors : List NamedFactor)
  | parallelPPM      (mode : ScheduleMode) (layers : List (List (CVar × List NamedFactor)))
  | hGate            (code logical : String)
  | sGate            (code logical : String)
  | xGate            (code logical : String)
  | zGate            (code logical : String)
  | cnotGate         (cCode cLogical tCode tLogical : String)
  | czGate           (cCode cLogical tCode tLogical : String)
  | blockTransversal (code : String) (g : BoolMat)
  | automorphism     (code : String) (M : BoolMat)
  | transversalCNOT  (cCode cLogical tCode tLogical : String) (incidence : BoolMat)
  | transversalBatch (cCode tCode : String) (incidence logicalIncidence : BoolMat)
  | codeSwitch       (sourceCode : String) (targetDecl : ChainQ.NamedCodeDecl) (cert : SwitchCert)
  | tGate            (code logical : String)

/-! ## §C.3. Strategy config + the NAMED, BASIS-CHECKED ancilla pool. -/

/-- A named, basis-tagged ancilla resource declaration: which `(code, logical)` qubit, and
    the basis it is DECLARED to be prepared in. -/
structure NamedAnc where
  code    : String
  logical : String
  basis   : AncBasis
  deriving Repr

/-- How a bare `cnotGate` is realized (the per-op CNOT strategy — not a global
    all-or-nothing switch). -/
inductive CNOTMode
  | preferTransversalWithPPMFallback  -- transversal CNOT (if an incidence is supplied) THEN PPM gadget
  | strictTransversal                 -- transversal CNOT only — reject if inapplicable, NO PPM fallback
  | ppmOnly                           -- PPM gadget only
  deriving DecidableEq, Repr

/-- Compile-time strategy: the declared ancilla resources, the CNOT realization mode, and an
    optional physical incidence enabling the `transversalCNOT` rule for a bare `cnotGate`. -/
structure StrategyConfig where
  ancillas      : List NamedAnc := []
  cnotMode      : CNOTMode := .preferTransversalWithPPMFallback
  cnotIncidence : Option BoolMat := none

/-- Resolve a named ancilla declaration to an available `AncEntry`. -/
def ChainQAddrCtx.ancEntry? (ctx : ChainQAddrCtx) (na : NamedAnc) : Except TypeError AncEntry :=
  (ctx.qubit? na.code na.logical).map (fun q => { q := q, basis := na.basis, status := .available })

/-- Resolve the declared ancilla resources to a checked `AncillaPool`. -/
def ChainQAddrCtx.ancPool? (ctx : ChainQAddrCtx) (ancs : List NamedAnc) : Except TypeError AncillaPool :=
  (ancs.mapM ctx.ancEntry?).map AncillaPool.mk

/-- The canonical qubits of the declared ancilla resources (best-effort resolution). -/
def ChainQAddrCtx.ancQubits? (ctx : ChainQAddrCtx) (ancs : List NamedAnc) : List LQubit :=
  ancs.filterMap (fun na => match ctx.qubit? na.code na.logical with | .ok q => some q | _ => none)

/-- Mark every pool entry on block `b` as DISCARDED (a block-level op transformed it, so it
    is no longer in its declared basis). -/
def poisonBlock (b : Nat) (p : AncillaPool) : AncillaPool :=
  ⟨p.entries.map (fun e => if e.q.blk == b then { e with status := .discarded } else e)⟩

/-! ## §C.4. The fixed compilation-rule table. -/

/-- A MixIR realization choice for a ChainQ logical op.  (GPPM is intentionally ABSENT:
    it is not a verified realization — see `Primitive.ExternalClaim`.) -/
inductive CompileRule
  | directTransversal | ppmGadget | pauli | transversalCNOT | transversalBatch
  | automorphism | codeSwitchThen | magicObligation
  deriving DecidableEq, Repr

/-- The ancilla BASIS a `(op, rule)` pair requires (`none` if it needs no gadget ancilla). -/
def ruleAncBasis? : ChainQPrimOp → CompileRule → Option AncBasis
  | .hGate _ _,        .ppmGadget => some .zero
  | .sGate _ _,        .ppmGadget => some .plus
  | .cnotGate _ _ _ _, .ppmGadget => some .plus
  | .czGate _ _ _ _,   .ppmGadget => some .plus
  | _, _ => none

/-- **The fixed rule table.**  Resolves named operands THROUGH `loc`, builds the checked
    `MixPrim`, returns its extra obligations, and a relocation `some (canonical, anc)` when
    an H/S PPM gadget teleports the canonical name to the (already-allocated) ancilla `anc`.
    Ancilla VALIDITY/BASIS is enforced by the pool `alloc` in `compileOpWithRule?` before
    this is called — gadget arms simply use the supplied `anc`. -/
def buildPrim? (ctx : ChainQAddrCtx) (loc : LocMap) (cfg : StrategyConfig)
    (anc : LQubit) (r₁ r₂ r₃ : CVar) :
    ChainQPrimOp → CompileRule → Except TypeError (MixPrim × List PrimitiveObligation × Option (LQubit × LQubit))
  | .hGate c l, .directTransversal => do
      let q ← ctx.qubit? c l
      if singleLogicalBlock ctx.env (loc.loc q).blk then .ok (.transversal (loc.loc q).blk hGate2x2, [], none)
      else .error (.notImplemented "directTransversal: H carrier on a multi-logical block — use a PPM gadget")
  | .hGate c l, .ppmGadget => do
      let q ← ctx.qubit? c l
      .ok (.ppmFragment (progHAt (loc.loc q) anc r₁ r₂), [.logicalAncillaDeferred], some (q, anc))
  | .sGate c l, .directTransversal => do
      let q ← ctx.qubit? c l
      if singleLogicalBlock ctx.env (loc.loc q).blk then .ok (.transversal (loc.loc q).blk sGate2x2, [], none)
      else .error (.notImplemented "directTransversal: S carrier on a multi-logical block — use a PPM gadget")
  | .sGate c l, .ppmGadget => do
      let q ← ctx.qubit? c l
      .ok (.ppmFragment (progSAt (loc.loc q) anc r₁ r₂), [.logicalAncillaDeferred], some (q, anc))
  | .xGate c l, .pauli => do let q ← ctx.qubit? c l; .ok (.pauli (loc.loc q) .X, [], none)
  | .zGate c l, .pauli => do let q ← ctx.qubit? c l; .ok (.pauli (loc.loc q) .Z, [], none)
  | .measure r factors, .ppmGadget => do let P ← ctx.mtargetLoc? loc factors; .ok (.ppm r P, [], none)
  | .parallelPPM mode layers, .ppmGadget => do let S ← ctx.scheduleLoc? loc layers; .ok (.parallelPPM mode S, [], none)
  | .cnotGate cc cl tc tl, .ppmGadget => do
      let cq ← ctx.qubit? cc cl; let tq ← ctx.qubit? tc tl
      .ok (.ppmFragment (progCNOTAt (loc.loc cq) (loc.loc tq) anc r₁ r₂ r₃), [.logicalAncillaDeferred], none)
  | .cnotGate cc cl tc tl, .transversalCNOT => do
      let cq ← ctx.qubit? cc cl; let tq ← ctx.qubit? tc tl
      match cfg.cnotIncidence with
      | some inc => .ok (.transversalCNOT { control := loc.loc cq, target := loc.loc tq, incidence := inc }, [], none)
      | none     => .error (.notImplemented "transversalCNOT rule for cnotGate needs a cnotIncidence in the StrategyConfig")
  | .czGate cc cl tc tl, .ppmGadget => do
      let cq ← ctx.qubit? cc cl; let tq ← ctx.qubit? tc tl
      .ok (.ppmFragment (progCZAt (loc.loc cq) (loc.loc tq) anc r₁ r₂ r₃), [.logicalAncillaDeferred], none)
  | .blockTransversal c g, .directTransversal => do let b ← ctx.block? c; .ok (.transversal b g, [], none)
  | .automorphism c M, .automorphism => do let b ← ctx.block? c; .ok (.automorphism b M, [], none)
  | .transversalCNOT cc cl tc tl inc, .transversalCNOT => do
      let cq ← ctx.qubit? cc cl; let tq ← ctx.qubit? tc tl
      .ok (.transversalCNOT { control := loc.loc cq, target := loc.loc tq, incidence := inc }, [], none)
  | .transversalBatch cc tc inc linc, .transversalBatch => do
      let cb ← ctx.block? cc; let tb ← ctx.block? tc
      .ok (.transversalBatch { controlBlock := cb, targetBlock := tb, incidence := inc, logicalIncidence := linc }, [], none)
  | .codeSwitch sc tdecl cert, .codeSwitchThen => do
      let b ← ctx.block? sc; let D ← resolveTargetBlock? tdecl
      .ok (.codeSwitch b D cert, [], none)
  | .tGate c l, .magicObligation => do let q ← ctx.qubit? c l; .ok (.magic { kind := .tGate, target := loc.loc q }, [], none)
  | _, _ => .error (.notImplemented "ChainQ2Mixed.Compile: compile rule not applicable to this op")

/-- The default (ordered) candidate rules.  CODE-DEPENDENT for `H`/`S`; CERT-DEPENDENT for
    `cnotGate`.  `measure` has ONLY the native PPM rule (no GPPM). -/
def defaultRulesFor (ctx : ChainQAddrCtx) (loc : LocMap) (cfg : StrategyConfig) :
    ChainQPrimOp → List CompileRule
  | .hGate c l =>
      match ctx.qubit? c l with
      | .ok q => if singleLogicalBlock ctx.env (loc.loc q).blk then [.directTransversal, .ppmGadget] else [.ppmGadget]
      | .error _ => [.directTransversal, .ppmGadget]
  | .sGate c l =>
      match ctx.qubit? c l with
      | .ok q => if singleLogicalBlock ctx.env (loc.loc q).blk then [.directTransversal, .ppmGadget] else [.ppmGadget]
      | .error _ => [.directTransversal, .ppmGadget]
  | .xGate _ _          => [.pauli]
  | .zGate _ _          => [.pauli]
  | .measure _ _        => [.ppmGadget]
  | .parallelPPM _ _    => [.ppmGadget]
  | .cnotGate _ _ _ _   =>
      match cfg.cnotMode with
      | .ppmOnly            => [.ppmGadget]
      | .strictTransversal  => [.transversalCNOT]
      | .preferTransversalWithPPMFallback =>
          match cfg.cnotIncidence with | some _ => [.transversalCNOT, .ppmGadget] | none => [.ppmGadget]
  | .czGate _ _ _ _     => [.ppmGadget]
  | .blockTransversal _ _ => [.directTransversal]
  | .automorphism _ _   => [.automorphism]
  | .transversalCNOT _ _ _ _ _ => [.transversalCNOT]
  | .transversalBatch _ _ _ _ => [.transversalBatch]
  | .codeSwitch _ _ _   => [.codeSwitchThen]
  | .tGate _ _          => [.magicObligation]

/-! ## §C.5. Compiling one op (rule-directed + pool allocation). -/

/-- A compiled ChainQ op: the rule, the checked MixIR primitive, and its obligations. -/
structure CompiledOp (caps : List Capability) (Γ : TypedEnv) (R : PPMState) where
  rule        : CompileRule
  checked     : CheckedPrimitive caps Γ R
  obligations : List PrimitiveObligation

/-- Compile one op with a SPECIFIC rule: ALLOCATE the required-basis ancilla from the pool
    (if the rule needs one — checked valid/live/available/basis, marked consumed), build the
    `MixPrim`, check it, and return the compiled op + relocation + the updated pool. -/
def compileOpWithRule? (caps : List Capability) (ctx : ChainQAddrCtx) (R : PPMState) (loc : LocMap)
    (cfg : StrategyConfig) (fresh : CVar) (pool : AncillaPool) (op : ChainQPrimOp) (rule : CompileRule) :
    Except TypeError (CompiledOp caps ctx.env R × Option (LQubit × LQubit) × AncillaPool) :=
  match ruleAncBasis? op rule with
  | none =>
      match buildPrim? ctx loc cfg ⟨0, 0⟩ fresh (fresh + 1) (fresh + 2) op rule with
      | .error e => .error e
      | .ok (prim, extra, reloc) =>
          match checkPrim? caps ctx.env R prim with
          | .ok cp   => .ok ({ rule := rule, checked := cp, obligations := cp.obligations ++ extra }, reloc, pool)
          | .error e => .error e
  | some basis =>
      match AncillaPool.alloc ctx.env R basis pool with
      | .error e => .error e
      | .ok (anc, pool') =>
          match buildPrim? ctx loc cfg anc fresh (fresh + 1) (fresh + 2) op rule with
          | .error e => .error e
          | .ok (prim, extra, reloc) =>
              match checkPrim? caps ctx.env R prim with
              | .ok cp   => .ok ({ rule := rule, checked := cp, obligations := cp.obligations ++ extra }, reloc, pool')
              | .error e => .error e

/-- Compile one op with the DEFAULT strategy: first applicable + type-checking rule. -/
def compileOp? (caps : List Capability) (ctx : ChainQAddrCtx) (R : PPMState) (loc : LocMap)
    (cfg : StrategyConfig) (fresh : CVar) (pool : AncillaPool) (op : ChainQPrimOp) :
    Except TypeError (CompiledOp caps ctx.env R × Option (LQubit × LQubit) × AncillaPool) :=
  go (defaultRulesFor ctx loc cfg op)
where
  go : List CompileRule → Except TypeError (CompiledOp caps ctx.env R × Option (LQubit × LQubit) × AncillaPool)
    | []          => .error (.notImplemented "ChainQ2Mixed.Compile: no applicable compile rule for this op")
    | rule :: rest =>
        match compileOpWithRule? caps ctx R loc cfg fresh pool op rule with
        | .ok co   => .ok co
        | .error _ => go rest

/-! ## §C.6. Compiling a whole program (env- + loc- + pool-threaded, proof-carrying). -/

/-- A compiled step: the rule, the resolved primitive, and its obligations. -/
structure CompiledStep where
  rule        : CompileRule
  prim        : MixPrim
  obligations : List PrimitiveObligation

/-- Replay primitives through `primCheck`, threading env/resources — the soundness witness. -/
def primCheckProgram (caps : List Capability) :
    TypedEnv → PPMState → List MixPrim → Except TypeError (TypedEnv × PPMState)
  | Γ, R, []        => .ok (Γ, R)
  | Γ, R, p :: rest =>
      match primCheck caps Γ R p with
      | .ok (Γ', R') => primCheckProgram caps Γ' R' rest
      | .error e     => .error e

/-- Sequencing lemma for the replay checker. -/
theorem primCheckProgram_append_ok (caps : List Capability) (ys : List MixPrim) :
    ∀ (xs : List MixPrim) (Γ R Γ₁ R₁ Γ₂ R₂),
      primCheckProgram caps Γ R xs = .ok (Γ₁, R₁) →
      primCheckProgram caps Γ₁ R₁ ys = .ok (Γ₂, R₂) →
      primCheckProgram caps Γ R (xs ++ ys) = .ok (Γ₂, R₂) := by
  intro xs
  induction xs with
  | nil =>
      intro Γ R Γ₁ R₁ Γ₂ R₂ hxs hys
      simp only [primCheckProgram, Except.ok.injEq, Prod.mk.injEq] at hxs
      obtain ⟨rfl, rfl⟩ := hxs
      exact hys
  | cons p ps ih =>
      intro Γ R Γ₁ R₁ Γ₂ R₂ hxs hys
      simp only [primCheckProgram, List.cons_append] at hxs ⊢
      cases hp : primCheck caps Γ R p with
      | error e =>
          simp only [hp] at hxs
          cases hxs
      | ok out =>
          obtain ⟨Γp, Rp⟩ := out
          simp only [hp] at hxs ⊢
          exact ih Γp Rp Γ₁ R₁ Γ₂ R₂ hxs hys

/-- Apply an op's relocation (an H/S PPM gadget teleports its canonical name to `anc`). -/
def applyReloc (loc : LocMap) : Option (LQubit × LQubit) → LocMap
  | some qa => loc.relocate qa.1 qa.2
  | none    => loc

/-- The blocks a BLOCK-AFFECTING op transforms (so reserved ancillas in them are no longer
    in their declared basis); `[]` for purely per-qubit ops.  A transversal CNOT (single or
    batched) is a PHYSICAL transversal across BOTH its blocks — `checkTransversalCNOT` only
    verifies the induced action on the two NAMED logicals, not identity on co-block reserved
    ancillas — so BOTH variants poison both blocks (conservatively).  NOTE: this poisoning is
    a separate mechanism from use-after-discard: an H/S gadget discards its data carrier, so a
    later block-level op on that block is independently rejected by the dead-qubit guard. -/
def ChainQAddrCtx.opTouchedBlocks (ctx : ChainQAddrCtx) : ChainQPrimOp → List Nat
  | .blockTransversal c _   => match ctx.block? c with | .ok b => [b] | _ => []
  | .automorphism c _       => match ctx.block? c with | .ok b => [b] | _ => []
  | .transversalCNOT cc _ tc _ _ =>
      (match ctx.block? cc with | .ok b => [b] | _ => []) ++ (match ctx.block? tc with | .ok b => [b] | _ => [])
  | .transversalBatch cc tc _ _ =>
      (match ctx.block? cc with | .ok b => [b] | _ => []) ++ (match ctx.block? tc with | .ok b => [b] | _ => [])
  | .codeSwitch sc _ _      => match ctx.block? sc with | .ok b => [b] | _ => []
  | _                       => []

/-- Poison the pool's entries in every block the op transforms. -/
def poisonTouched (ctx : ChainQAddrCtx) (op : ChainQPrimOp) (pool : AncillaPool) : AncillaPool :=
  (ctx.opTouchedBlocks op).foldl (fun p b => poisonBlock b p) pool

/-- Tail-recursive worker for `compileGo`.  `acc` stores compiled steps in reverse order. -/
def compileGoAcc (caps : List Capability) (decls : List ChainQ.NamedCodeDecl)
    (ifaces : List TypedLogicalInterface) (cfg : StrategyConfig) :
    TypedEnv → PPMState → LocMap → CVar → AncillaPool → List CompiledStep → List ChainQPrimOp →
    Except TypeError (List CompiledStep × TypedEnv × PPMState × LocMap × AncillaPool)
  | Γ, R, loc, _, pool, acc, [] => .ok (acc.reverse, Γ, R, loc, pool)
  | Γ, R, loc, fresh, pool, acc, op :: rest =>
      match compileOp? caps { decls := decls, ifaces := ifaces, env := Γ } R loc cfg fresh pool op with
      | .error e => .error e
      | .ok cor =>
          let step : CompiledStep :=
            { rule := cor.1.rule, prim := cor.1.checked.prim, obligations := cor.1.obligations }
          compileGoAcc caps decls ifaces cfg cor.1.checked.envOut cor.1.checked.resOut
              (applyReloc loc cor.2.1) (fresh + 3)
              (poisonTouched { decls := decls, ifaces := ifaces, env := Γ } op cor.2.2)
              (step :: acc) rest

/-- Compile a list of ChainQ ops, THREADING the env (a `codeSwitch` updates it), the
    LOCATION MAP, fresh outcome vars (`+3`/op), and the ANCILLA POOL (consumed per gadget;
    poisoned per block-level op). -/
def compileGo (caps : List Capability) (decls : List ChainQ.NamedCodeDecl)
    (ifaces : List TypedLogicalInterface) (cfg : StrategyConfig) :
    TypedEnv → PPMState → LocMap → CVar → AncillaPool → List ChainQPrimOp →
    Except TypeError (List CompiledStep × TypedEnv × PPMState × LocMap × AncillaPool)
  | Γ, R, loc, fresh, pool, ops => compileGoAcc caps decls ifaces cfg Γ R loc fresh pool [] ops

/-- **`compileGo` is sound**: the emitted steps' primitives all type-check IN SEQUENCE
    (`primCheckProgram`), threading the env/state — each primitive is checked at the carrier
    its operands resolve to.  (The location map and ancilla pool are threaded ORTHOGONALLY
    to type-checking.) -/
theorem compileGoAcc_sound (caps : List Capability) (decls : List ChainQ.NamedCodeDecl)
    (ifaces : List TypedLogicalInterface) (cfg : StrategyConfig) :
    ∀ (ops : List ChainQPrimOp) (Γ₀ : TypedEnv) (R₀ : PPMState)
      (Γ : TypedEnv) (R : PPMState) (loc : LocMap) (fresh : CVar)
      (pool : AncillaPool) (acc : List CompiledStep)
      {steps : List CompiledStep} {Γ' : TypedEnv} {R' : PPMState}
      {loc' : LocMap} {pool' : AncillaPool},
      primCheckProgram caps Γ₀ R₀ (acc.reverse.map (·.prim)) = .ok (Γ, R) →
      compileGoAcc caps decls ifaces cfg Γ R loc fresh pool acc ops =
        .ok (steps, Γ', R', loc', pool') →
      primCheckProgram caps Γ₀ R₀ (steps.map (·.prim)) = .ok (Γ', R') := by
  intro ops
  induction ops with
  | nil =>
      intro Γ₀ R₀ Γ R loc fresh pool acc steps Γ' R' loc' pool' hacc h
      simp only [compileGoAcc, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl, _, _⟩ := h
      exact hacc
  | cons op rest ih =>
      intro Γ₀ R₀ Γ R loc fresh pool acc steps Γ' R' loc' pool' hacc h
      simp only [compileGoAcc] at h
      cases hco : compileOp? caps { decls := decls, ifaces := ifaces, env := Γ } R loc cfg fresh pool op with
      | error e =>
          simp only [hco] at h
          cases h
      | ok cor =>
          let step : CompiledStep :=
            { rule := cor.1.rule, prim := cor.1.checked.prim, obligations := cor.1.obligations }
          have hstep : primCheckProgram caps Γ R [step.prim] =
              .ok (cor.1.checked.envOut, cor.1.checked.resOut) := by
            simp only [step, primCheckProgram, cor.1.checked.checked]
          have hacc' :
              primCheckProgram caps Γ₀ R₀ ((step :: acc).reverse.map (·.prim)) =
                .ok (cor.1.checked.envOut, cor.1.checked.resOut) := by
            simpa only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil]
              using primCheckProgram_append_ok caps [step.prim] (acc.reverse.map (·.prim)) Γ₀ R₀ Γ R
                cor.1.checked.envOut cor.1.checked.resOut hacc hstep
          have hrest :
              compileGoAcc caps decls ifaces cfg cor.1.checked.envOut cor.1.checked.resOut
                (applyReloc loc cor.2.1) (fresh + 3)
                (poisonTouched { decls := decls, ifaces := ifaces, env := Γ } op cor.2.2)
                (step :: acc) rest = .ok (steps, Γ', R', loc', pool') := by
            simpa only [hco, step] using h
          exact ih Γ₀ R₀ cor.1.checked.envOut cor.1.checked.resOut
            (applyReloc loc cor.2.1) (fresh + 3)
            (poisonTouched { decls := decls, ifaces := ifaces, env := Γ } op cor.2.2)
            (step :: acc) hacc' hrest

theorem compileGo_sound (caps : List Capability) (decls : List ChainQ.NamedCodeDecl)
    (ifaces : List TypedLogicalInterface) (cfg : StrategyConfig) :
    ∀ (ops : List ChainQPrimOp) (Γ : TypedEnv) (R : PPMState) (loc : LocMap) (fresh : CVar)
      (pool : AncillaPool) {steps : List CompiledStep} {Γ' : TypedEnv} {R' : PPMState}
      {loc' : LocMap} {pool' : AncillaPool},
      compileGo caps decls ifaces cfg Γ R loc fresh pool ops = .ok (steps, Γ', R', loc', pool') →
      primCheckProgram caps Γ R (steps.map (·.prim)) = .ok (Γ', R') := by
  intro ops Γ R loc fresh pool steps Γ' R' loc' pool' h
  exact compileGoAcc_sound caps decls ifaces cfg ops Γ R Γ R loc fresh pool [] (by rfl) h

/-- The `(codeName, logicalName)` pairs an op references as PER-QUBIT DATA operands. -/
def ChainQPrimOp.dataNames : ChainQPrimOp → List (String × String)
  | .measure _ factors        => factors.map (fun f => (f.1, f.2.1))
  | .parallelPPM _ layers      => layers.flatMap (fun layer => layer.flatMap (fun rf => rf.2.map (fun f => (f.1, f.2.1))))
  | .hGate c l                 => [(c, l)]
  | .sGate c l                 => [(c, l)]
  | .xGate c l                 => [(c, l)]
  | .zGate c l                 => [(c, l)]
  | .cnotGate cc cl tc tl      => [(cc, cl), (tc, tl)]
  | .czGate cc cl tc tl        => [(cc, cl), (tc, tl)]
  | .transversalCNOT cc cl tc tl _ => [(cc, cl), (tc, tl)]
  | .tGate c l                 => [(c, l)]
  | _                          => []

/-- The canonical logical qubits a program addresses as data operands. -/
def ChainQAddrCtx.programDataQubits (ctx : ChainQAddrCtx) (ops : List ChainQPrimOp) : List LQubit :=
  (ops.flatMap ChainQPrimOp.dataNames).filterMap (fun cl =>
    match ctx.qubit? cl.1 cl.2 with | .ok q => some q | .error _ => none)

/-- **Ancilla/data disjointness**: every declared ancilla must be disjoint from the
    logicals the program addresses as data operands (an ancilla may be used as gadget
    scratch only if it is never read as data). -/
def ancDeclDisjoint (ctx : ChainQAddrCtx) (cfg : StrategyConfig) (ops : List ChainQPrimOp) : Bool :=
  (ctx.ancQubits? cfg.ancillas).all (fun a => ! (ctx.programDataQubits ops).contains a)

/-- A proof-carrying compiled ChainQ → MixIR program.  Keeps the final LOCATION MAP and the
    final ANCILLA POOL (so resource consumption / poisoning is visible + compositional). -/
structure CompiledMixIR (caps : List Capability) where
  ctxIn   : ChainQAddrCtx
  ctxOut  : ChainQAddrCtx
  steps   : List CompiledStep
  resOut  : PPMState
  locOut  : LocMap
  poolOut : AncillaPool
  checked : primCheckProgram caps ctxIn.env PPMState.init (steps.map (·.prim)) = .ok (ctxOut.env, resOut)

/-- All deferred obligations across the compiled program. -/
def CompiledMixIR.obligations {caps : List Capability} (c : CompiledMixIR caps) : List PrimitiveObligation :=
  c.steps.flatMap (·.obligations)

/-- The rule chosen for each step (for audit). -/
def CompiledMixIR.rules {caps : List Capability} (c : CompiledMixIR caps) : List CompileRule :=
  c.steps.map (·.rule)

/-- **Query the final carrier** of a named ChainQ logical (resolves its canonical qubit,
    then follows the final location map). -/
def CompiledMixIR.carrierOf? {caps : List Capability} (c : CompiledMixIR caps)
    (code logical : String) : Option LQubit :=
  match c.ctxIn.qubit? code logical with | .ok q => some (c.locOut.loc q) | .error _ => none

/-- The final `AncStatus` of a named ancilla logical in the compiled program (`none` if the
    name does not resolve or is not a pool entry). -/
def CompiledMixIR.ancillaStatusOf? {caps : List Capability} (c : CompiledMixIR caps)
    (code logical : String) : Option AncStatus :=
  match c.ctxIn.qubit? code logical with
  | .ok q    => (c.poolOut.entries.find? (fun e => e.q == q)).map (·.status)
  | .error _ => none

/-- The still-available / consumed / discarded ancilla entries in the final pool. -/
def CompiledMixIR.availableAncillas {caps : List Capability} (c : CompiledMixIR caps) : List AncEntry :=
  c.poolOut.entries.filter (fun e => e.status == .available)
def CompiledMixIR.consumedAncillas {caps : List Capability} (c : CompiledMixIR caps) : List AncEntry :=
  c.poolOut.entries.filter (fun e => e.status == .consumed)
def CompiledMixIR.discardedAncillas {caps : List Capability} (c : CompiledMixIR caps) : List AncEntry :=
  c.poolOut.entries.filter (fun e => e.status == .discarded)

/-- **Pool invariant (poisoning).**  After `poisonBlock b`, EVERY entry on block `b` has
    status `discarded` — so a poisoned ancilla can never be re-allocated (`AncEntry.usable`
    requires `available`).  (An executable witness of the resource discipline; the
    allocation half is `Compiler.AncillaPool.alloc_valid`.) -/
theorem poisonBlock_discards (b : Nat) (p : AncillaPool) (e : AncEntry)
    (he : e ∈ (poisonBlock b p).entries) (hb : e.q.blk = b) : e.status = AncStatus.discarded := by
  simp only [poisonBlock, List.mem_map] at he
  obtain ⟨e0, _, he0⟩ := he
  split at he0
  · subst he0; rfl
  · subst he0
    rename_i hcond
    simp only [beq_iff_eq] at hcond
    exact absurd hb hcond

/-- A ChainQ source program: named code declarations + named logical operations. -/
structure ChainQPrimProgram where
  decls : List ChainQ.NamedCodeDecl
  ops   : List ChainQPrimOp

/-- **The public ChainQ → MixIR compiler.**  Elaborate the named declarations, resolve the
    declared ancilla resources into a checked `AncillaPool`, REQUIRE ancilla/data
    disjointness, then compile the ops rule-by-rule, threading the env + location map +
    ancilla pool.  The final location map is preserved in `locOut`. -/
private def compileChainQToMixIRRaw? (caps : List Capability) (cfg : StrategyConfig)
    (prog : ChainQPrimProgram) : Except TypeError (CompiledMixIR caps) := do
  let ctx ← mkAddrCtx? prog.decls
  let pool ← ctx.ancPool? cfg.ancillas
  if ! ancDeclDisjoint ctx cfg prog.ops then
    .error (.other "ChainQ2Mixed.Compile: a declared ancilla qubit is also addressed as a data operand (ancilla resources must be disjoint from data logicals)")
  else
    match h : compileGo caps prog.decls ctx.ifaces cfg ctx.env PPMState.init [] 0 pool prog.ops with
    | .ok (steps, Γ', R', loc', pool') =>
        .ok { ctxIn := ctx, ctxOut := { ctx with env := Γ' }, steps := steps, resOut := R',
              locOut := loc', poolOut := pool',
              checked := compileGo_sound caps prog.decls ctx.ifaces cfg prog.ops ctx.env PPMState.init [] 0 pool h }
    | .error e => .error e

/-- **The WITNESS-SAFE public ChainQ → MixIR compiler boundary.**  It accepts a list of
    `CapabilityWitness` (NOT raw `Capability`), converts them to capabilities INTERNALLY via
    `CapabilityWitness.toCapability`, and runs the raw compiler.  Because a witness is either
    `.generic cap (h : cap.kind ≠ .productSurgery)` or `.productSurgery cps blocks` (from a
    `CheckedProductSurgery`, connection DERIVED from the cert), a RAW `.productSurgery`
    capability can NEVER reach the compiler through this boundary — high-weight PPM is
    admitted ONLY through a witnessed adapter/product-surgery path. -/
def compileChainQToMixIR? (ws : List CapabilityWitness) (cfg : StrategyConfig)
    (prog : ChainQPrimProgram) : Except TypeError (CompiledMixIR (ws.map CapabilityWitness.toCapability)) :=
  compileChainQToMixIRRaw? (ws.map CapabilityWitness.toCapability) cfg prog

/-- **Soundness (modest, honest), raw form.**  A successfully-compiled program's primitives
    all type-check IN SEQUENCE (`primCheckProgram`), each at its current carrier.  Separately
    (operationally, NOT in this conclusion), the compiler checked ancilla allocation BEFORE
    returning (visible in `c.poolOut`).  NOT a claim of operational equivalence, ancilla-STATE
    preparation (the basis is a declared tag → `logicalAncillaDeferred`), or QStab lowering. -/
private theorem compileChainQToMixIRRaw?_sound (caps : List Capability) (cfg : StrategyConfig)
    (prog : ChainQPrimProgram) {c : CompiledMixIR caps}
    (_h : compileChainQToMixIRRaw? caps cfg prog = .ok c) :
    primCheckProgram caps c.ctxIn.env PPMState.init (c.steps.map (·.prim)) = .ok (c.ctxOut.env, c.resOut) :=
  c.checked

/-- **Public boundary soundness.**  The witness-safe compiler's emitted primitives all
    type-check in sequence against the CONVERTED capabilities `ws.map toCapability`. -/
theorem compileChainQToMixIR?_sound (ws : List CapabilityWitness) (cfg : StrategyConfig)
    (prog : ChainQPrimProgram) {c : CompiledMixIR (ws.map CapabilityWitness.toCapability)}
    (h : compileChainQToMixIR? ws cfg prog = .ok c) :
    primCheckProgram (ws.map CapabilityWitness.toCapability) c.ctxIn.env PPMState.init
        (c.steps.map (·.prim)) = .ok (c.ctxOut.env, c.resOut) :=
  compileChainQToMixIRRaw?_sound _ cfg prog h

/-! ## §C.7. Test fixtures. -/

/-- A bare 3-logical code: data logical "data" (idx 0) + two reserved ancilla logicals
    "anc0"/"anc1" (idx 1, 2).  Intra-block declared ancillas → gadget measurements type-check
    cap-free. -/
def regDecl : ChainQ.NamedCodeDecl :=
  { name := "reg",
    decl := .css { n := 3, hx := [], hz := [] },
    logicalIndex := some
      { names := ["data", "anc0", "anc1"],
        pauliBasis :=
          { zBasis    := [[true, false, false], [false, true, false], [false, false, true]],
            xDualBasis := [[true, false, false], [false, true, false], [false, false, true]] } } }

def regCtx : ChainQAddrCtx :=
  match mkAddrCtx? [regDecl] with | .ok c => c | .error _ => ⟨[], [], { blocks := [] }⟩
def twoCtx : ChainQAddrCtx :=
  match mkAddrCtx? [ChainQ.indexedTwoLogicalDecl] with | .ok c => c | .error _ => ⟨[], [], { blocks := [] }⟩
def bareCtx : ChainQAddrCtx :=
  match mkAddrCtx? [ChainQ.indexedBareDecl] with | .ok c => c | .error _ => ⟨[], [], { blocks := [] }⟩

/-- anc0 declared in |0⟩ (for H), anc1 in |+⟩ (for S). -/
def regCfg : StrategyConfig :=
  { ancillas := [{ code := "reg", logical := "anc0", basis := .zero },
                 { code := "reg", logical := "anc1", basis := .plus }] }
/-- only a |0⟩ ancilla (anc0). -/
def regZeroCfg : StrategyConfig := { ancillas := [{ code := "reg", logical := "anc0", basis := .zero }] }
/-- anc0 mis-declared as |+⟩ (so an H gadget, which needs |0⟩, must be rejected). -/
def regPlusCfg : StrategyConfig := { ancillas := [{ code := "reg", logical := "anc0", basis := .plus }] }
/-- A |+⟩ gadget ancilla (anc1) for a SAME-block CNOT, plus a (here inapplicable) global
    incidence — in the default FALLBACK mode the same-block CNOT uses the PPM gadget. -/
def regCnotCfg : StrategyConfig :=
  { ancillas := [{ code := "reg", logical := "anc1", basis := .plus }], cnotIncidence := some [[true]] }

def ctrlDecl : ChainQ.NamedCodeDecl := { ChainQ.indexedBareDecl with name := "ctrl" }
def tgtDecl  : ChainQ.NamedCodeDecl := { ChainQ.indexedBareDecl with name := "tgt" }

example : ok? regDecl.checkLogicalIndex? = true := by decide

/-! ## §C.8. Tests — RELOCATION + locOut (Fix A / Concern 3). -/

-- H(data) (multi-logical) uses the PPM fallback with a declared |0⟩ ancilla, relocating
-- "data" to anc0; measure(data) resolves to the RELOCATED carrier (a measure on the
-- discarded original would be rejected — so this passing proves relocation):
example : ok? (compileChainQToMixIR? [] regZeroCfg
    { decls := [regDecl], ops := [.hGate "reg" "data", .measure 5 [("reg", "data", .Z)]] }) = true := by decide
-- REPEATED relocation: H(data); S(data); measure(data) uses the LATEST carrier (anc1):
example : ok? (compileChainQToMixIR? [] regCfg
    { decls := [regDecl], ops := [.hGate "reg" "data", .sGate "reg" "data", .measure 5 [("reg", "data", .Z)]] }) = true := by decide
-- locOut reflects the final carrier of the named logical: after H, "data" lives at anc0 = ⟨0,1⟩:
example :
    (match compileChainQToMixIR? [] regZeroCfg { decls := [regDecl], ops := [.hGate "reg" "data"] } with
     | .ok c => c.carrierOf? "reg" "data" == some ⟨0, 1⟩ | .error _ => false) = true := by decide
-- after H; S the final carrier is the SECOND allocated ancilla anc1 = ⟨0,2⟩:
example :
    (match compileChainQToMixIR? [] regCfg { decls := [regDecl], ops := [.hGate "reg" "data", .sGate "reg" "data"] } with
     | .ok c => c.carrierOf? "reg" "data" == some ⟨0, 2⟩ | .error _ => false) = true := by decide
-- X on a relocated name acts on the carrier:
example : ok? (compileChainQToMixIR? [] regZeroCfg
    { decls := [regDecl], ops := [.hGate "reg" "data", .xGate "reg" "data"] }) = true := by decide
-- DIRECT H/S on a single-logical block: no teleportation, no ancilla declared/needed:
example : ok? (compileChainQToMixIR? [] {}
    { decls := [ChainQ.indexedBareDecl], ops := [.hGate "bare" "data", .sGate "bare" "data", .xGate "bare" "data"] }) = true := by decide

/-! ## §C.9. Tests — ANCILLA BASIS / POOL (Concern 1 / 6). -/

-- H succeeds with a |0⟩ ancilla; S succeeds with a |+⟩ ancilla (regCfg has both):
example : ok? (compileChainQToMixIR? [] regCfg { decls := [regDecl], ops := [.hGate "reg" "data"] }) = true := by decide
example : ok? (compileChainQToMixIR? [] regCfg { decls := [regDecl], ops := [.sGate "reg" "data"] }) = true := by decide
-- WRONG BASIS rejected: H needs |0⟩ but only a |+⟩ ancilla is declared:
example : ok? (compileChainQToMixIR? [] regPlusCfg { decls := [regDecl], ops := [.hGate "reg" "data"] }) = false := by decide
-- S needs |+⟩ but only a |0⟩ ancilla is declared:
example : ok? (compileChainQToMixIR? [] regZeroCfg { decls := [regDecl], ops := [.sGate "reg" "data"] }) = false := by decide
-- CONSUMED ancilla: one |0⟩ ancilla, two H gadgets — the second has no fresh |0⟩ ancilla:
example : ok? (compileChainQToMixIR? [] regZeroCfg { decls := [regDecl], ops := [.hGate "reg" "data", .hGate "reg" "data"] }) = false := by decide
-- NO declared ancilla at all: the PPM-gadget rule cannot allocate, so H is rejected:
example : ok? (compileChainQToMixIR? [] {} { decls := [regDecl], ops := [.hGate "reg" "data"] }) = false := by decide

/-! ## §C.10. Tests — BLOCK-LEVEL RESOURCE POISONING (Concern 4). -/

-- automorphism(reg) transforms the whole block, poisoning the reserved ancilla anc0; a
-- subsequent H(reg.data) that wants anc0 as |0⟩ scratch then FAILS to allocate:
example : ok? (compileChainQToMixIR? [] regZeroCfg
    { decls := [regDecl], ops := [.automorphism "reg" (idMat 6), .hGate "reg" "data"] }) = false := by decide
-- blockTransversal(reg) similarly poisons the ancilla:
example : ok? (compileChainQToMixIR? [] regZeroCfg
    { decls := [regDecl], ops := [.blockTransversal "reg" hGate2x2, .hGate "reg" "data"] }) = false := by decide
-- a block-level op on an UNRELATED block does not poison the ancilla (the gadget still works):
example : ok? (compileChainQToMixIR? [] regZeroCfg
    { decls := [regDecl, ctrlDecl], ops := [.blockTransversal "ctrl" hGate2x2, .hGate "reg" "data"] }) = true := by decide
-- a SINGLE transversal CNOT poisons BOTH its blocks too (consistent with transversalBatch —
-- it is a physical transversal across both blocks, so co-block reserved ancillas are poisoned):
example :
    (match mkAddrCtx? [ctrlDecl, tgtDecl] with
     | .ok c => c.opTouchedBlocks (.transversalCNOT "ctrl" "data" "tgt" "data" [[true]]) | .error _ => []) = [0, 1] := by decide

/-! ## §C.10b. Tests — final ANCILLA POOL preserved in the artifact (`poolOut`, Task 2). -/

-- after H(data) (PPM gadget), the |0⟩ ancilla it consumed is `consumed` in `poolOut`:
example :
    (match compileChainQToMixIR? [] regCfg { decls := [regDecl], ops := [.hGate "reg" "data"] } with
     | .ok c => c.ancillaStatusOf? "reg" "anc0" | .error _ => none) = some .consumed := by decide
-- an UNUSED ancilla (anc1, only needed by S) remains `available` after just H:
example :
    (match compileChainQToMixIR? [] regCfg { decls := [regDecl], ops := [.hGate "reg" "data"] } with
     | .ok c => c.ancillaStatusOf? "reg" "anc1" | .error _ => none) = some .available := by decide
-- a block-level op (automorphism) `discard`s/poisons the block's ancillas in `poolOut`:
example :
    (match compileChainQToMixIR? [] regZeroCfg { decls := [regDecl], ops := [.automorphism "reg" (idMat 6)] } with
     | .ok c => c.ancillaStatusOf? "reg" "anc0" | .error _ => none) = some .discarded := by decide
-- reusing a consumed ancilla is still rejected (two H gadgets, one |0⟩ ancilla):
example : ok? (compileChainQToMixIR? [] regZeroCfg
    { decls := [regDecl], ops := [.hGate "reg" "data", .hGate "reg" "data"] }) = false := by decide

/-! ## §C.11. Tests — other supported ops + codeSwitch naming (Concern 2). -/

example : ok? (compileChainQToMixIR? [] {}
    { decls := [ChainQ.indexedBareDecl], ops := [.measure 0 [("bare", "data", .Z)]] }) = true := by decide
example : ok? (compileChainQToMixIR? [] {}
    { decls := [ChainQ.indexedTwoLogicalDecl],
      ops := [.parallelPPM .directDisjoint [[(0, [("two_logicals", "left", .Z)]), (1, [("two_logicals", "right", .Z)])]]] }) = true := by decide
example : ok? (compileChainQToMixIR? [] {}
    { decls := [ctrlDecl, tgtDecl], ops := [.transversalCNOT "ctrl" "data" "tgt" "data" [[true]]] }) = true := by decide
example : ok? (compileChainQToMixIR? [] {}
    { decls := [ctrlDecl, tgtDecl], ops := [.transversalBatch "ctrl" "tgt" [[true]] [[true]]] }) = true := by decide

/-! ## §C.11b. Tests — CNOT realization mode (Task 1: per-op strategy + PPM fallback). -/

-- FALLBACK (default): a same-block CNOT compiles by the PPM gadget (valid |+⟩ ancilla) EVEN
-- THOUGH a global incidence is supplied — the transversal CNOT is inapplicable (same block),
-- so it does NOT cause rejection; it falls back:
example : ok? (compileChainQToMixIR? [] regCnotCfg
    { decls := [regDecl], ops := [.cnotGate "reg" "data" "reg" "anc0"] }) = true := by decide
-- and the rule actually CHOSEN is the PPM gadget (witness of the fallback, incidence present):
example :
    (match compileChainQToMixIR? [] regCnotCfg { decls := [regDecl], ops := [.cnotGate "reg" "data" "reg" "anc0"] } with
     | .ok c => c.rules | .error _ => []) = [.ppmGadget] := by decide
-- STRICT mode: the SAME inapplicable transversal is rejected with NO PPM fallback:
example : ok? (compileChainQToMixIR? [] { regCnotCfg with cnotMode := .strictTransversal }
    { decls := [regDecl], ops := [.cnotGate "reg" "data" "reg" "anc0"] }) = false := by decide
-- SUCCESSFUL transversal (distinct blocks, valid incidence) chooses `.transversalCNOT` FIRST
-- (before any PPM fallback), in the default fallback mode:
example :
    (match compileChainQToMixIR? [] { cnotIncidence := some [[true]] }
        { decls := [ctrlDecl, tgtDecl], ops := [.cnotGate "ctrl" "data" "tgt" "data"] } with
     | .ok c => c.rules | .error _ => []) = [.transversalCNOT] := by decide

-- CODE SWITCH (DESIGN A: source names are PRESERVED; the target supplies the new CODE but
-- not new names — the target must be arity-compatible, which `checkSwitch` enforces).  A
-- subsequent op resolves through the PRESERVED source name "bare"/"data":
example : ok? (compileChainQToMixIR? [] {}
    { decls := [ChainQ.indexedBareDecl],
      ops := [.codeSwitch "bare" ChainQ.indexedBareDecl { kind := .teleport, f := identMat 2 }, .hGate "bare" "data"] }) = true := by decide
-- ctxOut still resolves the SOURCE name "bare" (design A: names preserved through the switch):
example :
    (match compileChainQToMixIR? [] {}
        { decls := [ChainQ.indexedBareDecl],
          ops := [.codeSwitch "bare" ChainQ.indexedBareDecl { kind := .teleport, f := identMat 2 }] } with
     | .ok c => c.ctxOut.codeName? 0 == some "bare" && (ok? (c.ctxOut.qubit? "bare" "data")) | .error _ => false) = true := by decide

/-! ## §C.12. Tests — NEGATIVE (addressing / ancilla / rule legality / honest PPM scope). -/

example : ok? (compileChainQToMixIR? [] {} { decls := [ChainQ.indexedBareDecl], ops := [.hGate "ghost" "data"] }) = false := by decide
example : ok? (compileChainQToMixIR? [] {} { decls := [ChainQ.indexedBareDecl], ops := [.hGate "bare" "nope"] }) = false := by decide
example : ok? (compileChainQToMixIR? [] {}
    { decls := [ChainQ.indexedBareDecl], ops := [.measure 0 [("bare", "data", .Z)], .measure 0 [("bare", "data", .X)]] }) = false := by decide
-- a declared ancilla that is ALSO addressed as a data operand is rejected at entry:
example : ok? (compileChainQToMixIR? [] { ancillas := [{ code := "two_logicals", logical := "right", basis := .zero }] }
    { decls := [ChainQ.indexedTwoLogicalDecl], ops := [.hGate "two_logicals" "left", .measure 9 [("two_logicals", "right", .Z)]] }) = false := by decide
example : ancDeclDisjoint twoCtx { ancillas := [{ code := "two_logicals", logical := "right", basis := .zero }] }
    [.measure 9 [("two_logicals", "right", .Z)]] = false := by decide
-- bad transversal CNOT incidence (zero map requesting a CNOT) rejected:
example : ok? (compileChainQToMixIR? [] {}
    { decls := [ctrlDecl, tgtDecl], ops := [.transversalCNOT "ctrl" "data" "tgt" "data" [[false]]] }) = false := by decide
-- code switch to a mismatched-arity target rejected (checkSwitch k_C = k_D guard):
example : ok? (compileChainQToMixIR? [] {}
    { decls := [ChainQ.indexedBareDecl],
      ops := [.codeSwitch "bare" ChainQ.indexedTwoLogicalDecl { kind := .teleport, f := identMat 2 }] }) = false := by decide
-- Concern 5: a 3-body (high-weight) measurement is REJECTED with NO witness — native PPM is
-- 1-/2-body only (`MTarget.wf`); high-weight needs a capability WITNESS (see §C.12c):
example : ok? (compileChainQToMixIR? [] {}
    { decls := [regDecl], ops := [.measure 0 [("reg", "data", .Z), ("reg", "anc0", .Z), ("reg", "anc1", .Z)]] }) = false := by decide

/-! ## §C.12c. WITNESS-SAFE boundary (Concern 1): the public compiler takes
    `List CapabilityWitness`, so a raw `.productSurgery` capability CANNOT be supplied; a
    high-weight measure compiles ONLY through a witnessed adapter / product-surgery path. -/

/-- A 3-body logical-Z measurement on the bare 3-logical `reg` block. -/
def measure3 : ChainQPrimProgram :=
  { decls := [regDecl], ops := [.measure 0 [("reg", "data", .Z), ("reg", "anc0", .Z), ("reg", "anc1", .Z)]] }
/-- An ADAPTER merged capability (one auxiliary qubit) whose merged Z-stabilizers span the
    3-body data Z — NOT tagged `.productSurgery`. -/
def adapter3Cap : Capability :=
  { kind := .adapterPPM, blocks := [0], ancN := 1,
    connStab := [[false, false, false, false, true, true, true, true],
                 [false, false, false, false, false, false, false, true]] }

-- with NO witness, the high-weight measure is REJECTED:
example : ok? (compileChainQToMixIR? [] {} measure3) = false := by decide
-- through a WITNESSED adapter path, it COMPILES (the witness proves the cap is not raw product-surgery):
example : ok? (compileChainQToMixIR? [.generic adapter3Cap (by decide)] {} measure3) = true := by decide
-- a RAW `.productSurgery` capability CANNOT become a witness (provenance must be a
-- `CheckedProductSurgery`), so it can never reach the public compiler boundary:
example : ok? (genericWitness? { adapter3Cap with kind := .productSurgery }) = false := by decide
example : ok? (genericWitness? adapter3Cap) = true := by decide

/-! ## §C.12b. BOUNDARY tests — unsupported features must NOT silently compile. -/

-- A cross-block PPM CNOT WITHOUT a matching capability is REJECTED (`caps = []`): the gadget
-- `progCNOTAt` measures a joint Pauli spanning the two blocks, which needs an adapter
-- capability — so a cross-block CNOT cannot sneak through the PPM gadget cap-free:
def regCrossCfg : StrategyConfig :=
  { ancillas := [{ code := "reg", logical := "anc1", basis := .plus }], cnotMode := .ppmOnly }
example : ok? (compileChainQToMixIR? [] regCrossCfg
    { decls := [regDecl, ctrlDecl], ops := [.cnotGate "reg" "data" "ctrl" "data"] }) = false := by decide

-- GPPM is NOT an emittable source op: `ChainQPrimOp` has NO `gppm`/`homCNOT` constructor and
-- `CompileRule` has NO GPPM rule, so `compileChainQToMixIR?` can never produce a GPPM (the
-- chain-cert protocols live ONLY in the `Primitive.ExternalClaim` layer, NOT a CheckedPrimitive).
-- `measure` compiles to native 1-/2-body PPM only (see the 3-body rejection above + the
-- rule-table `measure ⇒ [ppmGadget]` below).

-- A code switch whose target has a DIFFERENT logical arity (a dimension/arity jump) is
-- REJECTED by `checkSwitch` (kC = kD): genuine dimension-jump code switching is unsupported
-- (named future work), not silently accepted (bare k=1 → two-logical k=2):
example : ok? (compileChainQToMixIR? [] {}
    { decls := [ChainQ.indexedBareDecl],
      ops := [.codeSwitch "bare" ChainQ.indexedTwoLogicalDecl { kind := .teleport, f := identMat 2 }] }) = false := by decide

/-! ## §C.13. Rule-table tests (Concern 5: GPPM absent; Concern: CNOT cert-dependent). -/

example : defaultRulesFor bareCtx [] {} (.hGate "bare" "data") = [.directTransversal, .ppmGadget] := by decide
example : defaultRulesFor twoCtx [] {} (.hGate "two_logicals" "left") = [.ppmGadget] := by decide
example : defaultRulesFor regCtx [] {} (.measure 0 [("reg", "data", .Z)]) = [.ppmGadget] := by decide
-- CNOT rule table is MODE-DEPENDENT (Task 1: per-op strategy, not a global all-or-nothing).
-- No incidence: fallback default = native PPM only.
example : defaultRulesFor twoCtx [] {} (.cnotGate "a" "x" "b" "y") = [.ppmGadget] := by decide
-- Fallback + incidence: try transversal CNOT FIRST, then fall back to PPM.
example : defaultRulesFor twoCtx [] { cnotIncidence := some [[true]] } (.cnotGate "a" "x" "b" "y")
    = [.transversalCNOT, .ppmGadget] := by decide
-- Strict mode: transversal CNOT ONLY, never PPM (rejects if inapplicable).
example : defaultRulesFor twoCtx [] { cnotMode := .strictTransversal, cnotIncidence := some [[true]] }
    (.cnotGate "a" "x" "b" "y") = [.transversalCNOT] := by decide
-- ppmOnly mode: PPM only, even when an incidence is supplied.
example : defaultRulesFor twoCtx [] { cnotMode := .ppmOnly, cnotIncidence := some [[true]] }
    (.cnotGate "a" "x" "b" "y") = [.ppmGadget] := by decide

end Compiler.ChainQ2Mixed
