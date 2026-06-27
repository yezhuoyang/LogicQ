/-
  Compiler.Mixed.Lower.Ancilla — the ancilla allocation discipline: the internal
  address supply (`AncillaSupply`), the proof-carrying checked pool
  (`AncBasis`/`AncStatus`/`AncEntry`/`AncillaPool` + `alloc`/`alloc_valid`), and
  `compileProgramLocA` + soundness (split out of Compiler/Mixed/Lower.lean).
-/
import Compiler.Mixed.Lower.LocMap

namespace Compiler
open TypeChecker PPM ChainQ.GF2 Logical

/-! ### Ancilla allocation discipline (M13 task 4).

    A single fixed ancilla is reused across all PPM fallbacks (M12 review:
    `single-anc-reuse`).  `AncillaSupply` allocates a FRESH ancilla per op, so two
    fallbacks on the same canonical qubit use DISTINCT ancillas. -/

/-- INTERNAL (M15): a bare logical-ancilla ADDRESS counter handing out
    `⟨block, next⟩`, `⟨block, next+1⟩`, … .  It proves nothing about the addresses;
    the PUBLIC resource is the runtime-checked `ResourcePool` (= `AncillaPool`) in
    `CompileConfig` (validity/liveness/basis/ownership).  `AncillaSupply` remains the
    internal address generator threaded by `compileProgramLocA`. -/
structure AncillaSupply where
  block : Nat
  next  : Nat
  deriving Repr, DecidableEq

/-- The supply seeded at a base ancilla qubit. -/
def AncillaSupply.fromQ (anc : LQubit) : AncillaSupply := ⟨anc.blk, anc.idx⟩

/-- Allocate the next fresh ancilla, advancing the supply. -/
def AncillaSupply.alloc (s : AncillaSupply) : LQubit × AncillaSupply :=
  (⟨s.block, s.next⟩, { s with next := s.next + 1 })

/-! ### A CHECKED ancilla pool (M14 task 3).

    `AncillaSupply` hands out fresh ADDRESSES but proves nothing about them.  An
    `AncillaPool` is a PROOF-CARRYING resource: each entry declares a logical
    qubit, the BASIS it is prepared in (`zero`/`plus`/`magicH`/`magicT`), and its
    OWNERSHIP (`available`/`consumed`/`discarded`).  Allocation succeeds only for an
    AVAILABLE entry of the requested basis that is `validLQubit` and NOT discarded —
    and marks it consumed (so it is never re-issued). -/

/-- The basis an ancilla must be prepared in for a gadget. -/
inductive AncBasis
  | zero | plus | magicH | magicT
  deriving DecidableEq, Repr

/-- The ownership status of a pool ancilla. -/
inductive AncStatus
  | available | consumed | discarded
  deriving DecidableEq, Repr

/-- A pool ancilla: a logical qubit, the basis it holds, and its status. -/
structure AncEntry where
  q      : LQubit
  basis  : AncBasis
  status : AncStatus
  deriving Repr

/-- A checked ancilla pool. -/
structure AncillaPool where
  entries : List AncEntry
  deriving Repr

/-- Is an entry available, of the right basis, valid, and not discarded? -/
def AncEntry.usable (Γ : TypedEnv) (R : PPMState) (basis : AncBasis) (e : AncEntry) : Bool :=
  e.status == .available && e.basis == basis && validLQubit Γ e.q && ! R.dead.contains e.q

/-- Allocate an ancilla of the requested basis: find a USABLE entry (available,
    right basis, valid, not discarded), mark it CONSUMED, and return it.  Fails if
    none exists. -/
def AncillaPool.alloc (Γ : TypedEnv) (R : PPMState) (basis : AncBasis) (p : AncillaPool) :
    Except TypeError (LQubit × AncillaPool) :=
  match p.entries.find? (AncEntry.usable Γ R basis) with
  | some e => .ok (e.q, ⟨p.entries.map (fun e' => if e'.q == e.q then { e' with status := .consumed } else e')⟩)
  | none   => .error (.other "no available ancilla of the required basis (valid / live / not-discarded)")

/-- **Allocation is CHECKED**: a successfully-allocated ancilla is a VALID logical
    qubit that is NOT discarded — not merely a fresh name. -/
theorem AncillaPool.alloc_valid (Γ : TypedEnv) (R : PPMState) (basis : AncBasis) (p : AncillaPool)
    {q : LQubit} {p' : AncillaPool} (h : AncillaPool.alloc Γ R basis p = .ok (q, p')) :
    validLQubit Γ q = true ∧ R.dead.contains q = false := by
  unfold AncillaPool.alloc at h
  cases hf : p.entries.find? (AncEntry.usable Γ R basis) with
  | none => rw [hf] at h; exact absurd h (by simp)
  | some e =>
    rw [hf] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, _⟩ := h
    have hp := List.find?_some hf
    simp only [AncEntry.usable, Bool.and_eq_true, Bool.not_eq_true'] at hp
    exact ⟨hp.1.2, hp.2⟩

/-- `compileProgramLoc` threading an ANCILLA SUPPLY: each op allocates a FRESH
    ancilla (so repeated PPM fallbacks never reuse one), resolves operands through
    the map, compiles, and relocates the canonical name to the freshly-allocated
    ancilla. -/
def compileProgramLocA (caps : List Capability) :
    TypedEnv → PPMState → CVar → LocMap → AncillaSupply → List LogicalOp →
    Except TypeError (LogicalExec × TypedEnv × PPMState × LocMap × AncillaSupply)
  | Γ, R, _, m, sup, []          => .ok ([], Γ, R, m, sup)
  | Γ, R, fresh, m, sup, op :: rest =>
      let anc := sup.alloc.1
      match compileOpR caps Γ R anc fresh (fresh + 1) (fresh + 2) (op.resolve m) with
      | .error e => .error e
      | .ok (instr, Γ', R') =>
        match compileProgramLocA caps Γ' R' (fresh + 3)
            (relocateOnFallback anc op instr m) sup.alloc.2 rest with
        | .error e => .error e
        | .ok (instrs, Γ'', R'', m'', sup'') => .ok (instr :: instrs, Γ'', R'', m'', sup'')

/-- **`compileProgramLocA` is SOUND** (same as `compileProgramLoc_sound`; the
    ancilla supply is threaded orthogonally to type-checking). -/
theorem compileProgramLocA_sound (caps : List Capability) :
    ∀ (ops : List LogicalOp) (Γ : TypedEnv) (R : PPMState) (fresh : CVar) (m : LocMap)
      (sup : AncillaSupply)
      {prog : LogicalExec} {Γ' : TypedEnv} {R' : PPMState} {m' : LocMap} {sup' : AncillaSupply},
      compileProgramLocA caps Γ R fresh m sup ops = .ok (prog, Γ', R', m', sup') →
      checkLogicalExecAux caps Γ R prog = .ok (Γ', R') := by
  intro ops
  induction ops with
  | nil =>
    intro Γ R fresh m sup prog Γ' R' m' sup' h
    simp only [compileProgramLocA, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl, _, _⟩ := h; rfl
  | cons op rest ih =>
    intro Γ R fresh m sup prog Γ' R' m' sup' h
    simp only [compileProgramLocA] at h
    cases hc : compileOpR caps Γ R sup.alloc.1 fresh (fresh + 1) (fresh + 2) (op.resolve m) with
    | error e => simp only [hc] at h; exact absurd h (by simp)
    | ok p1 =>
      obtain ⟨instr, Γ₁, R₁⟩ := p1
      cases hrest : compileProgramLocA caps Γ₁ R₁ (fresh + 3)
          (relocateOnFallback sup.alloc.1 op instr m) sup.alloc.2 rest with
      | error e => simp only [hc, hrest] at h; exact absurd h (by simp)
      | ok p2 =>
        obtain ⟨instrs, Γ₂, R₂, m₂, sup₂⟩ := p2
        simp only [hc, hrest, Except.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, _, _⟩ := h
        have hi := compileOp_sound caps Γ R sup.alloc.1 fresh (fresh + 1) (fresh + 2) (op.resolve m) hc
        simp only [checkLogicalExecAux, hi]
        exact ih _ _ _ _ _ hrest

end Compiler
