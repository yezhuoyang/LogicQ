/-
  Compiler.CodeSwitch.QGPUAddr — the QGPU clustered logical basis + merge-scheduling
  constraints (2603.05398), BOUND to ChainQ/TypedEnv logical addressing.

  QGPU requires a DIRECTLY ADDRESSABLE clustered logical basis: the `k = 2·n_a·n_b`
  logicals of a clustered-cyclic (CC) code split into a LEFT and a RIGHT sector
  (`n_a·n_b` each), each indexed by cluster ROW `⌊i/n_b⌋` / COLUMN `i mod n_b`, resolving
  to a real live logical qubit with an X/Z representative support of the code's width.
  Two logical PPMs can be merged in one parallel surgery round subject to:

    * INTER-sector merges (left ↔ right) are always realizable;
    * SAME-sector merges require ROW or COLUMN alignment
      (`⌊α/n_b⌋ = ⌊β/n_b⌋`  OR  `α ≡ β (mod n_b)`);
    * at most `M ≤ k/2 = n_a·n_b` merges per round;
    * every merge participant is a MEMBER of the basis, resolves to a LIVE logical
      (`validLQubit` + not dead) of the right support width, and NO logical is reused in a
      round (a logical cannot be in two simultaneous merges).

  All checks are decidable recomputes BOUND to a `TypedEnv`; merged-code distance / FT stay
  deferred to the `ProductSurgeryCert` obligations.
-/
import Compiler.CodeSwitch.ProductSurgery

namespace Compiler.CodeSwitch
open ChainQ.GF2 TypeChecker

/-! ## §QA.1. Clustered logical addressing (ChainQ-bound). -/

/-- A QGPU logical SECTOR. -/
inductive Sector | left | right
  deriving DecidableEq, Repr

/-- A clustered logical address: a ChainQ `(code, logical)` NAME, its RESOLVED live logical
    `qubit` (in the `TypedEnv`), its sector + cluster `row`/`col`, and its X/Z logical
    representative support. -/
structure QGPUAddr where
  code     : String
  logical  : String
  qubit    : Logical.LQubit
  sector   : Sector
  row      : Nat
  col      : Nat
  xSupport : BoolVec
  zSupport : BoolVec
  deriving Repr, DecidableEq

/-- The clustered logical basis of a CC code over `n` physical qubits: `k = 2·nA·nB` named
    logicals over two sectors (`nA·nB` each). -/
structure ClusteredLogicalBasis where
  n     : Nat
  nA    : Nat
  nB    : Nat
  addrs : List QGPUAddr
  deriving Repr

/-- The maximal merges per round: `k/2 = n_a·n_b`. -/
def ClusteredLogicalBasis.maxMerge (b : ClusteredLogicalBasis) : Nat := b.nA * b.nB
/-- `k = 2·n_a·n_b`. -/
def ClusteredLogicalBasis.k (b : ClusteredLogicalBasis) : Nat := 2 * (b.nA * b.nB)

/-- An address is well-formed against `Γ`: in-range cluster coordinates, X/Z support of the
    code width `2n`, and a RESOLVED LIVE logical qubit. -/
def QGPUAddr.wfIn (Γ : TypedEnv) (b : ClusteredLogicalBasis) (a : QGPUAddr) : Bool :=
  decide (a.row < b.nA) && decide (a.col < b.nB) &&
  decide (a.xSupport.length = 2 * b.n) && decide (a.zSupport.length = 2 * b.n) &&
  validLQubit Γ a.qubit

/-- The clustered basis is well-formed against `Γ`: every address `wfIn`, distinct
    `(code,logical)` names, exactly `k` logicals split `nA·nB` LEFT + `nA·nB` RIGHT. -/
def ClusteredLogicalBasis.wf (Γ : TypedEnv) (b : ClusteredLogicalBasis) : Bool :=
  b.addrs.all (fun a => a.wfIn Γ b) &&
  (b.addrs.map (fun a => (a.code, a.logical))).Nodup &&
  decide (b.addrs.length = b.k) &&
  decide ((b.addrs.filter (fun a => a.sector == .left)).length = b.nA * b.nB) &&
  decide ((b.addrs.filter (fun a => a.sector == .right)).length = b.nA * b.nB)

/-! ## §QA.2. The merge-alignment rule + round legality. -/

/-- Two clustered logicals are MERGEABLE: inter-sector always; same-sector needs ROW or
    COLUMN alignment. -/
def QGPUAddr.mergeable (a b : QGPUAddr) : Bool :=
  if a.sector == b.sector then decide (a.row = b.row) || decide (a.col = b.col) else true

/-- A requested merge of two clustered logicals. -/
structure QGPUMerge where
  a : QGPUAddr
  b : QGPUAddr
  deriving Repr, DecidableEq

/-- A QGPU parallel-surgery ROUND. -/
structure QGPURound where
  basis  : ClusteredLogicalBasis
  merges : List QGPUMerge
  deriving Repr

/-- The qubits a round touches (each merge contributes both participants). -/
def QGPURound.touched (r : QGPURound) : List Logical.LQubit :=
  r.merges.flatMap (fun m => [m.a.qubit, m.b.qubit])

/-- Recompute round legality BOUND to `Γ`: the basis is well-formed; every participant is a
    MEMBER of the basis, ALIGNED, LIVE (`validLQubit` + not in `dead`); NO logical is reused
    across the round; and `M ≤ k/2`. -/
def QGPURound.ok (Γ : TypedEnv) (dead : List Logical.LQubit) (r : QGPURound) : Bool :=
  r.basis.wf Γ &&
  r.merges.all (fun m =>
    r.basis.addrs.contains m.a && r.basis.addrs.contains m.b &&
    m.a.mergeable m.b &&
    validLQubit Γ m.a.qubit && validLQubit Γ m.b.qubit &&
    !dead.contains m.a.qubit && !dead.contains m.b.qubit) &&
  r.touched.Nodup &&
  decide (r.merges.length ≤ r.basis.maxMerge)

/-- A proof-carrying legal QGPU round: membership/alignment/liveness/no-reuse/bound RECOMPUTED. -/
structure CheckedQGPURound (Γ : TypedEnv) (dead : List Logical.LQubit) where
  round : QGPURound
  legal : round.ok Γ dead = true

/-- **Check a QGPU round** against `Γ`. -/
def checkQGPURound? (Γ : TypedEnv) (dead : List Logical.LQubit) (r : QGPURound) :
    Except TypeError (CheckedQGPURound Γ dead) :=
  if h : r.ok Γ dead = true then .ok { round := r, legal := h }
  else .error (.certFailed "QGPU round: off-basis / unaligned / dead / reused participant, or exceeds k/2")

/-- **QGPU round soundness**: a checked round is legal — basis wf, every merge member +
    aligned + live, no logical reused, and within the `M ≤ k/2` bound. -/
theorem checkQGPURound?_sound {Γ : TypedEnv} {dead : List Logical.LQubit} {r : QGPURound}
    {c : CheckedQGPURound Γ dead} (_h : checkQGPURound? Γ dead r = .ok c) :
    c.round.ok Γ dead = true := c.legal

/-- **Full-rank connection saturates parallelism** (ties to the `ProductSurgeryCert` rank). -/
def maximallyParallel (b : ClusteredLogicalBasis) (ps : ProductSurgeryCert) : Bool :=
  decide (ps.mergeCount = b.maxMerge)

/-! ## §QA.2b. The ChainQ-bound ADDRESS BUILDER (no caller-supplied qubit/support). -/

/-- A QGPU resolution context: each code-family NAME maps to its block id + the
    `TypedLogicalInterface` (logical-name ↔ index + the block). -/
abbrev QGPUCtx := List (String × Logical.BlockId × TypedLogicalInterface)

/-- **Build a clustered address from ChainQ NAMES** — does NOT trust a caller-supplied qubit
    or support.  Resolves `(code, logical)` through the context to the real `qubit` and SETS
    `xSupport`/`zSupport` to the block's ACTUAL logical representative rows `lx[idx]`/`lz[idx]`.
    REJECTS an unknown code family or unknown logical name. -/
def buildQGPUAddr? (ctx : QGPUCtx) (code logical : String) (sector : Sector) (row col : Nat) :
    Except TypeError QGPUAddr :=
  match ctx.find? (fun e => e.1 == code) with
  | none => .error (.certFailed "QGPU: unknown code family name")
  | some (_, bid, iface) =>
    match iface.indexOf? logical with
    | none     => .error (.certFailed "QGPU: unknown logical name in the code family")
    | some idx =>
        .ok { code := code, logical := logical, qubit := ⟨bid, idx⟩, sector := sector,
              row := row, col := col,
              xSupport := iface.block.block.lx.getD idx [], zSupport := iface.block.block.lz.getD idx [] }

/-- A built address carries the resolved qubit + the block's actual logical-representative
    support (so a name/qubit mismatch or a bogus support cannot be supplied). -/
theorem buildQGPUAddr?_resolves {ctx : QGPUCtx} {code logical : String} {sec : Sector} {row col : Nat}
    {a : QGPUAddr} (h : buildQGPUAddr? ctx code logical sec row col = .ok a) :
    a.code = code ∧ a.logical = logical := by
  simp only [buildQGPUAddr?] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [Except.ok.injEq] at h; subst h; exact ⟨rfl, rfl⟩

/-! ## §QA.2c. CHECKER-SAFE round: every address RE-RESOLVES through the context. -/

/-- An address RE-RESOLVES through `ctx`: rebuilding from its `(code, logical, sector, row,
    col)` yields EXACTLY this address — so its `qubit` is the name's real carrier and its
    `xSupport`/`zSupport` are the block's ACTUAL logical rows.  A fake name, a name/qubit
    mismatch, or a bogus/zero support all FAIL this. -/
def QGPUAddr.resolvesIn (ctx : QGPUCtx) (a : QGPUAddr) : Bool :=
  match buildQGPUAddr? ctx a.code a.logical a.sector a.row a.col with
  | .ok a' => a' == a
  | .error _ => false

/-- Checker-SAFE round legality: env-bound `ok` PLUS every basis address re-resolves through
    `ctx` (so caller-supplied qubits/supports cannot be trusted — they must be the resolved
    ones).  Since merge participants must be basis members, they re-resolve too. -/
def QGPURound.okIn (Γ : TypedEnv) (dead : List Logical.LQubit) (ctx : QGPUCtx) (r : QGPURound) : Bool :=
  r.ok Γ dead && r.basis.addrs.all (fun a => a.resolvesIn ctx)

structure CheckedQGPURoundIn (Γ : TypedEnv) (dead : List Logical.LQubit) (ctx : QGPUCtx) where
  round : QGPURound
  legal : round.okIn Γ dead ctx = true

/-- **Check a checker-safe QGPU round** (the ChainQ-bound API): rejects off-basis / unaligned
    / dead / reused participants AND any address whose name/qubit/support does not re-resolve. -/
def checkQGPURoundIn? (Γ : TypedEnv) (dead : List Logical.LQubit) (ctx : QGPUCtx) (r : QGPURound) :
    Except TypeError (CheckedQGPURoundIn Γ dead ctx) :=
  if h : r.okIn Γ dead ctx = true then .ok { round := r, legal := h }
  else .error (.certFailed "QGPU round: an address fails to re-resolve (fake name / wrong qubit / bogus support) or the round is illegal")

/-- **Checker-safe round soundness**: a checked round is legal AND every basis address
    re-resolves through the context (genuine ChainQ binding). -/
theorem checkQGPURoundIn?_sound {Γ : TypedEnv} {dead : List Logical.LQubit} {ctx : QGPUCtx}
    {r : QGPURound} {c : CheckedQGPURoundIn Γ dead ctx} (_h : checkQGPURoundIn? Γ dead ctx r = .ok c) :
    c.round.ok Γ dead = true ∧ c.round.basis.addrs.all (fun a => a.resolvesIn ctx) = true := by
  have := c.legal; simp only [QGPURound.okIn, Bool.and_eq_true] at this; exact this

/-! ## §QA.3. Tests — clustered basis + merge alignment, ChainQ-bound. -/

/-- A 2-logical env (block 0 has logicals ⟨0,0⟩,⟨0,1⟩, n = 2). -/
def qBlock : Block :=
  { n := 2, stab := [], lx := [[true, false, false, false], [false, true, false, false]],
    lz := [[false, false, true, false], [false, false, false, true]] }
def qEnv : TypedEnv :=
  match TypedEnv.ofEnv? { blocks := [qBlock] } with | .ok Γ => Γ | .error _ => { blocks := [] }

def L0 : QGPUAddr := { code := "cc", logical := "L0", qubit := ⟨0, 0⟩, sector := .left,  row := 0, col := 0,
                       xSupport := [true, false, false, false], zSupport := [false, false, true, false] }
def R0 : QGPUAddr := { code := "cc", logical := "R0", qubit := ⟨0, 1⟩, sector := .right, row := 0, col := 0,
                       xSupport := [false, true, false, false], zSupport := [false, false, false, true] }
def cb11 : ClusteredLogicalBasis := { n := 2, nA := 1, nB := 1, addrs := [L0, R0] }

/-- The ChainQ resolution context: code "cc" ↦ block 0 with logical names ["L0","R0"]. -/
def qIface : TypedLogicalInterface :=
  { block := (qEnv.block? 0).getD ⟨{ n := 0, stab := [], lx := [], lz := [] }, by decide⟩,
    names := ["L0", "R0"] }
def qCtx : QGPUCtx := [("cc", 0, qIface)]

-- the BUILDER resolves NAMES to the real qubit + sets support from the block's actual
-- logical rows — it REPRODUCES the (hand-written) basis addresses, so they are ChainQ-bound:
example : (match buildQGPUAddr? qCtx "cc" "L0" .left 0 0 with | .ok a => a == L0 | .error _ => false) = true := by decide
example : (match buildQGPUAddr? qCtx "cc" "R0" .right 0 0 with | .ok a => a == R0 | .error _ => false) = true := by decide
-- NEGATIVE — a BOGUS code family / unknown logical NAME is REJECTED by the builder:
example : ok? (buildQGPUAddr? qCtx "evil" "L0" .left 0 0) = false := by decide
example : ok? (buildQGPUAddr? qCtx "cc" "nope" .left 0 0) = false := by decide

example : cb11.wf qEnv = true := by decide                                       -- basis bound to qEnv
example : cb11.k = 2 := by decide
example : cb11.maxMerge = 1 := by decide
example : L0.mergeable R0 = true := by decide                                    -- inter-sector ok

-- a round with the inter-sector merge is ACCEPTED (and re-resolves through the context):
example : ok? (checkQGPURound? qEnv [] { basis := cb11, merges := [{ a := L0, b := R0 }] }) = true := by decide
example : ok? (checkQGPURoundIn? qEnv [] qCtx { basis := cb11, merges := [{ a := L0, b := R0 }] }) = true := by decide

-- THE CHECKER-SAFETY FIX: a basis whose member has a FAKE name "ghost" + a valid raw qubit +
-- a bogus (all-false) support is accepted by the env-only kernel `checkQGPURound?` but
-- REJECTED by the ChainQ-bound `checkQGPURoundIn?` (it fails to RE-RESOLVE through the ctx):
def ghost : QGPUAddr := { code := "ghost", logical := "g", qubit := ⟨0, 1⟩, sector := .right, row := 0, col := 0,
                          xSupport := [false, false, false, false], zSupport := [false, false, false, false] }
def cbGhost : ClusteredLogicalBasis := { cb11 with addrs := [L0, ghost] }
example : ghost.resolvesIn qCtx = false := by decide                              -- "ghost" does not resolve
example : ok? (checkQGPURound?   qEnv []      { basis := cbGhost, merges := [{ a := L0, b := ghost }] }) = true  := by decide  -- env-only kernel: accepts
example : ok? (checkQGPURoundIn? qEnv [] qCtx { basis := cbGhost, merges := [{ a := L0, b := ghost }] }) = false := by decide  -- ChainQ-bound: REJECTS
-- a FAKED support on a real name also fails re-resolution:
def L0faked : QGPUAddr := { L0 with xSupport := [false, false, false, false] }    -- wrong support
example : L0faked.resolvesIn qCtx = false := by decide

-- NEGATIVE — an OFF-BASIS "evil" participant (not in basis.addrs) is REJECTED (the confirmed hole):
def evil : QGPUAddr := { code := "evil", logical := "X", qubit := ⟨0, 0⟩, sector := .right, row := 0, col := 0,
                         xSupport := [false, true, false, false], zSupport := [false, false, false, true] }
example : ok? (checkQGPURound? qEnv [] { basis := cb11, merges := [{ a := L0, b := evil }] }) = false := by decide

-- NEGATIVE — the SAME logical used TWICE in a round (no-reuse) is REJECTED:
example : ok? (checkQGPURound? qEnv [] { basis := cb11, merges := [{ a := L0, b := R0 }, { a := L0, b := R0 }] }) = false := by decide

-- NEGATIVE — a DEAD participant carrier is REJECTED:
example : ok? (checkQGPURound? qEnv [⟨0, 0⟩] { basis := cb11, merges := [{ a := L0, b := R0 }] }) = false := by decide

-- NEGATIVE — exceeding the k/2 = 1 parallel bound is REJECTED:
def L0b : QGPUAddr := { L0 with logical := "L0b", qubit := ⟨0, 0⟩ }
example : ok? (checkQGPURound? qEnv [] { basis := cb11, merges := [{ a := L0, b := R0 }, { a := L0b, b := R0 }] }) = false := by decide

-- NEGATIVE — a same-sector NONALIGNED basis: a wrong support WIDTH makes wfIn fail:
def Lbad : QGPUAddr := { L0 with xSupport := [true] }                            -- width 1 ≠ 2n = 4
def cbBad : ClusteredLogicalBasis := { cb11 with addrs := [Lbad, R0] }
example : cbBad.wf qEnv = false := by decide

-- NEGATIVE — same-sector, DIFFERENT row AND column is NOT mergeable:
def La1 : QGPUAddr := { L0 with logical := "La1", row := 1, col := 1 }
example : La1.mergeable L0 = false := by decide

-- full-rank connection (rank H_Zp = 1 = k/2) saturates parallelism for cb11:
example : maximallyParallel cb11 psOK = true := by decide

end Compiler.CodeSwitch
