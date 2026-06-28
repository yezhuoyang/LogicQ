/-
  MagicQ.Library.Cultivation — the magic-state CULTIVATION protocol AST.

  Grounded in 2409.17595 (Gidney–Shutty–Jones, "Magic state cultivation: growing
  T states as cheap as CNOT gates").  Cultivation is a LIVE-CARRIER protocol — the
  QEC carrier changes over time — split into three stages:

    * INJECTION   — prepare an encoded `|T⟩` in a distance-3 color code (the
      unitary-injection path is the source-code default).
    * CULTIVATION — a check-grow-stabilize cycle: a double-check of the logical
      value, Bell-boundary growth `ColorCode(3) → ColorCode(d1)`, and superdense
      color-code stabilization rounds.  Early stages use FULL postselection.
    * ESCAPE      — graft the cultivated state into a larger matchable code of
      distance `d2`, run rounds, postselect selected color-region detectors, and
      KEEP/REJECT on a decoder GAP (a deferred decoder obligation).

  Paper parameter conventions: `d1` end-of-cultivation fault distance, `d2` final
  code distance after escape, `r1` grafted-code rounds, `r2` final matchable-code
  rounds.

  HONEST SCOPE (this pass): the color code and grafted matchable code are NAMED
  EXTERNAL carriers — ChainQ has only a `ColorCode` README, so the checker records
  them as external obligations rather than pretending the ChainQ color-code facts
  are proved.  The growth fault-distance, stabilization, and escape decoder-gap are
  all DEFERRED obligations, never discharged here.

  Mathlib-free.
-/
import MagicQ.Check

namespace MagicQ.Cultivation

/-! ## §1. The cultivation specification. -/

/-- Parameters of a cultivation run (paper conventions, 2409.17595). -/
structure CultivationSpec where
  d1               : Nat         := 5         -- end-of-cultivation fault distance
  d2               : Nat         := 15        -- final code distance after escape
  r1               : Nat         := 5         -- grafted-code rounds   (paper d1=5 construction)
  r2               : Nat         := 5         -- final matchable-code rounds (paper d1=5 construction)
  superdenseCycles : Nat         := 3         -- superdense color-code stabilization cycles
  injectStyle      : InjectStyle := .unitary  -- unitary injection (source-code default)
  baseColorCode    : String      := "ColorCode(3)"  -- the injection carrier
  deriving Repr, Inhabited

/-- The default cultivation spec (d1=5, d2=15, unitary injection). -/
def defaultSpec : CultivationSpec := {}

/-- The grown color code name `ColorCode(d1)`. -/
def grownCodeName (s : CultivationSpec) : String := s!"ColorCode(d1={s.d1})"
/-- The INTERMEDIATE grafted code name `Grafted(d2)` (color↔matchable, where the `r1`
    rounds run). -/
def graftedCodeName (s : CultivationSpec) : String := s!"Grafted(d2={s.d2})"
/-- The FINAL matchable code name `Matchable(d2)` (where the `r2` rounds run). -/
def matchableName (s : CultivationSpec) : String := s!"Matchable(d2={s.d2})"

/-- The PROMISED quality of the cultivated output `T`: fault distance `≥ d1`
    (established by growth), final code distance `d2` (established by escape).  This
    is the claim CHECKED at `output` against what the ops actually establish. -/
def cultivatedTQuality (s : CultivationSpec) : MagicQuality :=
  { rawError      := some "ε_inject"
    faultDistance := some s.d1
    codeDistance  := some s.d2
    deferred      := ["unitary injection prepares encoded |T⟩ in distance-3 color code",
                      "fault distance d1 established by Bell-boundary growth",
                      "final code distance d2 established by escape graft",
                      "escape kept iff decoder gap ≥ threshold"] }

/-! ## §2. The `cultivate_T` protocol AST. -/

/-- **The magic-state cultivation protocol** for one `T` state.  Threads a SINGLE
    live carrier (`carrier 0`) holding one magic resource (`resource 0`) through
    inject → check → grow → stabilize → escape → postselect → output.  Returns one
    `MagicState T` on the grafted matchable carrier, recording the growth /
    stabilization / escape-decoder obligations as DEFERRED. -/
def cultivateT (s : CultivationSpec) : Protocol :=
  { name   := "cultivate_T"
    params := { d1 := some s.d1, d2 := some s.d2, r1 := some s.r1, r2 := some s.r2
                injectStyle := s.injectStyle
                notes := ["Gidney–Shutty–Jones cultivation, 2409.17595",
                          "live-carrier: inject → check → grow → stabilize → graft → idle r1 → transition → idle r2 → output"] }
    ops    :=
      [ -- INJECTION: encoded |T⟩ in a distance-3 color code (unitary injection).
        .inject s.injectStyle .T 0 (.external s.baseColorCode) 0 (cultivatedTQuality s)
        -- CULTIVATION: the logical "double-check" of the T state.  This is the
        -- NON-Pauli H_XY = (X+Y)/√2 check (|T⟩ is its +1 eigenstate), measured by the
        -- GHZ-controlled transversal-H_XY gadget (2409.17595) — NOT a Pauli `.Z`.  ChainQ
        -- cannot yet PROVE the color code admits a transversal H_XY, so it takes the
        -- DEFERRED-assumption path (`assumeLogicalCheck`), recording the obligation
        -- explicitly.  Then EARLY FULL postselection (any detector event discards — a
        -- small-circuit early-stage behaviour), then grow and stabilize.
      , .assumeLogicalCheck 0 { idx := 0, axis := .hxy } "cultivate.double-check"
          "transversal H_XY=(X+Y)/√2 double-check (GHZ-controlled), 2409.17595"
      , .postselect .fullDetectors
      , .grow 0 (.external (grownCodeName s)) s.d1 "cultivate.grow.bell-boundary"
      , .stabilize 0 s.superdenseCycles "cultivate.stabilize.superdense"
        -- ESCAPE.  (1) GRAFT into the intermediate grafted code of distance d2.
      , .graft 0 (.external (graftedCodeName s)) s.d2 "cultivate.escape.graft"
        -- (2) idle in the GRAFTED code for `r1` rounds (paper: grafted-code rounds).
      , .stabilize 0 s.r1 "cultivate.escape.idle-grafted-r1"
        -- (3) the TRANSITION into the final matchable code of distance d2.
      , .transitionToMatchable 0 (.external (matchableName s)) s.d2 "cultivate.escape.transition"
        -- (4) idle in the FINAL matchable code for `r2` rounds (paper: matchable rounds).
      , .stabilize 0 s.r2 "cultivate.escape.idle-matchable-r2"
        -- The escape circuit is too large to fully postselect, so it uses only the
        -- SELECTED detectors and a decoder-GAP predicate (a deferred obligation).
      , .postselect (.taggedDetectors "cultivate.escape.transition")
      , .postselect (.decoderGap s!"gap ≥ Δ (escape decoder, d2={s.d2})")
        -- OUTPUT: the cultivated T on the matchable carrier (faultDistance ≥ d1).
      , .output 0 ]
    spec   := [s!"fault distance ≥ {s.d1} after cultivation",
               s!"final code distance {s.d2} after escape",
               "escape kept iff decoder gap ≥ threshold (deferred)"] }

/-- `MagicQ.Cultivation.defaultT` — the standard cultivation protocol (default
    spec), returning one `MagicState T`. -/
def defaultT : Protocol := cultivateT defaultSpec

/-! ## §3. A malformed variant (output BEFORE the growth/escape obligations). -/

/-- A BROKEN cultivation: injects then immediately outputs, BEFORE growth/escape
    establish the promised fault/code distances.  Must be REJECTED by the checker
    (`outputWithoutQuality "faultDistance"`). -/
def cultivateTPremature (s : CultivationSpec) : Protocol :=
  { name := "cultivate_T_premature"
    params := { injectStyle := s.injectStyle }
    ops :=
      [ .inject s.injectStyle .T 0 (.external s.baseColorCode) 0 (cultivatedTQuality s)
      , .output 0 ] }

end MagicQ.Cultivation
