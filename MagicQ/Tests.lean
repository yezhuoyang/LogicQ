/-
  MagicQ.Tests — cheap `decide` examples exercising the MagicQ checker on the
  library protocols.  These are the first regression tests that the checker
  genuinely REJECTS malformed cultivation/distillation programs at the logical/type
  level, and ACCEPTS well-formed ones with the expected output/obligation summary.

  Mathlib-free; every lemma is a small `by decide`.
-/
import MagicQ.Library.ReedMuller15
import MagicQ.Library.Cultivation

namespace MagicQ.Tests
open MagicQ TypeChecker

/-! ## §1. Standard 15-to-1 distillation (`rm15_to_1`). -/

/-- **RM15 resource arity (reject).**  Fewer than 15 inputs is rejected. -/
example : checks? ReedMuller15.rm15To1Underfull = false := by decide

/-- **RM15 resource arity (accept).**  Exactly 15 compatible `T` resources check,
    producing exactly ONE output and consuming all 15 inputs (+ the output). -/
example : checks? ReedMuller15.rm15To1 = true := by decide

/-- The accepted `rm15_to_1` produces exactly one output magic state. -/
example :
    ((checkProtocol ⟨[]⟩ ReedMuller15.rm15To1).toOption.map (·.outputs.length)) = some 1 := by decide

/-- … and that output is a `T`-type state. -/
example :
    ((checkProtocol ⟨[]⟩ ReedMuller15.rm15To1).toOption.map
      (fun cp => cp.outputs.all (fun s => s.basis.tType))) = some true := by decide

/-- … the 15 inputs are all consumed (16 consume-records: 15 inputs + the output). -/
example :
    ((checkProtocol ⟨[]⟩ ReedMuller15.rm15To1).toOption.map (·.consumed.length)) = some 16 := by decide

/-- … and nothing leaks (every resource is consumed exactly once). -/
example :
    ((checkProtocol ⟨[]⟩ ReedMuller15.rm15To1).toOption.map (·.leaked)) = some [] := by decide

/-- … the distillation threshold is recorded as a deferred obligation. -/
example :
    ((checkProtocol ⟨[]⟩ ReedMuller15.rm15To1).toOption.map
      (fun cp => cp.deferred.contains (.distillThreshold "ε < 0.141"))) = some true := by decide

/-- … the NON-Pauli Bravyi–Kitaev `A`-type syndrome (`η`) + decoding is recorded as a
    deferred obligation — the binary CSS surrogate does NOT prove it. -/
example :
    ((checkProtocol ⟨[]⟩ ReedMuller15.rm15To1).toOption.map
      (fun cp => cp.deferred.contains .bkATypeSyndrome)) = some true := by decide

/-- … and the 15 consumed input carriers are RETIRED — `finalCarriers` has NO live
    carrier (every input carrier + the output carrier is retired by op-end). -/
example :
    ((checkProtocol ⟨[]⟩ ReedMuller15.rm15To1).toOption.map
      (fun cp => (cp.finalCarriers.filter (fun p => p.2.live)).length)) = some 0 := by decide

/-! ## §1·5. 15-to-1 input basis: only standard `|A₀⟩ = T|+⟩` (`.T`/`.A0`). -/

/-- 15 inputs of a single `basis`, distilled to one `.T` output. -/
def distillWith (basis : MagicBasis) : Protocol :=
  { name := "distill_with"
    ops  := ((List.range 15).map
              (fun i => ProtocolOp.inject .supplied basis i (.external "noisy-T-input") i {})) ++
      [ .distill15To1 (List.range 15) 15 15 (.external "RM15") {} []
      , .output 15 ] }

/-- **Valid `.T` inputs are accepted.** -/
example : checks? (distillWith .T) = true := by decide
/-- **Valid `.A0` inputs are accepted** (`|A₀⟩ = T|+⟩`, the canonical BK input). -/
example : checks? (distillWith .A0) = true := by decide
/-- **`.Tdg` inputs are REJECTED** — the conjugate `T†` is not silently relabelled to `.T`. -/
example : checks? (distillWith .Tdg) = false := by decide
/-- **`.Y` inputs are REJECTED** (wrong magic family). -/
example : checks? (distillWith .Y) = false := by decide

/-! ## §2. Magic-state cultivation (`cultivate_T`). -/

/-- **Cultivation (accept).**  The default cultivation protocol checks. -/
example : checks? Cultivation.defaultT = true := by decide

/-- … producing exactly one output magic state. -/
example :
    ((checkProtocol ⟨[]⟩ Cultivation.defaultT).toOption.map (·.outputs.length)) = some 1 := by decide

/-- … and recording the deferred GROWTH fault-distance obligation (d1 = 5). -/
example :
    ((checkProtocol ⟨[]⟩ Cultivation.defaultT).toOption.map
      (fun cp => cp.deferred.contains (.growthFaultDistance 0 5))) = some true := by decide

/-- … and the deferred ESCAPE graft obligation (d2 = 15). -/
example :
    ((checkProtocol ⟨[]⟩ Cultivation.defaultT).toOption.map
      (fun cp => cp.deferred.contains (.escapeGraft 0 15))) = some true := by decide

/-- … and the external-carrier obligations for the un-materialised color codes. -/
example :
    ((checkProtocol ⟨[]⟩ Cultivation.defaultT).toOption.map
      (fun cp => cp.deferred.contains
        (.externalCarrier "ColorCode(3)" "injection carrier not materialised in ChainQ")))
      = some true := by decide

/-- **Cultivation (reject): premature output.**  Outputting BEFORE growth/escape
    establish the promised fault/code distances is rejected. -/
example : checks? (Cultivation.cultivateTPremature Cultivation.defaultSpec) = false := by decide

/-- **Cultivation uses the NON-Pauli H_XY (T-basis) double-check, not `.Z`**, via the
    DEFERRED-assumption path (`assumeLogicalCheck`) — the AST carries the `hxy` axis
    (faithful to 2409.17595), never a Pauli letter, and never the validated path. -/
example :
    Cultivation.defaultT.ops.any
      (fun op => match op with
        | .assumeLogicalCheck _ obs _ _ => decide (obs.axis = .hxy)
        | _ => false) = true := by decide

/-- … and the checker records the deferred-assumption check EXPLICITLY in
    `CheckedProtocol.deferred` with its FULL data (carrier, observable, detector,
    justification), not free-text only — ChainQ cannot yet prove the carrier admits a
    transversal H_XY, but the obligation is machine-readable. -/
example :
    ((checkProtocol ⟨[]⟩ Cultivation.defaultT).toOption.map
      (fun cp => cp.deferred.contains
        (.assumedLogicalCheck 0 { idx := 0, axis := .hxy } "cultivate.double-check"
          "transversal H_XY=(X+Y)/√2 double-check (GHZ-controlled), 2409.17595")))
      = some true := by decide

/-- … and a cultivation quality `deferred` claim is SURFACED into the checked summary
    (`MagicQuality.deferred` → `Obligation.qualityClaim`), not just left on the value. -/
example :
    ((checkProtocol ⟨[]⟩ Cultivation.defaultT).toOption.map
      (fun cp => cp.deferred.contains
        (.qualityClaim "fault distance d1 established by Bell-boundary growth"))) = some true := by decide

/-! ## §2·5. `r1`/`r2` are OPERATIONAL ops, not just `params` metadata. -/

/-- A spec with distinct idling rounds `r1=7`, `r2=9`. -/
def spec79 : Cultivation.CultivationSpec := { Cultivation.defaultSpec with r1 := 7, r2 := 9 }

/-- **`r1` drives the grafted-code idling `stabilize`** — `r1=7` ⇒ a
    `stabilizationRounds 0 7` obligation. -/
example :
    ((checkProtocol ⟨[]⟩ (Cultivation.cultivateT spec79)).toOption.map
      (fun cp => cp.deferred.contains (.stabilizationRounds 0 7))) = some true := by decide

/-- **`r2` drives the final-matchable idling `stabilize`** — `r2=9` ⇒ a
    `stabilizationRounds 0 9` obligation. -/
example :
    ((checkProtocol ⟨[]⟩ (Cultivation.cultivateT spec79)).toOption.map
      (fun cp => cp.deferred.contains (.stabilizationRounds 0 9))) = some true := by decide

/-- … and the default (`r1=r2=5`) does NOT record `r1=7` rounds — the parameter
    genuinely changes the op structure, it is not dead metadata. -/
example :
    ((checkProtocol ⟨[]⟩ Cultivation.defaultT).toOption.map
      (fun cp => cp.deferred.contains (.stabilizationRounds 0 7))) = some false := by decide

/-- … and the explicit escape TRANSITION into the final matchable code (distance d2=15)
    is recorded as its own obligation, distinct from the initial `escapeGraft`. -/
example :
    ((checkProtocol ⟨[]⟩ Cultivation.defaultT).toOption.map
      (fun cp => cp.deferred.contains (.escapeTransition 0 15))) = some true := by decide

/-! ## §3. Postselection scope. -/

/-- A standalone protocol postselecting on an UNKNOWN syndrome. -/
def badPostselect : Protocol :=
  { name := "bad_postselect"
    ops  := [ .postselect (.syndromeEq "no-such-syndrome" false) ] }

/-- **Postselection scope (reject).**  A postselection on an unproduced
    detector/syndrome is rejected. -/
example : checks? badPostselect = false := by decide

/-- A protocol whose postselection DOES refer to a produced syndrome checks. -/
def goodPostselect : Protocol :=
  { name := "good_postselect"
    ops  :=
      [ .inject .unitary .T 0 (.external "C") 0 {}
      , .checkLogical 0 { idx := 0, axis := .pauli .Z } "syn"
      , .postselect (.syndromeEq "syn" false)
      , .discard 0 ] }

example : checks? goodPostselect = true := by decide

/-- **External-carrier deferral is EXPLICIT, not silent.**  A protocol on an
    `external` carrier checks, but ONLY with the external carrier recorded as a
    deferred obligation in `CheckedProtocol.deferred`. -/
example :
    ((checkProtocol ⟨[]⟩ goodPostselect).toOption.map
      (fun cp => cp.deferred.contains
        (.externalCarrier "C" "injection carrier not materialised in ChainQ"))) = some true := by decide

/-! ## §4. Linearity and well-formedness corner cases. -/

/-- A logical check addressing a NON-exposed logical (idx ≥ k) is rejected. -/
def badObservable : Protocol :=
  { name := "bad_observable"
    ops  :=
      [ .inject .unitary .T 0 (.external "C") 0 {}
      , .checkLogical 0 { idx := 3, axis := .pauli .Z } "syn"   -- carrier exposes only idx 0
      , .discard 0 ] }

example : checks? badObservable = false := by decide

/-- DOUBLE-output of the same resource is rejected (linearity: consumed twice). -/
def doubleOutput : Protocol :=
  { name := "double_output"
    ops  :=
      [ .inject .unitary .T 0 (.external "C") 0 {}
      , .output 0
      , .output 0 ] }

example : checks? doubleOutput = false := by decide

/-- A duplicate carrier id is rejected. -/
def dupCarrier : Protocol :=
  { name := "dup_carrier"
    ops  :=
      [ .inject .unitary .T 0 (.external "C") 0 {}
      , .inject .unitary .T 0 (.external "C") 1 {}    -- carrier 0 reused
      , .discard 0 ] }

example : checks? dupCarrier = false := by decide

/-- A distillation output claiming a code distance that NO op establishes is
    REJECTED — the output codeDistance gate is a genuine cross-check, not the
    tautology `d ≤ d` (distillation never self-stamps its own claimed distance). -/
def distillInflatedDistance : Protocol :=
  { name := "distill_inflated_distance"
    ops  := ReedMuller15.inputInjections ++
      [ .distill15To1 (List.range 15) 15 15 (.external "RM15") { codeDistance := some 9999 } []
      , .output 15 ] }

example : checks? distillInflatedDistance = false := by decide

/-- **Linearity: leaks fail by default.**  Two states injected, only one output —
    the un-disposed state is a `resourceLeak` ERROR, so the protocol is REJECTED. -/
def leaky : Protocol :=
  { name := "leaky"
    ops  :=
      [ .inject .unitary .T 0 (.external "C") 0 {}
      , .inject .unitary .T 1 (.external "C2") 1 {}
      , .output 0 ] }                                   -- resource 1 never consumed

example : checks? leaky = false := by decide

/-- … disposing BOTH live states (output one, discard the other) checks. -/
def notLeaky : Protocol :=
  { leaky with name := "not_leaky", ops := leaky.ops ++ [ .discard 1 ] }

example : checks? notLeaky = true := by decide

/-! ## §4·4. Carrier lifecycle: output/discard RETIRES the carrier. -/

/-- **`inject; output; grow` is REJECTED** — once a state is returned, its carrier is
    no longer live, so the later `grow` fails (`carrierNotLive`). -/
def outputThenGrow : Protocol :=
  { name := "output_then_grow"
    ops  :=
      [ .inject .unitary .T 0 (.external "C") 0 {}
      , .output 0
      , .grow 0 (.external "D") 5 "g" ] }

example : checks? outputThenGrow = false := by decide

/-- **`inject; discard; checkLogical` is REJECTED** — `discard` also retires the carrier. -/
def discardThenCheck : Protocol :=
  { name := "discard_then_check"
    ops  :=
      [ .inject .unitary .T 0 (.external "C") 0 {}
      , .discard 0
      , .checkLogical 0 { idx := 0, axis := .pauli .Z } "c" ] }

example : checks? discardThenCheck = false := by decide

/-! ## §4·5. Ownership and aliasing: block-backed carriers must be live + owned. -/

/-- A minimal valid one-logical-qubit block (validity ignores ownership/liveness). -/
def bareQubit (o : Owned) : Block :=
  { n := 1, stab := [], lx := [[true, false]], lz := [[false, true]], own := o }

/-- Γ holding a single BORROWED block. -/
def borrowedEnv : TypedEnv := ⟨[⟨bareQubit .borrowed, by decide⟩]⟩
/-- Γ holding a single OWNED block. -/
def ownedEnv : TypedEnv := ⟨[⟨bareQubit .owned, by decide⟩]⟩

/-- Inject onto the (block 0) carrier, then dispose it. -/
def injectOntoBlock : Protocol :=
  { name := "inject_onto_block"
    ops  := [ .inject .unitary .T 0 (.block 0) 0 {}, .discard 0 ] }

/-- **Block-backed op on a BORROWED block is REJECTED** (reuses `TypeError.notOwned`). -/
example : checksIn? borrowedEnv injectOntoBlock = false := by decide

/-- … the SAME op on an OWNED block checks. -/
example : checksIn? ownedEnv injectOntoBlock = true := by decide

/-- **Block aliasing is REJECTED.**  Two LIVE MagicQ carriers must not reference the
    same underlying `.block id` (reuses `TypeError.clone`). -/
def aliasBlock : Protocol :=
  { name := "alias_block"
    ops  :=
      [ .inject .unitary .T 0 (.block 0) 0 {}
      , .inject .unitary .T 1 (.block 0) 1 {}    -- block 0 already held by a live carrier
      , .discard 0, .discard 1 ] }

example : checksIn? ownedEnv aliasBlock = false := by decide

/-- … but a block FREED by a prior `discard` may be re-claimed (liveness transfers). -/
def reuseBlock : Protocol :=
  { name := "reuse_block"
    ops  :=
      [ .inject .unitary .T 0 (.block 0) 0 {}
      , .discard 0                               -- retires carrier 0, freeing block 0
      , .inject .unitary .T 1 (.block 0) 1 {}
      , .discard 1 ] }

example : checksIn? ownedEnv reuseBlock = true := by decide

/-- **`grow` into a `.block` TARGET is REJECTED** — the v1 AST carries no switch
    certificate, so a real block-backed switch cannot be validated; a `.block` target
    must not be silently treated as a code template / aliased in. -/
def growIntoBlock : Protocol :=
  { name := "grow_into_block"
    ops  := [ .inject .unitary .T 0 (.external "C") 0 {}, .grow 0 (.block 0) 5 "g", .discard 0 ] }

/-- grow into a BORROWED `.block` → rejected. -/
example : checksIn? borrowedEnv growIntoBlock = false := by decide
/-- grow into an OWNED `.block` → still rejected (no `SwitchCert` path implemented). -/
example : checksIn? ownedEnv growIntoBlock = false := by decide

/-- **`graft` into a `.block` TARGET is REJECTED** too (borrowed shown). -/
def graftIntoBlock : Protocol :=
  { name := "graft_into_block"
    ops  := [ .inject .unitary .T 0 (.external "C") 0 {}, .graft 0 (.block 0) 5 "g", .discard 0 ] }

example : checksIn? borrowedEnv graftIntoBlock = false := by decide

/-- **A live carrier on `.block 0`, then ANOTHER carrier `grow`s into `.block 0`, is
    REJECTED** — no silent `.block` target aliasing. -/
def growAliasLiveBlock : Protocol :=
  { name := "grow_alias_live_block"
    ops  :=
      [ .inject .unitary .T 0 (.block 0) 0 {}        -- carrier 0 lives on (owned) block 0
      , .inject .unitary .T 1 (.external "C") 1 {}
      , .grow 1 (.block 0) 5 "g"                      -- carrier 1 grows INTO block 0 → rejected
      , .discard 0, .discard 1 ] }

example : checksIn? ownedEnv growAliasLiveBlock = false := by decide

/-! ## §4·6. Non-Pauli `hxy` requires the explicit deferred-assumption path. -/

/-- **`.hxy` via the validated `checkLogical` path on a bare block is REJECTED** — the
    type system cannot prove a transversal H_XY; it must use `assumeLogicalCheck`. -/
def hxyOnBareBlock : Protocol :=
  { name := "hxy_on_bare_block"
    ops  :=
      [ .inject .unitary .T 0 (.block 0) 0 {}
      , .checkLogical 0 { idx := 0, axis := .hxy } "c"
      , .discard 0 ] }

example : checksIn? ownedEnv hxyOnBareBlock = false := by decide

/-- … while the SAME `.hxy` check via `assumeLogicalCheck` is ACCEPTED and recorded as
    an explicit deferred obligation in `CheckedProtocol.deferred`. -/
def hxyViaAssume : Protocol :=
  { name := "hxy_via_assume"
    ops  :=
      [ .inject .unitary .T 0 (.external "C") 0 {}
      , .assumeLogicalCheck 0 { idx := 0, axis := .hxy } "c" "assumed H_XY"
      , .discard 0 ] }

example : checks? hxyViaAssume = true := by decide

/-- … recording the obligation with FULL data: carrier `0`, observable `{idx 0, hxy}`,
    detector `"c"`, and justification — not free-text only. -/
example :
    ((checkProtocol ⟨[]⟩ hxyViaAssume).toOption.map
      (fun cp => cp.deferred.contains
        (.assumedLogicalCheck 0 { idx := 0, axis := .hxy } "c" "assumed H_XY"))) = some true := by decide

/-! ## §5. Obligation discharge (pairing MagicQ outputs with compiler obligations). -/

/-- A produced `T` output DISCHARGES a mixed-IR `tGate` obligation — so either
    `cultivate_T` or `rm15_to_1` can supply a logical `T`-gate's magic state. -/
example :
    dischargesObligation { basis := .T, carrier := 0 } { kind := .tGate, target := ⟨0, 0⟩ } = true := by decide

example :
    dischargesObligation { basis := .A0, carrier := 0 } { kind := .tGate, target := ⟨0, 0⟩ } = true := by decide

/-- A non-`T`-type (`Y`) state does NOT discharge a `tGate` obligation. -/
example :
    dischargesObligation { basis := .Y, carrier := 0 } { kind := .tGate, target := ⟨0, 0⟩ } = false := by decide

end MagicQ.Tests
