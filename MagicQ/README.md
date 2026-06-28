# MagicQ

> A source language and high-level checker for magic-state protocols (cultivation + 15-to-1 distillation).

MagicQ is a real abstract syntax (data, not Lean-embedded notation) for magic-state protocols: producing, improving, and consuming magic states while their QEC *carrier* changes over time. It sits BESIDE the logical compiler in the LogicQ stack — algorithm compilation emits typed `Compiler.MagicObligation`s, and MagicQ describes the factory/cultivation protocols that (eventually) discharge them. This pass is high-level CHECKING only: carrier liveness/ownership, linearity, arity, and postselection scope are validated, while stochastic fault tolerance and decoder performance are tracked as honest DEFERRED obligations, never proven. Carriers reuse `TypeChecker.Block`/`BlockId`, logical Pauli checks reuse `PPM.PLetter`, and pending resources reuse `Compiler.MagicObligation` (REUSE over reinvention).

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Public umbrella (`import MagicQ.Basic`); aggregates Syntax, Check, and the two `Library/` protocols. |
| [Syntax.lean](Syntax.lean) | The protocol AST: `MagicBasis`, `MagicQuality`, `Carrier`/`CarrierRef`, linear `MagicState`/`MagicEnv`, `PostselectCond`/`PostPred`, `ProtocolOp`, `Protocol`. |
| [Check.lean](Check.lean) | The high-level checker (`Γ ; Σ ; CheckState`): `MagicError`, `Obligation`, `checkOp`, `checkProtocol`, the real block-switch path. |
| [Tests.lean](Tests.lean) | `by decide` regressions (NOT imported by the umbrella; `lake build MagicQ.Tests`) — accepts well-formed protocols, REJECTS malformed ones. |

The `Library/` subdirectory holds the worked protocols ([Library/ReedMuller15.lean](Library/ReedMuller15.lean) — the Bravyi–Kitaev `[[15,1,3]]` code + `rm15_to_1`; [Library/Cultivation.lean](Library/Cultivation.lean) — the Gidney–Shutty–Jones `cultivate_T`) and has no README of its own.

## Key definitions

```lean
inductive ProtocolOp
  | inject (style : InjectStyle) (basis : MagicBasis)
           (carrier : CarrierId) (code : CarrierRef)
           (resource : ResourceId) (quality : MagicQuality := {})
  | checkLogical (carrier : CarrierId) (obs : LogicalObs) (detector : String)
  | assumeLogicalCheck (carrier : CarrierId) (obs : LogicalObs) (detector justification : String)
  | grow (carrier : CarrierId) (to : CarrierRef) (faultDistance : Nat) (detector : String)
  | graft (carrier : CarrierId) (into : CarrierRef) (codeDistance : Nat) (detector : String)
  | distill15To1 (inputs : List ResourceId)
                 (output : ResourceId) (outCarrier : CarrierId) (outCode : CarrierRef)
                 (quality : MagicQuality := {}) (syndromes : List String := [])
  | output (resource : ResourceId)
```
(elided; see [Syntax.lean](Syntax.lean) for the full constructor list)

```lean
-- MagicQ/Check.lean
def checkOp (Γ : TypedEnv) (menv : MagicEnv) (st : CheckState) :
    ProtocolOp → Except MagicError (MagicEnv × CheckState)
```

```lean
-- MagicQ/Check.lean
def checkProtocol (Γ0 : TypedEnv) (p : Protocol) : Except MagicError CheckedProtocol
```

```lean
-- MagicQ/Check.lean — the honest deferred-obligation vocabulary
inductive Obligation
  | externalCarrier     (name : String) (reason : String)
  | growthFaultDistance (carrier : CarrierId) (claim : Nat)
  | escapeGraft         (carrier : CarrierId) (codeDistance : Nat)
  | distillThreshold    (claim : String)
  | bkATypeSyndrome
  | assumedLogicalCheck (carrier : CarrierId) (obs : LogicalObs) (detector justification : String)
  -- … (full list in Check.lean)
```

## Example

```lean
/-- RM15 resource arity (accept).  Exactly 15 compatible `T` resources check,
    producing exactly ONE output and consuming all 15 inputs (+ the output). -/
example : checks? ReedMuller15.rm15To1 = true := by decide

/-- … the NON-Pauli Bravyi–Kitaev `A`-type syndrome (`η`) + decoding is recorded as a
    deferred obligation — the binary CSS surrogate does NOT prove it. -/
example :
    ((checkProtocol ⟨[]⟩ ReedMuller15.rm15To1).toOption.map
      (fun cp => cp.deferred.contains .bkATypeSyndrome)) = some true := by decide
```

The checker ACCEPTS the standard 15-to-1 distillation, yet the non-Pauli `A`-type syndrome and decoding stay an explicit deferred obligation rather than being claimed as proven. Source: [Tests.lean](Tests.lean) (§1).

## Status & scope

What is CHECKED at the highest logical/type level: carrier existence + liveness; OWNERSHIP of `.block` carriers (a borrowed block cannot be injected onto / grown / grafted — reusing `TypeError.notOwned`); carrier lifecycle (`output`/`discard` retire the carrier; a distillation retires its 15 consumed input carriers); NO block aliasing (two live carriers may not reference the same real `.block id`, reusing `TypeError.clone`); exact 15-input arity restricted to the `|A₀⟩ = T|+⟩` family (`.T`/`.A0` only — `.Tdg`/`.Y` rejected, no silent relabel); postselection SCOPE; and EXACTLY-ONCE linear consumption (leaks fail by default). Output is gated on declared fault/code-distance promises being established by prior `grow`/`graft` ops. There is now a REAL ChainQ-backed block switch (`checkBlockSwitch`/`switchBlock`) that reuses `TypeChecker.checkSwitchWithDistance` — no duplicate algebra, no fake acceptance.

What is DEFERRED (recorded in `CheckedProtocol.deferred`, never silently discharged — `A` in the Compiler/CONTRACT.md tiering): stochastic fault tolerance, decoder performance / escape gap, the distillation threshold and cubic output-error, injection-correctness, assumed logical checks (`assumedLogicalCheck`, including the non-Pauli `H_XY` T-basis cultivation check of 2409.17595), the Bravyi–Kitaev non-Pauli `A`-type syndrome `η` + decoding (`bkATypeSyndrome` — `rm15Code : CSSCode` is only the binary CSS surrogate proving `𝓛₁ ⊆ 𝓛₂^⊥`/`k=1`, NOT the `A`-checks/threshold/15-to-1 correctness), the escape graft + transition, surfaced `MagicQuality.deferred` quality claims, and every `external` carrier. A `.block` grow/graft target is *rejected* (not deferred) for lack of a `SwitchCert`. The accepted/rejected behaviors are `by decide` tests (`D`); the Tests module is not imported by the umbrella. NO parser, no custom notation, no Stim/circuit lowering, and no gate-teleportation discharge of `Compiler.MagicObligation` yet (`dischargesObligation` only records that a `T`-type output *can* pair with a `tGate` obligation). The 15-to-1 raw inputs remain a `.supplied`-style fixture (a first-class protocol-input surface is future work — see the TODO in [Library/ReedMuller15.lean](Library/ReedMuller15.lean)).

## See also

- [../README.md](../README.md) — the LogicQ repository root.
- [Compiler/CONTRACT.md](../Compiler/CONTRACT.md) — the P/D/A/M obligation tiering this README mirrors.
- [DESIGN_PLAN.md](DESIGN_PLAN.md) — the first-pass design grounded in cultivation + 15-to-1.
- [IMPLEMENTATION_PROMPT.md](IMPLEMENTATION_PROMPT.md) — the handoff prompt for the first implementation agent.
