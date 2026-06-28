# TypeChecker/Judgment/Switch

> Typed code-switching judgment: legality-check a transparent coercion from one ChainQ code block to another.

This folder is the `Switch` judgment of the LogicQ TypeChecker. It sits between the ChainQ code-family front-end (which produces `Block`s carrying stabilizer / logical-operator data) and the Compiler Mixed IR: given a typed environment and a target code, `checkSwitch` decides whether a switch certificate `f` is an algebraically faithful cross-code symplectic map, consumes the source block, and emits typed evidence plus the deferred fault-tolerance obligations for the chosen physical protocol. It never asserts the protocol is fault-tolerant — only that the coercion preserves the stabilizer group and the logical X̄/Z̄ bases modulo target stabilizers.

## What's here

| Module | Role |
|--------|------|
| [Cert.lean](Cert.lean) | `SwitchKind`, the `SwitchCert` (kind + symplectic map `f`), and the `TypedSwitch` evidence record |
| [Check.lean](Check.lean) | `checkSwitch` and its distance-strengthened / raw-env entry points, plus the `CheckedSwitchCert` shape-proven certificate |
| [Examples.lean](Examples.lean) | Worked example: encode a bare qubit into the `[[3,1,1]]` repetition code, with `by decide` legality and rejection tests |

## Key definitions

```lean
inductive SwitchKind
  | gaugeFix          -- gauging logical operators / subsystem gauge fixing (2410.02213)
  | transversalCNOT   -- one-way transversal CNOT switching (2409.13465)
  | dimensionJump     -- transversal dimension jump for product codes (2510.07269)
  | teleport          -- gate-teleportation bridge
  deriving DecidableEq, Repr
```

```lean
structure SwitchCert where
  kind : SwitchKind
  f    : BoolMat
  deriving Repr
```

```lean
def checkSwitch (Γ : TypedEnv) (b : BlockId) (D : TypedBlock) (cert : SwitchCert) :
    Except TypeError (TypedEnv × TypedSwitch)
```

```lean
def checkSwitchWithDistance
    (Γ : TypedEnv) (b : BlockId) (D : TypedBlock) (cert : SwitchCert)
    (requiredDistance : Nat) :
    Except TypeError (TypedEnv × TypedSwitch × TypedDistanceEvidence)
```

```lean
structure CheckedSwitchCert (nC nD : Nat) where
  cert    : SwitchCert
  shapeWf : (decide (cert.f.length = 2 * nC) && cert.f.all (fun r => decide (r.length = 2 * nD))) = true
```

The checker requires: the source block exists, is `live`, and is `Owned.owned` (a borrowed block cannot be switched); `f` has shape `2·n_C × 2·n_D`; the X/Z logical arities of source and target agree; the mapped source stabilizers `f(S_C)` land in `inSpan` of `S_D`; and `f(X̄_C)`, `f(Z̄_C)` equal `X̄_D`, `Z̄_D` modulo the target stabilizer span (`rowsEqualModSpan`). On success it sets the source slot to the target block made live and inheriting the source ownership.

## Example

```lean
def encF : BoolMat := [[true, true, true, false, false, false],
                       [false, false, false, true, false, false]]

-- The encode-into-repetition switch is legal:
example : ok? (checkSwitch tsrc 0 tdst { kind := .gaugeFix, f := encF }) = true := by decide
-- …and it preserves the logical operators (induced X̄ = XXX, Z̄ = Z₀):
example : (res? (checkSwitch tsrc 0 tdst { kind := .gaugeFix, f := encF })).map (·.2.inducedLX)
            = some [[true, true, true, false, false, false]] := by decide

-- a degenerate map (everything ↦ 0) does not preserve the logical operators;
example : ok? (checkSwitch tsrc 0 tdst { kind := .gaugeFix, f := zeroMat 2 6 }) = false := by decide
```

The map `f` encodes the bare logical qubit into the `[[3,1,1]]` bit-flip repetition code, sending `X̄ ↦ XXX` and `Z̄ ↦ Z₀`; the legality and logical-preservation are settled by `decide`, and a degenerate all-zero map is rejected. Source: [Examples.lean](Examples.lean).

## Status & scope

- **D (`by decide` tests):** The algebraic legality of the switch — stabilizer-span preservation, logical-basis preservation, certificate shape `2·n_C × 2·n_D`, ownership/liveness gating, and the typed-target safety (a malformed target is unrepresentable as a `TypedBlock` and reported as `malformedTarget`, never as a source id) — is exercised by the `by decide` examples in [Examples.lean](Examples.lean) and [Check.lean](Check.lean).
- **A (documented assumption / deferred):** The four `SwitchKind`s name physical protocols (gauge-fixing 2410.02213, transversal-CNOT 2409.13465, dimension-jump 2510.07269, teleportation). The checker emits, but does NOT discharge, their fault-tolerance prerequisites via `switchObligations` — e.g. code distance `d_D`, single-shot / small-set-flip decoder thresholds, fault distance `R ≥ d`, postselection acceptance, Künneth merged-code distance, and Bell-pair fidelity. These remain external obligations.
- `checkSwitchWithDistance` additionally requires a certified post-switch distance lower bound `≥ requiredDistance` (`checkBlockDistance`), but the distance evidence it consumes is itself the responsibility of [ChainQ/Core/Distance](../../../ChainQ/Core/Distance.lean); no channel-correctness or operational-equivalence claim is made here.
- No `Step`/operational semantics or decoder soundness is proved in this folder.

## See also

- [../README.md](../README.md) — the `TypeChecker/Judgment` layer (PPM, PPMProgram, Switch, Transversal judgments)
- [../../README.md](../../README.md) — the `TypeChecker` root
- [Compiler/CONTRACT.md](../../../Compiler/CONTRACT.md) — the P / D / A / M proof-tier contract referenced above
