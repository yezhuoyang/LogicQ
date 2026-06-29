# Compiler/PPR2PPM

> Proof-carrying evidence for a single type-checked PPM fragment (a placeholder home for a future PPR-to-PPM lowering pass).

This folder sits late in the LogicQ stack, on the path from the Mixed IR toward the PPM measurement sublanguage. Despite the `PPR2PPM` name, there is currently **no** Pauli-product-rotation lowering pass here. After the M9 design shift the standalone PPM-only compiler was superseded by `Compiler.Mixed` (where PPM is one checked target among transversal gates, automorphisms, and code switches), so what remains is the proof-carrying evidence that a single `PPM.Stmt` fragment passes the TypeChecker's `checkPPMProgram`.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | `CompiledPPM` evidence wrapper, the `mkCompiledPPM?` validator, three soundness `theorem`s, and two `by decide` tests. |

## Key definitions

```lean
/-- A PPM program FRAGMENT carrying the proof that it type-checks. -/
structure CompiledPPM (Γ : TypedEnv) (caps : List Capability) where
  stmt  : PPM.Stmt
  typed : ok? (checkPPMProgram Γ caps stmt) = true
```

```lean
/-- Validate a raw PPM fragment into proof-carrying evidence. -/
def mkCompiledPPM? (Γ : TypedEnv) (caps : List Capability) (s : PPM.Stmt) :
    Except TypeError (CompiledPPM Γ caps) :=
  if h : ok? (checkPPMProgram Γ caps s) = true then .ok ⟨s, h⟩
  else .error (.other "PPM fragment does not type-check under the environment")
```

```lean
/-- Every measurement emitted by a compiled fragment is LEGAL under the
    TypeChecker (via the structural `checkPPMStmt_meas_sound`). -/
theorem CompiledPPM.meas_legal {Γ : TypedEnv} {caps : List Capability}
    (c : CompiledPPM Γ caps) :
    (measTargets c.stmt).all (fun P => ok? (checkPPM Γ caps P)) = true
```

```lean
/-- Every `frame`/`discard` of a compiled fragment targets a valid logical qubit. -/
theorem CompiledPPM.targets_valid {Γ : TypedEnv} {caps : List Capability}
    (c : CompiledPPM Γ caps) :
    (frameDiscardTargets c.stmt).all (validLQubit Γ) = true
```

(There is also `CompiledPPM.wellFormed`, which simply re-exposes the `typed` proof field.)

## Example

The fragments are `PPM.Stmt` values checked under `tenvQ` (a `TypedEnv` holding the
single bare logical qubit `q0`, [TypeChecker/Judgment/PPM/Examples.lean:17](../../TypeChecker/Judgment/PPM/Examples.lean#L17),26)
with no capabilities.

In PPM surface syntax (parses today — [PPM/Parse.lean](../../PPM/Parse.lean), by `decide`),
the accepting fragment is a native single-qubit measurement binding the outcome `c0` to the
logical Pauli `Z` on logical qubit `q[0]`:

```text
c0 := M q[0]↦Z
```

The empty measurement (no Pauli factors) has no surface form — the parser requires at least
one `LQubit ↦ PLetter` factor — so it is exhibited only as the rejecting machine-form AST below.

As the underlying `PPM.Stmt` machine-form AST (the values fed to `mkCompiledPPM?` in
[Basic.lean](Basic.lean)):

```lean
-- the native single-qubit measurement fragment — binds outcome c0 to M_Z on logical qubit ⟨0,0⟩ (= q[0]):
.meas 0 [(⟨0, 0⟩, PPM.PLetter.Z)]   -- OK: validates into proof-carrying evidence
-- the empty measurement fragment (no Pauli factors):
.meas 0 []                          -- rejected: non-native / empty measurement list
```

`tenvQ` is the typed environment that contains exactly the bare qubit `q0`
([TypeChecker/Judgment/PPM/Examples.lean:17](../../TypeChecker/Judgment/PPM/Examples.lean#L17)):

```lean
def q0 : Block := { n := 1, stab := [], lx := [[true, false]], lz := [[false, true]] }
def tenvQ : TypedEnv := ⟨[⟨q0, by decide⟩]⟩
```

The single-qubit `Z` measurement on logical qubit `⟨0,0⟩` validates into proof-carrying
evidence under `tenvQ`; the empty measurement list is rejected.

Source: [Basic.lean](Basic.lean) (lines 55-58).

## Status & scope

Honest scope, mirroring [Compiler/CONTRACT.md](../CONTRACT.md):

- **Proved (P):** the three `theorem`s — `CompiledPPM.wellFormed`, `CompiledPPM.meas_legal`, and `CompiledPPM.targets_valid` — are universally-quantified soundness statements over any compiled fragment. They establish well-formedness, measurement legality (via `checkPPMStmt_meas_sound`), and target validity (via `checkPPMStmt_targets_valid`) at the **type-checking** level only.
- **Decided (D):** the two PPM fragments above — the single-qubit `Z` measurement accepts, the empty measurement list rejects (decided by `by decide` smoke tests in [Basic.lean](Basic.lean)).
- **Planned / stub (M):** the actual PPR-to-PPM lowering pass. There is **no** code here that lowers Pauli-product rotations to adaptive PPM, and **no** denotational/operational-equivalence theorem of the intended shape `denote(PPR program) = semantics(lowered PPM program)`. Magic-resource tracking for such a pass is likewise not present. For reference, both endpoints of the intended bridge already have real text parsers: the PPR source side parses today ([PPR/Parse.lean](../../PPR/Parse.lean), by `decide`), e.g. a `T` rotation `+π/8 · q[0]↦Z`, an `S` rotation `+π/4 · q[0]↦Z`, and a two-body `ZZ` rotation `+π/8 · q[0]↦Z q[1]↦Z`; the PPM target side parses today ([PPM/Parse.lean](../../PPM/Parse.lean), by `decide`), e.g. `c0 := M q[0]↦Z` and the joint measurement `c0 := M q[0]↦Z, a[0]↦X`.

Nothing here makes a channel-correctness, fault-tolerance, distance, or decoder claim; the guarantees are confined to TypeChecker legality of a measurement fragment.

## See also

- [../README.md](../README.md) — the Compiler layer overview.
- [../CONTRACT.md](../CONTRACT.md) — the correctness-boundary matrix (P / D / A / M tiers).

(This folder has no child directories.)
