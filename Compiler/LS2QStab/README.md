# Compiler/LS2QStab

> Compatibility shim: re-exports the migrated PPM→QStab surgery certificate into the `Compiler` namespace, plus a tiny native one-measurement fixture.

This is the legacy `LS2QStab` edge in the LogicQ stack — the place where a single logical
PPM/surgery measurement is lowered to a [QStab](../../QStab/README.md) `Prog` and recorded
in a `SurgeryCert`. The surgery-certificate + fault-obligation types were MIGRATED to the
lattice-surgery IR layer ([`Compiler/LS/Cert.lean`](../LS/Cert.lean), namespace
`Compiler.LS`), which now OWNS them; this folder's [`Basic.lean`](Basic.lean) is a thin shim
that re-exports them so existing `Compiler.SurgeryCert` / `Compiler.FaultObligations` /
`Compiler.ppmMeasToQStab` users keep resolving unchanged. It sits between the Mixed/PPM IR
and the QStab physical-target dataflow (Stage 5/6 in [CONTRACT.md](../CONTRACT.md)).

## What's here

| Module | Role |
|---|---|
| [Basic.lean](Basic.lean) | COMPATIBILITY SHIM — re-exports `FaultStatus`/`FaultObligations`/`SurgeryCert`/`ppmMeasToQStab`/`ppmMeasToQStab_readout` from `Compiler.LS` into `Compiler`, and keeps the native `ZZ`-parity fixture (`progZZ`/`certZZ`) with its checked examples. |

There are no child directories. The actual definitions live in
[`../LS/Cert.lean`](../LS/Cert.lean); see the [Compiler.LS](../LS/README.md) layer for the
full lattice-surgery IR.

## Key definitions

The re-exported definitions (declared in [`../LS/Cert.lean`](../LS/Cert.lean)):

```lean
inductive FaultStatus
  | certified | deferred
  deriving DecidableEq, Repr
```

```lean
structure FaultObligations where
  distance      : FaultStatus := .deferred
  faultDistance : FaultStatus := .deferred
  decoder       : FaultStatus := .deferred
  deriving Repr, DecidableEq
```

```lean
def SurgeryCert.check (c : SurgeryCert) : Bool :=
  ! c.measuredParity.isEmpty
  && ! c.preservedLogicals.isEmpty
  && c.faults.allDeferred
```

```lean
def ppmMeasToQStab (sched : Option QStab.Sched) (P : QStab.PauliString) : QStab.Prog :=
  [ .prop sched P, .parity [0] ]
```

The native fixture in this folder ([`Basic.lean`](Basic.lean)):

```lean
def progZZ : QStab.Prog := LS.ppmMeasToQStab (some ⟨0, 0⟩) (Physical.ofString "ZZ")
```

## Example

```lean
-- The certificate's COMPUTABLE checks pass (parity nonempty, a preserved logical, all deferred).
example : certZZ.check = true := by decide
-- DETECTOR DETERMINISM of the lowered program is genuinely checkable (noiseless ⇒ fixed readout).
example : LS.SurgeryCert.detectorsDeterministic? progZZ LS.ppmMeasToQStab_readout = true := by decide
-- The fault obligations are explicitly DEFERRED (none certified) — honest by construction.
example : certZZ.faults.allDeferred = true := by decide
-- A cert that (dishonestly) marked its distance CERTIFIED would FAIL `check`:
example : LS.SurgeryCert.check { certZZ with faults := { distance := .certified } } = false := by decide
```

These `by decide` checks (from [Basic.lean](Basic.lean)) lower one logical `ZZ`-parity
measurement to a well-formed QStab program, verify the certificate's structural checks and
its noiseless detector determinism, and confirm that a certificate dishonestly claiming the
distance obligation is `certified` is REJECTED by `check`.

## Status & scope

Honest scope (Stage 5 "Surgery/Adapter" in [CONTRACT.md §1](../CONTRACT.md)):

- **D (`by decide`)** — what IS checked here: program well-formedness (`progZZ.wf`), the
  certificate's structural `check` (parity non-empty, a preserved logical, obligations
  deferred), noiseless detector determinism (`detectorsDeterministic?`, non-vacuous: requires
  a well-formed program and an in-range readout var), a flipped physical outcome flipping the
  readout, and rejection of a dishonest `certified` distance claim.
- **A (assumption / skeleton)** — `ppmMeasToQStab` is a one-measurement skeleton with **no
  pass-soundness theorem**. The `claimed*` fields (`claimedMergedCommutes`,
  `claimedDetectorsDet`, `claimedIrreducible`) are RECORDED claims, not decided.
- **M / A (deferred)** — distance, fault-distance, and decoder obligations are all
  `FaultStatus.deferred` (never certified by this layer). There is no operational lattice-
  surgery semantics here; this is not a full surgery semantics.

Nothing here is claimed as a proved pass-soundness theorem or a wired end-to-end edge beyond
the single-measurement lowering. The CONTRACT lists `PPM-measurement → QStab` =
`ppmMeasToQStab` as a **skeleton, no soundness theorem**.

## See also

- [../README.md](../README.md) — the Compiler layer overview.
- [../CONTRACT.md](../CONTRACT.md) — the full correctness-boundary matrix (Stage 5/6).
- [../LS/Cert.lean](../LS/Cert.lean) — where the re-exported types actually live, in the
  `Compiler.LS` lattice-surgery IR.
- [../../QStab/README.md](../../QStab/README.md) — the QStab physical-target language.
