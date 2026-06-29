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

The native fixture in this folder ([`Basic.lean`](Basic.lean)) — the `progZZ` definition and
the QStab `Prog` value it unfolds to (`ppmMeasToQStab (some ⟨0,0⟩) (Physical.ofString "ZZ")` =
`[.prop (some ⟨0,0⟩) [Pauli.Z, Pauli.Z], .parity [0]]`):

```lean
def progZZ : QStab.Prog := LS.ppmMeasToQStab (some ⟨0, 0⟩) (Physical.ofString "ZZ")

-- progZZ as a concrete QStab.Prog value:
[ .prop (some ⟨0,0⟩) [Pauli.Z, Pauli.Z]   -- stmt 0: measure the ZZ parity (scheduled at slot ⟨0,0⟩)
, .parity [0] ]                            -- stmt 1: read its outcome (the readout var = 1)
```

This is a pass-bridge edge, so the two sides have concrete surface syntax. The SOURCE is a
single logical Z-parity PPM measurement (parses today — [`PPM/Parse.lean`](../../PPM/Parse.lean)):

```text
c0 := M q[0]↦Z, q[1]↦Z      -- one logical Z⊗Z (ZZ) parity measurement
```

`ppmMeasToQStab` lowers that to the TARGET QStab program `progZZ`, whose value is exactly what
the QStab text parser produces (parses today — [`QStab/Parse.lean`](../../QStab/Parse.lean)):

```text
c0 = Prop[r=0,s=0] ZZ       -- measure the dense physical Z-parity ZZ at round 0, slot 0
d0 = Parity c0              -- read its outcome (the readout var = 1)
```

## Example

The native `ZZ`-parity fixture (from [Basic.lean](Basic.lean)) — the `progZZ` program above
plus the `certZZ` certificate VALUE it certifies:

```lean
-- The surgery certificate VALUE for the ZZ-parity measurement (the recorded surgery data
-- with all fault obligations DEFERRED):
def certZZ : LS.SurgeryCert where
  measuredParity        := Physical.ofString "ZZ"    -- the measured logical Z-parity = [Pauli.Z, Pauli.Z]
  preservedLogicals     := [Physical.ofString "XX"]  -- the X-logical preserved by a Z-parity merge = [[Pauli.X, Pauli.X]]
  byproductFrame        := []                       -- +1 outcome ⇒ no byproduct (track-not-apply)
  claimedMergedCommutes := true                     -- CLAIM: ZZ commutes with the data Z-stabilizers (CSS)
  claimedDetectorsDet   := true                     -- CLAIM: noiseless ⇒ deterministic
  claimedIrreducible    := true                     -- CLAIM: a single 2-qubit Z parity is irreducible
  faults                := {}                        -- distance / fault-distance / decoder: all DEFERRED
```

These values lower one logical `ZZ`-parity measurement to a well-formed QStab program and
record its certificate; their checked outcomes (from [Basic.lean](Basic.lean)) are:

```lean
certZZ.check                                                       -- = true:  parity nonempty, a preserved logical, all deferred
LS.SurgeryCert.detectorsDeterministic? progZZ LS.ppmMeasToQStab_readout  -- = true:  noiseless ⇒ fixed readout (readout var = 1, in range, wf)
certZZ.faults.allDeferred                                          -- = true:  none certified — honest by construction
LS.SurgeryCert.check { certZZ with faults := { distance := .certified } }
                                                                  -- = false: a cert dishonestly claiming `certified` distance is REJECTED
certZZ.measuredParity                                              -- = [Pauli.Z, Pauli.Z]
certZZ.preservedLogicals                                          -- = [[Pauli.X, Pauli.X]]
```

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
