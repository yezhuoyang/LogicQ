# TypeChecker/Capability

> Proof-carrying capabilities for joint logical measurements across code blocks.

This layer defines the `Capability` witness: a description of how a set of logical
blocks may be merged so a joint logical Pauli can be measured (lattice surgery,
universal adapter PPM, product surgery, homomorphic measurement, or bridge). It
sits inside the TypeChecker legality stage — front-end ChainQ code families feed
blocks here; the cross-code-PPM matcher (`checkPPM`, elsewhere in TypeChecker)
consumes these capabilities before lowering toward the Compiler Mixed IR and the
QStab/QClifford physical target. The `kind` only selects deferred physical
obligations; the algebraic merged-code certificate is recomputed downstream.

## What's here

| Module | Role |
| --- | --- |
| [Defs.lean](Defs.lean) | `CapKind`, `Capability`, `CheckedCapability`, and the width-validating `mkCapability?` constructor. |

## Key definitions

```lean
inductive CapKind
  | nativeSurgery            -- same-family lattice/code surgery
  | adapterPPM               -- universal adapter between LDPC codes (2410.03628)
  | productSurgery           -- product / homological-product surgery (2407.18490)
  | homomorphicMeasurement   -- homomorphic / homological measurement (2211.03625, 2410.02753)
  | bridge                   -- bridge / teleportation domain (2407.18393, 2503.10390)
  deriving DecidableEq, Repr
```

```lean
structure Capability where
  kind     : CapKind
  blocks   : List BlockId
  ancN     : Nat
  connStab : BoolMat
  deriving Repr
```

```lean
structure CheckedCapability where
  cap     : Capability
  mergedN : Nat
  connWf  : cap.connStab.all (fun r => decide (r.length = 2 * mergedN)) = true
```

```lean
def mkCapability? (cap : Capability) (mergedN : Nat) : Except TypeError CheckedCapability :=
  if h : cap.connStab.all (fun r => decide (r.length = 2 * mergedN)) = true then
    .ok ⟨cap, mergedN, h⟩
  else .error (.shapeMismatch "capability connStab rows must have width 2·mergedN")
```

Here `BlockId := Nat` ([../Core/Block.lean](../Core/Block.lean)) and
`BoolMat := List BoolVec` ([../../ChainQ/Algebra/GF2.lean](../../ChainQ/Algebra/GF2.lean)).
A `Capability` adds `ancN` ancilla qubits and the `connStab` connection-stabilizer
rows over the merged `2·(Σ n_block + ancN)`-wide symplectic space.

## Example

```lean
-- a connStab of width 8 is well-formed for mergedN = 4, malformed for mergedN = 3:
private def capW8 : Capability :=
  { kind := .adapterPPM, blocks := [0, 1], ancN := 0,
    connStab := [[false, false, false, false, true, true, false, false]] }

-- capW8 against mergedN = 4:  -- OK: connStab row width 8 = 2·4, builds a CheckedCapability
-- capW8 against mergedN = 3:  -- rejected: row width 8 ≠ 2·3 = 6 (shapeMismatch)
```

An 8-wide connection-stabilizer row validates as a `CheckedCapability` for
`mergedN = 4` (width `2·4 = 8`) and is rejected for `mergedN = 3`.
Source: [Defs.lean](Defs.lean) (lines 56-61).

## Status & scope

- **D (`by decide`)**: The two width examples in [Defs.lean](Defs.lean) are
  machine-checked sanity tests, not soundness theorems.
- **P (proved invariant)**: `CheckedCapability` carries a width proof `connWf`, and
  `mkCapability?` only emits it via the dependent `if h : …` branch — so a
  `CheckedCapability`'s `connStab` shape cannot silently disagree with its
  declared `mergedN`.
- **A (documented assumption / deferred)**: The `kind` only *selects* which
  physical/fault-tolerance obligations are deferred (surgery distance, decoder,
  channel correctness); none of those are discharged here. As the source notes, an
  *empty* `connStab` makes the width proof vacuous, so the matcher `checkPPM`
  RE-validates `connStab` width against the actual `mergedN` and does not trust the
  typed wrapper blindly. The references cited in `CapKind` constructors
  (2410.03628, 2407.18490, 2211.03625, 2410.02753, 2407.18393, 2503.10390) are the
  external constructions whose algebraic certificates are recomputed downstream, not
  proved in this file.

There are no soundness theorems or `#eval`s in this folder; it is a definitions
module consumed by the cross-code-PPM checker elsewhere in TypeChecker.

## See also

- Parent: [../README.md](../README.md) — TypeChecker legality stage.
- Repo root: [../../README.md](../../README.md).
- `BlockId` / block model: [../Core/Block.lean](../Core/Block.lean).
- GF(2) `BoolMat` algebra: [../../ChainQ/Algebra/README.md](../../ChainQ/Algebra/README.md).
