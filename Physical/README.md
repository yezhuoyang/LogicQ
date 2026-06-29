# Physical

> The shared PHYSICAL-level vocabulary: physical qubit addresses and the dense 4-letter Pauli alphabet.

`Physical` is the bottom of the LogicQ stack: it fixes the names that the physical target IRs (`QStab`, `QClifford`) speak. While `ChainQ` code families, the `TypeChecker`, and the `Compiler` Mixed IR all reason about *logical* qubits of PPR/PPM, `Physical` is about the data/ancilla qubits of an actual surface-code patch. It is intentionally pure vocabulary (Mathlib-free, just `Nat`/`Char`/`List`) — the physical *semantics* live downstream in `QStab` and `QClifford`.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | Physical qubit index `PQubit`, the dense single-qubit `Pauli` alphabet (`I/X/Y/Z`), and char/string parsers for dense Pauli strings. |

## Key definitions

```lean
/-- A physical qubit index. -/
abbrev PQubit := Nat
```

```lean
/-- A single-qubit Pauli, INCLUDING identity (physical Pauli strings are dense,
    e.g. `ZZI = [Z, Z, I]`). -/
inductive Pauli
  | I | X | Y | Z
  deriving DecidableEq, Repr, Inhabited
```

```lean
/-- Parse a Pauli letter (`'X'`/`'Y'`/`'Z'`, anything else `I`). -/
def Pauli.ofChar : Char → Pauli
  | 'X' => .X | 'Y' => .Y | 'Z' => .Z | _ => .I

/-- Parse a dense physical Pauli string, e.g. `"ZZI" ↦ [Z, Z, I]`. -/
def ofString (s : String) : List Pauli := s.toList.map Pauli.ofChar
```

Note that `ofChar`/`ofString` are *total*: missing or unrecognized characters parse as `I` (no failure mode), which is why physical Pauli strings here are dense rather than sparse.

## Example

```lean
"ZZI"   ↦   [.Z, .Z, .I]    -- OK: trailing identity is kept (dense)
"ZZZ"   ↦   [.Z, .Z, .Z]    -- OK: a weight-3 Z string
```

These two values pin down the dense-string parser: `"ZZI"` becomes `[Z, Z, I]` (note the trailing identity is kept). Source: [Basic.lean](Basic.lean).

## Status & scope

- This folder is **pure vocabulary** — it defines names and a total parser, nothing more.
- The two parser values above are tier **D** (`by decide` tests in [Basic.lean](Basic.lean)) in the [CONTRACT](../Compiler/CONTRACT.md) sense: they confirm the concrete parse behavior, not any operational property.
- There is **no semantics here**: stabilizer/Clifford evolution, channel correctness, distance, decoders, and fault-tolerance claims all live downstream and are out of scope for this module (and many of those are themselves explicitly deferred). This module asserts none of them.
- No `axiom`s, no `sorry`, no deferred obligations are introduced by this file.

## See also

- [Repository root README](../README.md) — the full LogicQ pipeline overview.
- [QStab/README.md](../QStab/README.md) — physical stabilizer-IR target that consumes this vocabulary.
- [QClifford/README.md](../QClifford/README.md) — physical Clifford-circuit target that consumes this vocabulary.
