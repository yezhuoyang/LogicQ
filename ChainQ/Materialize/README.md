# ChainQ / Materialize

> Concrete matrix export for ChainQ CSS codes: turn a `CSSCode` into its honest GF(2) check and symplectic-stabilizer matrices.

This is the front-end accessor layer (M20 Part B) sitting on top of the ChainQ code types and parametric families. For FIXED parameters the family constructors (`surface`/`toric`/`mkHGP`/`mkBB`/`mkLiftedProduct`) compute CONCRETE GF(2) check matrices — not symbolic placeholders — and this module exposes the accessors (`xChecks`, `zChecks`, `checkMatrices`, `symplecticStabilizers`) that materialize a `CSSCode` into those matrices. The width-`2n` symplectic stabilizer matrix is exactly the convention `TypeChecker` uses for `Block.stab`: the front-end owns the CSS→stabilizer path, and the former `TypeChecker.cssToStab` is now a thin alias of `CSSCode.symplecticStabilizers`.

## What's here

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | The CSS materialization / export API: `xChecks`, `zChecks`, `checkMatrices`, `symplecticStabilizers`. |
| [Tests.lean](Tests.lean) | `by decide` tests that family constructors compute concrete matrices for fixed parameters (exact surface-2 `Hx`/`Hz`, surface-3 shape, surface-2 symplectic matrix, `mkSurface 2` agreement, smoke tests across all five families). |

## Key definitions

```lean
/-- The X-check (parity) matrix: `hx`, rows over the `n` data qubits. -/
def CSSCode.xChecks (c : CSSCode) : BoolMat := c.hx

/-- The Z-check (parity) matrix: `hz`. -/
def CSSCode.zChecks (c : CSSCode) : BoolMat := c.hz

/-- Both check matrices as the pair `(hx, hz)`. -/
def CSSCode.checkMatrices (c : CSSCode) : BoolMat × BoolMat := (c.hx, c.hz)

/-- The complete symplectic stabilizer-check matrix (width `2·n`) ... -/
def CSSCode.symplecticStabilizers (c : CSSCode) : BoolMat :=
  c.hx.map (fun row => row ++ List.replicate c.n false) ++
  c.hz.map (fun row => List.replicate c.n false ++ row)
```

In `symplecticStabilizers`, each X-check row `r` (width `n`) is laid out as `r ++ 0ⁿ`, each Z-check row `r` as `0ⁿ ++ r`, with all X-rows before all Z-rows. Row count = `hx.length + hz.length`. See [Basic.lean](Basic.lean).

## Example

```lean
example : (surface 2).symplecticStabilizers =
  [[true, false, true, false, true, false, false, false, false, false],
   [false, true, false, true, true, false, false, false, false, false],
   [false, false, false, false, false, true, true, false, false, true],
   [false, false, false, false, false, false, false, true, true, true]] := by decide
```

The surface-2 code materializes to a concrete 4-row, width-`2n = 10` symplectic stabilizer matrix — verified by `decide`, demonstrating that the family constructor produces an honest GF(2) value rather than a placeholder. Source: [Tests.lean](Tests.lean) §3.

## Status & scope

- **D (`by decide`)** — Every claim here is a closed `decide` test in [Tests.lean](Tests.lean): exact surface-2 check matrices and symplectic matrix, surface-3 shapes, `mkSurface 2` agreeing with the raw `surface 2` matrices, and well-shapedness smoke tests across all five families (surface, toric, HGP, BB, lifted product).
- **No validation here.** [Basic.lean](Basic.lean) does NOT validate a code. Use `mkCSS` or a checked family constructor (see [../Checked/README.md](../Checked/README.md)) first if validity matters.
- **Redundant generators allowed.** The "complete stabilizer set" means the generated check rows `Hx`/`Hz`; we do NOT claim independence or minimality of generators.
- **Out of scope (deferred).** Code DISTANCE and FAULT-TOLERANCE are explicitly out of scope for this module, consistent with the repository's honest-scope tiering.

## See also

- Parent: [../README.md](../README.md) (ChainQ front-end code type system)
- Sibling: [../Checked/README.md](../Checked/README.md) (validity-carrying constructors)
- Sibling: [../Core/README.md](../Core/README.md) (code types, chain complexes, parameters)
- Sibling: [../Algebra/README.md](../Algebra/README.md) (GF(2) matrix kernel)
