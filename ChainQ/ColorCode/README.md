# ChainQ/ColorCode

> Reserved slot for color-code families in the ChainQ front-end. No Lean implementation yet.

This folder is a **planned** member of the ChainQ code-family layer — the front-end where parametric QEC code families materialize concrete `CSSCode` / `ChainComplex` values that later flow through the TypeChecker (legality) into the Compiler Mixed IR and on to the QStab/QClifford physical target. Sibling families (Surface, Toric, HGP, BB, LiftedProduct) already follow the ChainQ pattern; color codes are not built here yet.

## What's here

There are currently **no `.lean` modules** in this folder and **no child subdirectories** — only this README. When the implementation lands it should follow the ChainQ rule used by the other families: define the family parametrically, materialize a concrete `CSSCode` for fixed parameters, and add checked constructors plus matrix-shape / CSS-condition examples.

| Module | Role |
| --- | --- |
| _(none yet)_ | Color-code family construction is planned but unimplemented. |

## Key definitions

None in this folder. For the pattern a future `ColorCode` module is expected to follow, see the sibling families. For example, the Surface family (in [../Surface/README.md](../Surface/README.md)) exposes:

```text
surface d      -- HGP(repOpen d, repOpen d), a concrete CSSCode for fixed d
surface? d     -- option-returning checked constructor (rejects d < 2)
mkSurface d    -- checked constructor
```

A color-code family here would analogously provide a parametric constructor, an option/checked variant, and a validity argument inheriting the CSS condition `Hx * Hzᵀ = 0`.

## Example

This folder is a header/stub only — there is no Lean code to quote. The README's own statement of intent is the entire content:

```text
Reserved for color-code families.

There is no Lean implementation in this folder yet.  When it lands, the code
should follow the ChainQ rule: define the family parametrically, materialize a
concrete CSSCode for fixed parameters, and add checked constructors plus
matrix-shape/CSS-condition examples.
```

Source: this file, [README.md](README.md) (prior content, preserved).

## Status & scope

- **M (missing / planned):** the entire color-code family. No types, defs, theorems, `#eval`s, or `by decide` tests exist in this folder.
- Nothing here is proved or wired. There are no soundness theorems, no `propext`-clean obligations, and no `by decide` validity tests in this folder, because there is no code.
- Channel correctness, fault-tolerance, distance, and decoder properties are **out of scope** for ChainQ generally (ChainQ only asserts structural validity such as `ChainComplex.valid` / `CSSCode.valid`), and remain unaddressed here in any case.

Do not treat any color-code construction as available from this module until a `.lean` file is added.

## See also

- Parent layer: [../README.md](../README.md) — the ChainQ front-end code type system.
- Sibling code families for the pattern to follow: [../Surface/README.md](../Surface/README.md), [../Toric/README.md](../Toric/README.md), [../HGPCode/README.md](../HGPCode/README.md), [../BBCode/README.md](../BBCode/README.md), [../LiftedProduct/README.md](../LiftedProduct/README.md).
- Supporting layers: [../Core/README.md](../Core/README.md) (code types, chain complexes), [../Algebra/README.md](../Algebra/README.md) (GF(2) matrix kernel), [../Materialize/README.md](../Materialize/README.md) (concrete check/stabilizer export), [../Checked/README.md](../Checked/README.md) (validity-carrying constructors).
