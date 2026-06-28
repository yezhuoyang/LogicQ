# TypeChecker

> Static legality checker for logical operations over typed QEC blocks: the
> judgments accept an operation only when a finite GF(2)/symplectic certificate
> can be recomputed, and the soundness layer reads that certificate back out.

This layer sits between the front-end ChainQ code families and the Compiler Mixed
IR. It does **not** execute programs; given a typed environment of blocks
(`TypedEnv`), it decides whether a requested logical operation — a transversal
gate, logical automorphism, code switch, or (cross-block / high-weight) PPM — is
algebraically legal for the current codes. Acceptance returns
`Except TypeError evidence`, and [Soundness.lean](Soundness.lean) proves that a
`.ok` result genuinely entails the underlying algebraic facts. Downstream the
checked operations flow on into Compiler Mixed IR and eventually the
QStab/QClifford physical target.

## What's here

This folder's own modules (internals live under the subfolders linked in
[See also](#see-also)):

| Module | Role |
| --- | --- |
| [Basic.lean](Basic.lean) | PUBLIC umbrella: `import TypeChecker.Basic` pulls in the whole checker (Core, Capability, all Judgment folders, Soundness). Root-level `.lean` files are forbidden by policy (M21). |
| [Soundness.lean](Soundness.lean) | Milestone-4/M6/M7 soundness theorems: each extracts, from "the judgment returned `.ok`", the algebraic certificate that genuinely holds. |

## Key definitions

Real signatures from [Soundness.lean](Soundness.lean):

```lean
theorem Block.valid_complete {b : Block} (h : Block.valid b = true) :
    b.lx.length = b.n - rank b.stab
```

```lean
theorem checkTransversal_sound {Γ : TypedEnv} {b : BlockId} {g : BoolMat}
    {e : TypedTransversal} {tb : TypedBlock} (hb : Γ.block? b = some tb)
    (h : checkTransversal Γ b g = .ok e) :
    preservesSymp 1 g = true ∧
      (applyMap tb.block.n (Internal.transversalMap tb.block.n g) tb.block.stab).all
        (fun r => inSpan tb.block.stab r) = true
```

```lean
theorem checkSwitch_sound {Γ : TypedEnv} {b : BlockId} {D : TypedBlock} {cert : SwitchCert}
    {tb : TypedBlock} {ev : TypedEnv × TypedSwitch} (hC : Γ.block? b = some tb)
    (h : checkSwitch Γ b D cert = .ok ev) :
    tb.block.live = true ∧ tb.block.own = Owned.owned ∧ ...
```

```lean
theorem checkPPM_merged_sound {Γ : TypedEnv} {caps : List Capability} {P : PPM.MTarget}
    {r : TypedPPM} {bos : List (BlockId × Block × Nat)} {dataN : Nat} {cap : Capability} ...
```

(`checkLogicalAutomorphism_sound`, `checkTransversalCNOT_sound`,
`checkTransversalCNOTBatch_sound`, `checkPPM_nonempty`, and `checkPPM_noDup`
round out the set.)

## Example

```lean
/-- **`checkPPM` rejects empty targets** (no identity/no-op measurement form). -/
theorem checkPPM_nonempty {Γ : TypedEnv} {caps : List Capability} {P : PPM.MTarget}
    {r : TypedPPM} (h : checkPPM Γ caps P = .ok r) : P.isEmpty = false := by
  simp only [checkPPM] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hne; simpa using hne
```

This is the smallest soundness theorem in the layer: it shows that whenever
`checkPPM` accepts a measurement target `P`, that target is non-empty — the
checker never certifies a no-op identity measurement. Source:
[Soundness.lean](Soundness.lean).

## Status & scope

Using the tiers from [Compiler/CONTRACT.md](../Compiler/CONTRACT.md)
(P = proved theorem, D = `by decide` test, A = documented assumption,
M = missing/planned):

- **P — soundness of the static judgments.** Every theorem in
  [Soundness.lean](Soundness.lean) is fully proved: acceptance by
  `checkTransversal`, `checkLogicalAutomorphism`, `checkTransversalCNOT(Batch)`,
  `checkSwitch`, and `checkPPM` entails the corresponding symplectic /
  stabilizer-preservation / merged-code certificate. These are the usual
  `propext`-style soundness results (NOT advertised as "axiom-free").
- **M7 typing discipline.** Judgments run over a `TypedEnv`/`TypedBlock`, so
  block well-formedness is guaranteed by the types; soundness statements no
  longer restate `Block.valid` guards. `Block.valid_complete` reads the
  `k = n − rank(stab)` completeness law back out.
- **Scope boundary (A/M).** This is a STATIC algebraic-legality layer. It proves
  that requested logical operations are legal for the current codes; it does NOT
  prove channel correctness, fault tolerance, code distance, decoder behavior, or
  operational equivalence — those are explicitly deferred elsewhere in the stack.
  Certificate verification for individual judgments (and any `by decide`
  examples) lives in the [Judgment](Judgment/README.md) subfolders, not here.

## See also

- Parent / repo root: [../README.md](../README.md)
- [Core/README.md](Core/README.md) — blocks, symplectic algebra, elaboration, errors, distance.
- [Capability/README.md](Capability/README.md) — cross-block measurement capabilities.
- [Judgment/README.md](Judgment/README.md) — Transversal, Switch, PPM, and PPMProgram checks.
- [PPM/README.md](PPM/README.md) · [PPR/README.md](PPR/README.md) · [LatticeSurgery/README.md](LatticeSurgery/README.md) · [ChainQ/README.md](ChainQ/README.md)
