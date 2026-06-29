# Compiler/QASM

> An OpenQASM-2 front-end: parse a QASM source string, map its virtual qubits onto LogicQ logical qubits, and emit checked Mixed IR through the verified `Compiler.ChainQ2Mixed` compiler.

This is the **text-entry point** of the LogicQ stack. It parses a conservative OpenQASM-2 subset to a small source AST, performs **first-fit logical allocation** of virtual qubits onto user-declared ChainQ logical qubits (with a basis-tagged ancilla pool), translates the supported instructions to `ChainQPrimOp`s, and hands the result to the verified `compileChainQToMixIR?` for all real gate-legality checking. It sits *above* `TypeChecker`/`Compiler.ChainQ2Mixed` and reuses them — it does **not** re-implement gate legality. `Physical.lean` wires this front-end further down to checked MixedIR -> QStab -> QClifford for the verified structural fragment only.

Rejection is a **correct compiler result**, not a crash: out-of-contract gates (`rx/ry/rz`, `u3`, `reset`, dynamic `if`, custom gates) parse to `Instr.unsupported name` and are rejected by the allocator; malformed text is a `ParseError`.

## What's here

| Module | Role |
|---|---|
| [Basic.lean](Basic.lean) | Public umbrella; imports `Syntax`, `Allocate`, `Parse`, `Physical`, `AuditTests`. |
| [Syntax.lean](Syntax.lean) | OpenQASM-2-style source AST: `VQubit`/`VCBit`, `QReg`/`CReg`, the `Instr` subset (+ `unsupported`), `QASMProgram`, flatten/validation predicates. Pure data, no LogicQ dependency. |
| [Allocate.lean](Allocate.lean) | `NamedLogical`, `AllocationRequest`, `QASMError`, `Allocation`, `QASMArtifact`; `allocate?` (first-fit + resource validation + translation) and the public `compileQASMToMixIR?`; positive/negative `by decide` tests. |
| [Parse.lean](Parse.lean) | Total OpenQASM-2 text parser `parseOpenQASM2?` (text → AST, over `List Char`) + the phase-distinguished `compileOpenQASM2ToMixIR?` parse+compile helper; `by decide` parse + end-to-end tests. |
| [Physical.lean](Physical.lean) | QASM artifact -> checked MixedIR -> QStab structural compiler -> QClifford extraction circuits (`compileQASMToQClifford?` / `compileOpenQASM2ToQClifford?`) for the verified stabilizer fragment. |
| [AuditTests.lean](AuditTests.lean) | Additive adversarial-audit `by decide` regression tests (CRLF, zero-size registers, missing `logicalIndex`, multi-`qreg` first-fit order, strict-CNOT, …), self-contained over the public API. |
| [Benchmarks.lean](Benchmarks.lean) | Curated QASMBench regression suite of embedded raw QASM programs under MixedIR allocation setups plus separated-bare physical QClifford guards (not imported by `Basic.lean`; a heavier stress target). |

## Key definitions

```lean
-- Syntax.lean — the supported instruction subset (unsupported = parsed-but-rejected)
inductive Instr where
  | h          (q : VQubit)
  | s          (q : VQubit)
  | x          (q : VQubit)
  | z          (q : VQubit)
  | t          (q : VQubit)
  | cx         (c t : VQubit)
  | cz         (c t : VQubit)
  | measure    (q : VQubit) (target : VCBit)
  | barrier    (qs : List VQubit)
  | unsupported (name : String)

-- Allocate.lean — the cap-independent allocation request
structure AllocationRequest where
  decls           : List ChainQ.NamedCodeDecl
  dataLogicals    : List NamedLogical
  ancillas        : List NamedAnc
  cnotMode        : CNOTMode := .preferTransversalWithPPMFallback
  cnotIncidence   : Option BoolMat := none

-- Allocate.lean — the public QASM → MixIR compiler (reuses compileChainQToMixIR?)
def compileQASMToMixIR? (ws : List CapabilityWitness) (prog : QASMProgram) (req : AllocationRequest) :
    Except QASMError (QASMArtifact ws)

-- Parse.lean — the total text parser, and the parse+compile end-to-end helper
def parseOpenQASM2? (src : String) : Except ParseError QASMProgram
def compileOpenQASM2ToMixIR? (ws : List Compiler.CodeSwitch.CapabilityWitness) (src : String)
    (req : AllocationRequest) : Except FrontendError (QASMArtifact ws)

-- Physical.lean — checked structural physical compiler
def compileOpenQASM2ToQClifford? (ws : List CapabilityWitness) (src : String)
    (req : AllocationRequest) : Except PhysicalCompileError (QASMPhysicalArtifact ws)
```

The deferred physical obligations of the underlying compiler are preserved verbatim via
`QASMArtifact.obligations`. Physical compilation succeeds only when the current QStab/QClifford
structural lowerer can discharge the relevant QStab/extraction obligations.

## Example

```lean
-- a full Bell-style program: header, include, comment, qreg/creg, h/cx/measure, newlines:
def bellSrc : String :=
  "OPENQASM 2.0;\ninclude \"qelib1.inc\";\nqreg q[2];\ncreg c[2];\nh q[0]; // hadamard\ncx q[0],q[1];\nmeasure q[0] -> c[0];\nmeasure q[1] -> c[1];\n"

-- parsing `bellSrc` yields exactly this `QASMProgram` AST (header/include/comment dropped):
-- OK:
{ qregs := [⟨"q", 2⟩], cregs := [⟨"c", 2⟩],
  instrs := [.h ⟨"q", 0⟩, .cx ⟨"q", 0⟩ ⟨"q", 1⟩,
             .measure ⟨"q", 0⟩ ⟨"c", 0⟩, .measure ⟨"q", 1⟩ ⟨"c", 1⟩] }

-- out-of-contract gates are NEVER dropped — they parse to `.unsupported name` and the
-- allocator rejects them (the source string ⇒ the resulting instr list):
"rx(0.3) q[0];"           -- rejected: instrs := [.unsupported "rx"]
"u3(0,0,0) q[0];"         -- rejected: instrs := [.unsupported "u3"]
"reset q[0];"             -- rejected: instrs := [.unsupported "reset"]
"if (c==1) x q[0];"       -- rejected: instrs := [.unsupported "if"]
"ccx q[0],q[1],q[2];"     -- rejected: instrs := [.unsupported "ccx"]
```

The text parser maps a header/include/comment-bearing Bell program to exactly that AST. The
source value `bellSrc` and the parsed `QASMProgram` value are from [Parse.lean](Parse.lean)
(§5, lines 321–326); the `.unsupported` values are from §6 (lines 348–357). The whole parser
is written over `List Char` (via `src.toList`) specifically so these values stay
kernel-reducible / `by decide`-checkable.

## Status & scope

Honest scope, mirroring `Compiler/CONTRACT.md` tiers (D = `by decide` test, A = documented assumption, M = missing/planned):

- **(D) Parser + allocator + typed emission.** Both phases are exercised by extensive positive/negative `by decide` tests in [Parse.lean](Parse.lean), [Allocate.lean](Allocate.lean), and [AuditTests.lean](AuditTests.lean): supported gates, exact aliases (`sdg`, `tdg`), comments, malformed-text `ParseError`s, out-of-contract `Instr.unsupported`, resource validation, fresh SSA measurement `CVar`s, and strict vs. fallback CNOT mode.
- **(A/reuse) Legality checking is delegated, not re-proved here.** `compileQASMToMixIR?` calls the verified `compileChainQToMixIR?`, which performs the real addressing / ancilla basis & consumption / PPM / transversal / magic typing. This layer adds no new soundness theorem — it reuses the underlying one.
- **(M) Completeness is bounded.** The pipeline is complete **only** for the accepted QASM subset (`h s x z t cx cz measure barrier`, with `sdg`/`tdg` expanded), given enough basis-correct user-supplied logical/ancilla resources, and subject to existing ChainQ/TypeChecker legality. **No** arbitrary rotations, **no** Clifford+T synthesis, **no** custom-gate expansion, **no** `reset`, **no** dynamic `if` — these are correct rejections, never approximations.
- **(M / deferred) No full physical correctness.** The emitted `CompiledMixIR` is checked for logical/resource legality. [Physical.lean](Physical.lean) adds a real structural QStab/QClifford path for the currently verified stabilizer fragment and prepends one physical stabilizer-extraction pass over every resident code block. Repeated syndrome rounds, decoder logic, fault-tolerance padding, and T-gate magic injection remain **deferred obligations**. The physical path still **explicitly rejects** `.magic`, `.switch`, scheduled/controlled PPM, automorphisms without chunks, and parallel PPM rather than fabricating a circuit.
- **(D) Benchmark boundary.** [Benchmarks.lean](Benchmarks.lean) embeds 20 QASMBench programs. All 20 still compile through MixedIR under the existing separated/packed bare setups; every no-magic case also compiles through QClifford under separated bare blocks, while the T-containing cases are kept as negative physical tests until MagicQ gate injection is wired.

Everything outside the contract is a correct rejection (`ParseError` for malformed text, `QASMError`/`FrontendError.compile` for out-of-contract gates or insufficient/ill-typed resources), never a silent drop or miscompile.

## See also

- [../README.md](../README.md) — the `Compiler/` layer overview.
- [../../README.md](../../README.md) — the LogicQ repository root.
- [../CONTRACT.md](../CONTRACT.md) — the proof-tier contract (P / D / A / M) this README's status section mirrors.

This folder has no child-directory READMEs (no nested subfolders).
