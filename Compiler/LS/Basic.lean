/-
  Compiler.LS.Basic — PUBLIC AGGREGATE (umbrella) for the lattice-surgery IR (LSIR).

  LSIR is the missing surgery-schedule / certificate layer SHARED by both lowering
  paths:  PPM → LS → QStab  and  MagicQ cultivation → LS → QStab.  It is NOT another
  QStab: QStab owns the physical measurements / Clifford-prep / SSA parity dataflow;
  LS owns the surgical control structure (patches, rounds/slots, logical→physical
  measurement certificates, stabilizer-flow contracts, detector/observable/postselect
  annotations, deferred fault/decoder/quality obligations).

  Modules:
    * `Compiler/LS/Syntax.lean`     — the LS AST: sparse Pauli, ops, postselect policy,
                                       deferred contracts, flow contracts, programs.
    * `Compiler/LS/Cert.lean`       — surgery certificate + fault obligations (migrated
                                       from `Compiler/LS2QStab/Basic.lean`, now a shim).
    * `Compiler/LS/Check.lean`      — the LS checker (SSA / scope / sparse-Pauli / flow
                                       structure / detector determinism) + honest summary.
    * `Compiler/LS/LowerQStab.lean` — lower the executable ops to `QStab.StabilizerProg`
                                       + sidecar; the `lower_dataflow` preservation theorem.
    * `Compiler/LS/Extract.lean`     — classify which physical measurements current
                                       QStab2QClifford extraction schemes can handle.
    * `Compiler/LS/Geometry.lean`    — patch geometry metadata (`Frac`-rational coords).
    * `Compiler/LS/Chunk.lean`       — the GENERIC `LSChunk`/`LoweredChunk` abstraction +
                                       chunk-aware lowering (code/layout/protocol agnostic).
    * `Compiler/LS/ChunkCompose.lean`— generic sequential `List LSChunk` composition
                                       (QVar-offset + merge) + structural flow-interface match.
    * `Compiler/LS/SyndromeRounds.lean`— generic repeated syndrome-extraction chunk (real
                                       `prop` rounds + adjacent-round repeat detectors).
    * `Compiler/LS/PPM.lean`        — the PPM → LS adapter (requires a physical witness).
    * `Compiler/LS/MagicQ.lean`     — the MagicQ cultivation → LS stage scaffold.
    * `Compiler/LS/Gidney/Basic.lean`       — compatibility shim re-exporting `Compiler.LS.Chunk`.
    * `Compiler/LS/Gidney/Cultivation.lean` — the real d=3 double-cat / H_XY check
                                       `gen.Chunk` (7-MX body + 6 detectors + 8 flows).

  HONEST SCOPE: nothing here claims FULL-chunk Gidney exactness, surgery/flow soundness,
  or fault-distance / decoder correctness; those are explicit deferred obligations.
  Mathlib-free.
-/
import Compiler.LS.Syntax
import Compiler.LS.Cert
import Compiler.LS.Check
import Compiler.LS.Geometry
import Compiler.LS.LowerQStab
import Compiler.LS.Extract
import Compiler.LS.Chunk
import Compiler.LS.ChunkCompose
import Compiler.LS.SyndromeRounds
import Compiler.LS.PPM
import Compiler.LS.MagicQ
import Compiler.LS.Gidney.Basic
import Compiler.LS.Gidney.Cultivation
