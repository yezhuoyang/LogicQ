/-
  Compiler.LS.Gidney.Basic — COMPATIBILITY SHIM.

  The chunk abstraction (`LSChunk`, `LoweredChunk`, `lowerChunkCheckedWithExtract`, and
  the `LSChunk.*` helpers) is GENERIC and now lives in `Compiler.LS` (`Compiler/LS/Chunk.lean`)
  — it is NOT Gidney-specific.  This module re-exports it so existing
  `import Compiler.LS.Gidney.Basic` users keep working; Gidney-specific chunks live in the
  sibling `Compiler/LS/Gidney/*` modules.  Mathlib-free.
-/
import Compiler.LS.Chunk

namespace Compiler.LS.Gidney

-- re-export the generic chunk API under `Compiler.LS.Gidney.*` for source compatibility.
export Compiler.LS (LSChunk LoweredChunk lowerChunkCheckedWithExtract)

end Compiler.LS.Gidney
