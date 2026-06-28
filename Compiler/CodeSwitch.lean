/-
  Compiler.CodeSwitch — SHIM (M20 strict-folder-ownership refactor).

  The typed code-switch / dimension-jump certificate skeleton (EXTERNAL/ASSUMED, not
  verification) now lives in `Compiler.CodeSwitch.Basic`; this shim re-exports it
  (namespace `Compiler.CodeSwitch` unchanged) so `import Compiler.CodeSwitch` keeps
  resolving `SwitchProtocolCert`/`structuralCheck`/… unchanged.
-/
import Compiler.CodeSwitch.Basic
import Compiler.CodeSwitch.QLDPCPapers
import Compiler.CodeSwitch.QLDPCPapers.Concrete
import Compiler.CodeSwitch.QLDPCPapers.Verification
-- QGPU / qLDPC PL-extension (product surgery, clustered addressing, batch axis, dimension
-- jump, GPPM semantics): typed certificates with recomputed GF(2) checks + deferred FT.
import Compiler.CodeSwitch.ProductSurgery
import Compiler.CodeSwitch.QGPUAddr
import Compiler.CodeSwitch.BatchedSwitch
import Compiler.CodeSwitch.DimensionJump
import Compiler.CodeSwitch.GPPMSemantics
-- The FORMAL qLDPC MixIR-status layer (lowersToMixIR | externalOnly) + the checked headline.
import Compiler.CodeSwitch.QLDPCStatus
