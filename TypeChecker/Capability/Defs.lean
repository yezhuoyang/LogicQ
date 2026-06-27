/-
  TypeChecker.Capability.Defs — capabilities for joint logical measurements.

  A `Capability` is a proof-carrying witness that a set of logical blocks CAN be
  jointly measured: it supplies the surgery/adapter CONSTRUCTION (ancilla qubits
  + connection stabilizers, over the merged symplectic space).  The `kind`
  selects only the deferred obligations — the certificate the checker recomputes
  is unified and GENERAL (works for any QEC code): the merged code is valid, it
  preserves the data codes, and it measures the requested logical Pauli.
-/
import TypeChecker.Core.Block

namespace TypeChecker
open ChainQ.GF2

/-- The construction realizing a joint measurement — selects the obligations,
    not the algebraic certificate (which is unified). -/
inductive CapKind
  | nativeSurgery            -- same-family lattice/code surgery
  | adapterPPM               -- universal adapter between LDPC codes (2410.03628)
  | productSurgery           -- product / homological-product surgery (2407.18490)
  | homomorphicMeasurement   -- homomorphic / homological measurement (2211.03625, 2410.02753)
  | bridge                   -- bridge / teleportation domain (2407.18393, 2503.10390)
  deriving DecidableEq, Repr

/-- A joint-measurement capability over a set of data `blocks` (listed in the
    order they are lifted into the merged space).  It adds `ancN` ancilla qubits
    and the `connStab` connection/ancilla stabilizer rows (over the merged
    `2·(Σ n_block + ancN)`-wide symplectic space). -/
structure Capability where
  kind     : CapKind
  blocks   : List BlockId
  ancN     : Nat
  connStab : BoolMat
  deriving Repr

/-- A capability whose connection stabilizers are PROVEN to have the right width
    `2·mergedN` for a declared merged size.  Constructed only via `mkCapability?`,
    so the `connStab` shape cannot silently disagree.
    NOTE: for an EMPTY `connStab` the width proof is vacuous (it constrains no
    `mergedN`) — a degenerate no-connection capability.  This is harmless: the
    matcher `checkPPM` takes a raw `Capability` and RE-validates the `connStab`
    width against the actual `mergedN` before using it, so a vacuous typed wrapper
    is never trusted by the merge. -/
structure CheckedCapability where
  cap     : Capability
  mergedN : Nat
  connWf  : cap.connStab.all (fun r => decide (r.length = 2 * mergedN)) = true

/-- Validate a capability's `connStab` width against a declared `mergedN`. -/
def mkCapability? (cap : Capability) (mergedN : Nat) : Except TypeError CheckedCapability :=
  if h : cap.connStab.all (fun r => decide (r.length = 2 * mergedN)) = true then
    .ok ⟨cap, mergedN, h⟩
  else .error (.shapeMismatch "capability connStab rows must have width 2·mergedN")

-- a connStab of width 8 is well-formed for mergedN = 4, malformed for mergedN = 3:
private def capW8 : Capability :=
  { kind := .adapterPPM, blocks := [0, 1], ancN := 0,
    connStab := [[false, false, false, false, true, true, false, false]] }
example : ok? (mkCapability? capW8 4) = true := by decide
example : ok? (mkCapability? capW8 3) = false := by decide

end TypeChecker
