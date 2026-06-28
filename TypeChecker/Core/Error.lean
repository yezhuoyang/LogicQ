/-
  TypeChecker.Core.Error — the type-error vocabulary (the only new "syntax";
  judgments return `Except TypeError <evidence>`).
-/

namespace TypeChecker

/-- Errors a type-checking judgment can raise. -/
inductive TypeError
  | badBlock               (b : Nat)        -- unknown block id
  | notLive                                 -- block already consumed / retired
  | notOwned                                -- a borrowed block cannot be consumed
  | shapeMismatch          (msg : String)   -- dimensions disagree
  | notSymplectic                           -- the gate action does not preserve J
  | stabilizerNotPreserved                  -- the gate maps a stabilizer outside the code
  | notLogicalOp                            -- a requested Pauli is not a logical operator
  | badLogicalIndex        (blk idx : Nat)  -- a logical-qubit index out of range for its block
  | malformedBlock         (b : Nat)        -- a block fails `Block.valid` (bad shape / not a code)
  | malformedTarget                         -- a switch TARGET code is malformed (not a source-block id)
  | emptyMeasurement                        -- a PPM target with no factors (no identity/no-op form)
  | nonNativeMeasurement                    -- a PPM target with >2 factors or a duplicate logical qubit
  | unboundOutcome         (r : Nat)        -- an adaptive `ite` branches on an unmeasured classical outcome
  | outcomeReused          (r : Nat)        -- a measurement binds a classical outcome var that is ALREADY bound (SSA violation)
  | useAfterDiscard        (blk idx : Nat)  -- a logical qubit is used after being discarded/consumed
  | notImplemented         (msg : String)   -- no legal implementation found for a logical operation
  | leak                   (b : Nat)        -- an owned block was never consumed
  | clone                  (b : Nat)        -- a block id aliased across two live owners
  | noCommonCapability     (msg : String)   -- no native PPM / adapter / switch path
  | certFailed             (msg : String)   -- a supplied certificate failed recomputation
  | other                  (msg : String)
  deriving Repr

/-- Did a judgment succeed? -/
def ok? {ε α : Type} : Except ε α → Bool
  | .ok _    => true
  | .error _ => false

/-- The success value, if any. -/
def res? {ε α : Type} : Except ε α → Option α
  | .ok a    => some a
  | .error _ => none

end TypeChecker
