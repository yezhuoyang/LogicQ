/-
  MagicQ.Basic — PUBLIC AGGREGATE (umbrella) for the MagicQ magic-state protocol
  language (the first real MagicQ pass).

  PUBLIC ENTRYPOINT: `import MagicQ.Basic` for the whole MagicQ layer.  Internal
  modules:

    * `MagicQ/Syntax.lean`             — the protocol AST (bases, quality, carriers,
                                          linear resources, postselection, ops).
    * `MagicQ/Check.lean`              — the high-level checker (Γ ; Σ ; CheckState).
    * `MagicQ/Library/ReedMuller15.lean` — the Bravyi–Kitaev `[[15,1,3]]` code and
                                          the `rm15_to_1` protocol.
    * `MagicQ/Library/Cultivation.lean`  — the Gidney–Shutty–Jones `cultivate_T`
                                          protocol.

  The `decide` regression examples live in `MagicQ/Tests.lean`, which is NOT imported
  here (tests stay out of the public umbrella); build them with `lake build
  MagicQ.Tests`.

  MagicQ sits BESIDE the logical compiler: algorithm compilation emits typed
  `Compiler.MagicObligation`s; MagicQ compiles the factory/cultivation protocols
  that (eventually) discharge them.  This pass is high-level CHECKING only —
  stochastic fault tolerance and decoder performance are tracked as deferred
  obligations, never proven.  See `MagicQ/DESIGN_PLAN.md`.

  Mathlib-free.
-/
import MagicQ.Syntax
import MagicQ.Check
import MagicQ.Library.ReedMuller15
import MagicQ.Library.Cultivation
