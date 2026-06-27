/-
  TypeChecker.Judgment.Transversal — AGGREGATOR (M20 strict-folder-ownership refactor).

  The transversal/automorphism judgments (binary-symplectic matrix algebra), split by
  ownership under Judgment/Transversal/:
    * `Judgment.Transversal.Cert`     — `TypedAutomorphism`/`TypedTransversal` (data)
    * `Judgment.Transversal.Check`    — `checkLogicalAutomorphism`/`Internal.transversalMap`/`checkTransversal`
    * `Judgment.Transversal.Examples` — the worked examples + their fixtures

  Every name stays in `namespace TypeChecker`, so `import TypeChecker.Judgment.Transversal`
  keeps resolving `checkTransversal`/`Internal.transversalMap`/`checkLogicalAutomorphism`.
-/
import TypeChecker.Judgment.Transversal.Cert
import TypeChecker.Judgment.Transversal.Check
import TypeChecker.Judgment.Transversal.Examples
