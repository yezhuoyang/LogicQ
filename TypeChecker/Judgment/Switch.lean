/-
  TypeChecker.Judgment.Switch — AGGREGATOR (M20 strict-folder-ownership refactor).

  Code switching as a typed coercion, split by ownership under Judgment/Switch/:
    * `Judgment.Switch.Cert`     — `SwitchKind`/`SwitchCert`/`TypedSwitch` (data)
    * `Judgment.Switch.Check`    — `checkSwitch`/`toTargetBlock?`/`mkSwitchCert?` + helpers
    * `Judgment.Switch.Examples` — the worked examples + their fixtures

  Every name stays in `namespace TypeChecker`, so `import TypeChecker.Judgment.Switch`
  keeps resolving `checkSwitch`/`SwitchCert`/`toTargetBlock?` unchanged.
-/
import TypeChecker.Judgment.Switch.Cert
import TypeChecker.Judgment.Switch.Check
import TypeChecker.Judgment.Switch.Examples
