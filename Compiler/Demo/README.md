# Compiler/Demo

Small examples used to keep the compiler honest.

## What Is Here

- `Direct`: direct source-to-Mixed examples.
- `Frames`: exact operational fragment and boundary classifier.
- `Entangling`: CNOT/CZ gadget lowering under the ideal-channel assumption.
- `Families`: ChainQ family codes through `cssToTypedBlock?` and `compile?`.
- `Algorithms`: ideal-source DJ/Grover/Simon programs.
- `Contract`: examples matching `Compiler/CONTRACT.md`.

## Rule

Demo files must state whether an example is exact, ideal-channel, typechecked
only, or deferred.  Do not use a simulator comparison to imply gadget-channel
correctness unless the channel is actually modeled.

## Example

The Bell-prep CNOT example typechecks with adapter capabilities, but `execMixed`
gets stuck on the gadget.  That is intentional and documented.
