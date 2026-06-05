# Controlling cars on a bridge

Models of controlling cars on a one-way bridge between the mainland and an
island in:

- Event-B

- TLA+

- Coq / Rocq

- Isabelle

This example is interesting because it solves the problem using a top-down
approach, introducing a succession of increasingly refined models. Each refined
model introduces new details, which keeps the modeling task manageable. All
invariants and refinements are formally proved.

The [original
models](https://web-archive.southampton.ac.uk/deploy-eprints.ecs.soton.ac.uk/112/1/sld.ch2.car.pdf)
use the Event-B formalism. We adapt them here to:

- [TLA+](https://lamport.azurewebsites.net/tla/tla.html), whose syntax and
semantics are very similar

- [Coq / Rocq](https://rocq-prover.org/), which diverges more significantly

- [Isabelle](https://isabelle.in.tum.de/) (idem)

The Event-B models feature all the three refinements. For now, the TLA+ and Rocq
models go up to the second refinement, while the Isabelle models go up to the
first.

See READMEs in the respective subdirectories.


# Requirements

The proofs have been successfully verified with:

## Event-B

- [Rodin 3.9
  platform](https://sourceforge.net/projects/rodin-b-sharp/files/Core_Rodin_Platform/3.9/)
  with the following plugins (in Rodin, `Help > Install New Software`):

  + Atelier B provers 2.4.1

  + SMT Solvers 1.5.0

  + editing (optional): Camille Text Editor 3.6.0

## TLA+

- [TLA+ proof manager
  1.5.0](https://github.com/tlaplus/tlapm/releases/tag/202210041448)

- editing (optional): The [TLA+ Toolbox
  1.7.4](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.4)

Note: An alternative editor I have not tested is
[VsCode](https://code.visualstudio.com/) with the [TLA+ (Temporal Logic of
Actions)](https://marketplace.visualstudio.com/items?itemName=tlaplus.vscode-ide)
extension.

## Rocq

- [Rocq](https://rocq-prover.org/releases) 9.0.1

- [Coq-hammer](https://coqhammer.github.io/) 1.3.2+9.0 (for proof automation)

- editing (optional): [VsCode](https://code.visualstudio.com/) with the
  [VsRocq](https://marketplace.visualstudio.com/items?itemName=rocq-prover.vsrocq)
  2.4.3 extension.

## Isabelle

- [Isabelle](https://isabelle.in.tum.de/installation.html) 2025-2/HOL
