# Controlling cars on a bridge

Models of controlling cars on a one-way bridge between the mainland and an
island.

This example is interesting because it solves the problem using a top-down
approach, introducing a succession of increasingly refined models. Each refined
model introduces new details, which keeps the modelling task manageable. All
invariants and refinements are formally proved.

The [original models](https://www.event-b.org/A_ch2.pdf) use the Event-B
formalism. We adapt them here to
[TLA+](https://lamport.azurewebsites.net/tla/tla.html), whose syntax and
semantics are very similar, and to [Isabelle](https://isabelle.in.tum.de/),
which diverges more significantly.

For now, the TLA+ models go up to the second refinement, while the Isabelle
models go up to the first.

The TLA+ models require the [TLA+ proof
manager](https://github.com/tlaplus/tlapm) version 1.5.0.

The Isabelle models have been tested with
[Isabelle2025-2/HOL](https://isabelle.in.tum.de/installation.html).
