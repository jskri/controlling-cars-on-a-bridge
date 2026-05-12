# Approach

The approach is to stay close to the original Event-B version. Behaviors are
inductively defined (`inductive` keyword), with the help of a `nxt` function
(`next` being a reserved keyword) for the inductive case. Integers (`int`) are
favored over natural numbers (`nat`) and ">= 0" constraints are added to
compensate: we have found proofs automation much easier this way.

Proofs were mostly found by
[Sledgehammer](https://isabelle.in.tum.de/website-Isabelle2009-1/sledgehammer.html)
and LLM.


# Models

The refinement chain is `C1 → C0`, where `→` means "refines" and `C0` is
the most abstract model. `C2` is not modeled yet.


# Dependencies

- [Isabelle](https://isabelle.in.tum.de/installation.html) 2025-2/HOL


# Proofs verification

Automatic in the official IDE; just scroll to the end of the files.
