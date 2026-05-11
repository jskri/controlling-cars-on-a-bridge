# Approach

The approach is to stay close to the original Event-B version. This means in
particular that modeling is not centered on dependent types.

A dependent-type-centric approach would for instance model behaviors with an
inductive type and one constructor per event (including init). Beyond the
greater translation effort, that would risk falling into the "transport hell",
i.e. the need to explicitly rewrite along type equality proofs when types are
propositionally but not definitionally equal.

Thus the models use:

- one function per event, returning an optional state (`None` is returned when
  the guard is false), instead of an inductive type

- boolean expressions (`if then else`, `<?`, etc.) instead of propositions


# Models

The refinement chain is `C2 → C1 → C0`, where `→` means "refines" and `C0` is
the most abstract model.


# Dependencies

- [Rocq](https://rocq-prover.org/releases) 9.0.1

- [Coq-hammer](https://coqhammer.github.io/) 1.3.2+9.0 (for proof automation)

Rocq and Coq-Hammer can be installed with [opam](https://opam.ocaml.org/), the
OCaml Package Manager.

- editing (optional): [VsCode](https://code.visualstudio.com/) with the
  [VsRocq](https://marketplace.visualstudio.com/items?itemName=rocq-prover.vsrocq)
  2.4.3 extension.

Note: The provided `_CoqProject` file is required by the VsRocq extension.


# Proofs verification

1. Build with [Dune](https://dune.build/):

```bash
dune build
```

2. Optionally in VsCode use VsRocq "Interpret to" commands (Alt + {RightArrow,
  End}) or "Step" commands (Alt + {UpArrow, DownArrow}) to interactively verify
  proofs.
