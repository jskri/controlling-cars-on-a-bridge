# Approach

The approach is to stay close to the original Event-B version, which is natural
since the syntax and semantics of the two languages are very similar.


# Models

The refinement chain is `C2 → C1 → C0`, where `→` means "refines" and `C0` is
the most abstract model.


# Dependencies

- [TLA+ proof manager
  1.5.0](https://github.com/tlaplus/tlapm/releases/tag/202210041448)

- editing (optional): The [TLA+ Toolbox
  1.7.4](https://github.com/tlaplus/tlaplus/releases/tag/v1.7.4)


# Proofs verification

In the TLA+ Toolbox, to verify the whole file, right-click outside a proof and
select `TLA Proof Manager > Prove Step or Module`. Alternatively, press
`<Ctrl-g><Ctrl-g>` outside a proof. To verify a specific proof step, place the
cursor on it and proceed in the same way.
