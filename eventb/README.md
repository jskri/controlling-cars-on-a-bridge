# File tree

The model files are stored in an XML format and can be conveniently edited only
through the Rodin IDE. For the sake of accessibility for newcomers, plain text
versions are provided, but are not authoritative.

```
.
├── rodin/ # Rodin project
└── txt/   # text versions of machines and contexts
```


# Presentation

Event-B models are decomposed into "machines" and "contexts". A context contains
constants, carrier sets (abstract sets), and axioms for a machine. A machine is
a state machine with possibly:

- a state, given by a set of variables (`variable` clause). Note: the Camille
  syntax variant is used here.

- an initial "event" (`INITIALISATION`), setting the values of variables in the
  initial state.

- events, each one describing a transition from the current state to new
  states.

    + to trigger, an event may require a condition, called a "guard", to hold
      (`where` clause).

    + the new states are given by the `then` clause. Unmentioned variables are
      unchanged.

    + an event may be "convergent", in which case it must decrease a so-called
      variant (see below).

- invariants, which must hold in the initial state, and in the new state of each
  event assuming the invariant held before the event. POs are automatically
  generated.

- optionally theorems, which must be proved from axioms and invariants, but
  unlike invariants, they do not generate a preservation PO for each event.

- optionally a variant, which is a natural number expression that all convergent
  events must decrease.

A machine can refine another one. Intuitively, this means it implements the
other machine. Then an event of the refining machine can refine an event from
the refined machine. This will automatically generate specific POs.

The point of variants is to make sure any event introduced in a refining machine
that does not refine an abstract event is convergent (since it has no abstract
counterpart to justify its existence).


# Models

The refinement chain is `C3 → C2 → C1 → C0`, where `→` means "refines" and `C0`
is the most abstract model.


# Dependencies

- [Rodin 3.9
  platform](https://sourceforge.net/projects/rodin-b-sharp/files/Core_Rodin_Platform/3.9/)
  with the following plugins (in Rodin, `Help > Install New Software`):

  + Atelier B provers 2.4.1

  + SMT Solvers 1.5.0

  + editing (optional): Camille Text Editor 3.6.0


# Import

To import the project in Rodin go to `File > Import > Existing Projects into
Workspace`, then set the `rodin/` directory as the root directory.


# Proof verification

In Rodin, go to the `Event-B Explorer` panel, unfold `C0` (and similarly for
`C1`, `C2` and `C3`), then `Proof obligations`. All proof obligations (POs)
should be discharged, i.e. proved (green).

When working on a model, POs are automatically generated, then discharged if
possible. To manually relaunch provers, right-click on `Proof obligations`, then
`Retry Auto Provers`.

When the automatic provers fail to discharge a PO, it must be manually handled:
double-click on the PO and switch to the `Proving` perspective. In particular,
you will see a selection of hypotheses, the goal and the proof tree. More
hypotheses can be added through the `Search Hypothesis` panel.


# Proof hints

- Transform hypotheses and goal. In the hypotheses and goal panels, some parts
  of the formulas may be red (typically connectors): hovering over them shows a
  menu with possible logical transformations.

- Add a hypothesis. Write a new hypothesis in the `Proof Control` panel, then
  click the `Add Hypothesis` button (`ah`). This generates three POs: one for
  well-formedness, one for the new hypothesis, and one for the current PO with
  the new hypothesis. Click the `Run auto provers` button (the green robot) to
  discharge the well-formedness PO. The other two POs may be discharged in the
  same way, if they are simple enough.

- Reason by cases. Write a new hypothesis in the `Proof Control` panel, then
  click the `Case distinction` button (`dc`). This generates three POs: one for
  well-formedness, one for the current PO with the new hypothesis, and one for
  the current PO with the negation of the new hypothesis.

- Backtrack from a dead end. In the `Proof Control` panel, click the `Backtrack
  from the current node` button. It is also possible to directly prune the proof
  tree: in the `Proof Tree` panel, right-click on a node, then `Prune`.

- Brute-force. In the `Search Hypothesis` panel, click the `Refresh` button,
  click the `Select all searched hypotheses` button, then the `Select
  hypotheses` button. This will add all selected hypotheses to the `Selected
  Hypothesis` panel. Then in the `Proof Control` panel, click the `SMT` button
  (requires the `SMT solvers` plugin) then `All enabled SMT`.
