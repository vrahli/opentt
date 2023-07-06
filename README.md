## An Agnostic Extensional Type Theory

### Description

A parameterized extensional type theory, parameterized by a choice
operator, and interpreted by a forcing interpretation parameterized by
a modality. The choice operator can for example be instantiated by
free-choice sequences or references. Modalities can be instantiated by
bar "spaces", capturing standard Beth models. Parameters can be
instantiated so as to obtain either a classical or a intuitionsitic
theory.

### Compilation

Compile `all.lagda` to compile all files, or simply type `make`.
It compiles with Agda version 2.6.3.

### Formalization

For a walk through what is formalized, see the file all.lagda, which
points to the main contributions.

The formalization currently relies on function extensionality in
`forcing.lagda` to prove `↓U-uni`. It might be possible to do without.

Agda cannot figure out that `eqInType` forms an inductive type when
`□·'` is a parameter, so we make sure not to break the `Bar`
abstraction defined in `bar.lagda`, and switch between bars in
`barI.lagda`.

The formalization currently helps Agda using TERMINATION pragmas
because Agda cannot figure out on its own that functions are
terminating when they involve the modalities. Therefore, the plan
(this is still work in progress) is to only make use of the induction
principles in `ind.lagda` and `ind2.lagda` (only use TERMINATING
there), and show that these can be proved for the different modalities
we have (see `indKripke.lagda`).
