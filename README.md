## An Agnostic Extensional Type Theory

### Description

A parameterized extensional type theory parameterized by a choice
operator, and interpreted by a forcing interpretation parameterized by
a modality. The choice operator can for example be instantiated by
free-choice sequences or references. Modalities can be instantiated by
bar spaces, capturing standard Beth models. Parameters can be
instantiated so as to obtain either a classical or a intuitionsitic
theory.

### Compilation

Compile `all.lagda` to compile all files.

### Formalization

The formalization currently relies on function extensionality in
`forcing.lagda` to prove `↓U-uni`. It might be possible to do without.

Agda cannot figure out that `eqInType` forms an inductive type when
`□·'` is a parameter, so we make sure not to break the `Bar`
abstraction defined in `bar.lagda`, and switch between bars in
`barI.lagda`.

The formalization currently helps Agda using TERMINATION pragmas
because Agda cannot figure out on its own that functions are
terminating when they involve the modalities. We however checked that
they do and provide such an example in `props0.lagda`: see
`if-equalInType-EQ-test` (comment it out), which unfolds enough the
abstractions used in the `EQTBAR` case in `if-equalInType-EQ` for Agda
to figure out that it terminates.
