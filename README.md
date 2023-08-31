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

The opentt formalisation compiles with Agda version 2.6.3.

This formalisation depends on the
[logrel-mltt](https://github.com/mr-ohman/logrel-mltt) Agda formalisation of
MLTT and the agda standard-library. The standard-library should already be
available from your Agda installation. To setup
logrel-mltt for use as a library:

1. Clone the repository at <https://github.com/mr-ohman/logrel-mltt>. We have
   tested it with commit `a9a7fa1`, so if you have problems try rolling back to
   said version.

2. Add the logrel-mltt to your Agda libraries. You can do this by adding the
   following line to your agda libraries file
   ```
   LOGREL-MLTT-DIR/logrel-mltt.agda-lib
   ```
   replacing `LOGREL-MLTT-DIR` with the location of the cloned repo. For help on
   finding the location of your agda libraries file check the [Installing
   Libraries](https://my-agda.readthedocs.io/en/latest/tools/package-system.html#installing-libraries)
   subsubsection of the Agda documentation.
   
Having done this, you should now be able to compile the opentt formalisation.
Compile `all.lagda` to compile all files, or simply type `make`.

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
