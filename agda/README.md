# Agda code for a generalized Cartesian Cubical Type Theory

To typecheck everything run:
```
> make
```

This assumes that Agda version >=2.6.0 is installed.


Contents
--------

- ABCFHL: Equivalence between weak fibrations and ABCFHL fibrations
  when the diagonal on I is a cofibration.

- CCHM: Equivalence with weak fibrations and CCHM fibrations in the
  presence of a connection algebra structure.

- cofprop: Definition of the universe of cofibrant propositions and
  basic operations on these.

- cofreplacement: Cofibrant replacement and definition of (trivial)
  cofibrations.

- Data/functions: Fibrancy of Π-types.

- Data/id: CCHM style identity types.

- Data/id2:

- Data/id3:

- Data/inductive-fiber:

- Data/nat: The type of natural numbers is fibrant.

- Data/paths: Fibrancy of Path types.

- Data/products: Fibrancy of Σ-types.

- equivs: Definitions of contractible, extensible (SContr), fibers,
equivalences and quasi-invertible maps.

- equivscontrfib: Equivalent definition of isFib due to Dan Licata.

- everything: File that imports all of the other files.

- fiberwise-total:

- fibrations: Definition of weak composition and fibrations. Proof
that they are closed under isomorphism and that weak composition can
be strictified.

- fibreplacement:

- glueing: Import the files related to Glue types (equivalence
  extension types).

- glueing/aligned: Realigning strict Glue types.

- glueing/core: Definition of (weak) Glue types and their (unaligned)
  fibrancy.

- glueing/strict: Strict Glue types.

- hcomp-coe: Definition of weak homogeneous composition and
coercion. Proof that these imply weak composition.

- interval: Definition of the interval and Path types.

- prelude: Basics.

- pushout: Axiomatization of pushouts.

- realignment: Realign a fibration structure.

- retract:

- strictness-axioms: Axioms related to strictifying Glue types.

- trivialfib: Definition of trivial fibrations and proof that they are
actually fibrations.

- univalence: Proof of univalence in the form of ua and uaβ.

- wtypesred: W-types with reductions.
