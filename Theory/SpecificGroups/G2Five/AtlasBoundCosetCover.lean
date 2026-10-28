module

public import Theory.SpecificGroups.G2Five.AtlasBoundCertificate.Alphabet

/-!
# Assembly of the fixed-subgroup coset cover

A certificate supplies an acyclic representative tree and actual signed
transition equations in the original ATLAS presentation. The auxiliary alphabet
and its relators are justified in `AtlasBoundCertificate.Alphabet`. Only the
original two generators need output transitions, even if auxiliary subgroup
letters occur in the trace.

The factory below isolates the remaining finite certificate from the abstract
cover argument. It assumes neither subgroup finiteness nor identification with
the permutation image. Its certificate premise must be supplied before an
unconditional `boundCosetCover` can be exported.

Source: `AtlasPresentation`, `AtlasBoundSubgroup`, and the six-rule checker in
`Theory.GroupTheory.CosetWordCertificate`.
-/

namespace G2Five.AtlasPresentation

/-- Assemble the cover once the signed transition certificate has been checked. -/
public def boundCosetCoverOfTransitions (C : BoundCosetTransitions) :
    Subgroup.GeneratorCosetCover boundSubgroup generator (Fin 3906) :=
  BoundCertificate.coverOfOriginalTransitions C.definitions C.index C.initial
    C.initial_zero C.dest C.transitions

end G2Five.AtlasPresentation
