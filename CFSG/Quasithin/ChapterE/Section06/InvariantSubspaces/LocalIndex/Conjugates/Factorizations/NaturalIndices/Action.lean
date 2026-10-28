module

public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Action.AlternatingThree
public import CFSG.Quasithin.ChapterE.Section06.InvariantSubspaces.LocalIndex.Conjugates.Factorizations.NaturalIndices.Action.Internal

/-!
# Natural Baumann action coordinates

The A₃ contract is proved by `alternatingThreeCoordinatesInput`: a nontrivial
two-group action on its actual elementary module of order four becomes the
binary shear action. The source's trivial-central-layer hypothesis is retained.

The linear branch remains open. `LinearInternalSylowInput` isolates the source
application of B.6.9–10, and `LinearSylowCoordinatesInput` isolates the independent
natural-module coordinate construction. `linearCoordinatesInput_of_internalSylow`
assembles them only after both inputs are supplied. The actual block quotient
projection and its literal internal-conjugation formula are already proved.

Source: Aschbacher–Smith, combined manuscript (1 March 2004), C.5.4(2),(4),
printed p.155, and C.5.6 (*), printed p.156.
-/
