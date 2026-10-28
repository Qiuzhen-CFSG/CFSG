module

public import CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.WeakClosure.ActionImage
public import CFSG.Quasithin.ChapterH.Section05To09.NaturalDual.SourceSetup

/-!
# The compatible H.9 action input for the doubled orbit

The source group is the actual ambient automizer of W, its representation
is the conjugation representation, and both summands are the original branch
summands. This interface lets the geometric implications proceed independently
of construction of the compatible model. In particular, it is not asserted
that the abstract automizer-group isomorphism alone supplies these fields.
The construction is a separate obligation of the weak-closure assembly.

Source: Aschbacher--Smith, H.9 setup and 12.1, pp.389,788--794.
-/

public noncomputable section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
variable {G : Type*} [Group G] {T : Sylow 2 G} {L V : Subgroup G} {n : ℕ}
  (B : DoubledBranch T L V n)
  [IsElementaryAbelian 2 (componentOrbit V (T : Subgroup G))]

/-- Compatibility requirements for using H.9 on the literal doubled orbit.
No offender or weak-closure conclusion is part of this input. -/
structure MarkedAutomizerModel where
  setup : ChapterH.NaturalDual.SourceSetup n
    (ChapterE.Automizer (componentOrbit V (T : Subgroup G)))
    (Additive (componentOrbit V (T : Subgroup G)))
  representation_eq : setup.representation = ChapterE.automizerRepresentation
    (componentOrbit V (T : Subgroup G))
  natural_eq : setup.natural = B.naturalSpace
  dual_eq : setup.dual = B.dualSpace

end CFSG.Quasithin.Chapter12.Section01.DoubleNaturalSource.DoubledBranch
