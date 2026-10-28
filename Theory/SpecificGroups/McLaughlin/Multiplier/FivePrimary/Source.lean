module

public import Theory.SpecificGroups.McLaughlin.Multiplier.FivePrimary
public import Theory.SpecificGroups.McLaughlin.Multiplier

/-!
# The McLaughlin odd-center input to A.2.19

For the original finite quasisimple group, compose the given isomorphism
from its central quotient to the permutation carrier with the specified
model comparison. The resulting perfect central cover has kernel exactly
the original center. Prime support and the proved five-primary exclusion
then make every nontrivial odd-primary center a three-group.

This discharges precisely the McL three-primary-center input used by
Aschbacher–Smith A.2.19, printed pp.40–41 (PDF pp.51–52). The final source
assembly owner is `qt-a02-sporadic`; its other cases and local-rank argument
are separate. This result does not assert that the center has order three
or require the unfinished two/three-primary bounds or triple-cover lower
bound. The independent carrier-comparison owner supplies the sole model
premise retained here.
-/

namespace Theory.SpecificGroups.McLaughlin.Multiplier
open Sporadic.LeechRelated.McL Atlas.Sporadic.McLaughlin
open Theory.GroupTheory Subgroup

/-- The literal A.2.19 McL application, retaining the original quotient and center. -/
public theorem source_center_isThreeGroup
    (comparison : Carrier ≃* Model)
    {G : Type*} [Group G] [Finite G] [IsQuasisimple G]
    (e : G ⧸ center G ≃* Carrier) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : IsPGroup p (center G)) (hne : center G ≠ ⊥) :
    IsPGroup 3 (center G) := by
  exact source_center_isThreeGroup_of_not_five_dvd (e.trans comparison)
    hp hp2 hZ hne
    (not_five_dvd_card_kernel comparison (sourceCover (e.trans comparison)))

end Theory.SpecificGroups.McLaughlin.Multiplier
