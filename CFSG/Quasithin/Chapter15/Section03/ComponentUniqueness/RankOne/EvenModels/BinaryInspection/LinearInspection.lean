module

public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.QuotientGeometry
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.MiddleMarking
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.FourNode
public import CFSG.Quasithin.Chapter15.Section03.ComponentUniqueness.RankOne.EvenModels.BinaryInspection.LinearInspection.FiveExclusion
public import Theory.SpecificGroups.SymmetricEight.PairFlagParabolic

/-!
# Binary linear inspection in 15.3.43

The actual binary component model yields the maximal S-invariant parabolic
in I/C_I(L), and the actor retains two-core index three. In degree five the
residual and invariant flag calculation exclude every possible node. In
degree four the source involution selects the outer middle node. The genuine
exceptional comparison then gives one S₈ equivalence marking the component
intersection as the even pair stabilizer and the full local image as the
full pair stabilizer. The latter has no normal subgroup of order four,
contradicting the image of V₂.

The final exclusion has exactly the inputs of `RemainingModel.linear`;
the parabolic, node and permutation marking are all constructed here.

Source: Aschbacher--Smith, 15.3.43, printed p.1140, with 1.1.5(3)(a) and A.2.3--4.
-/

public section

open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection

variable {G : Type*} [Group G] [Finite G]
variable {Yplus S M I L V₁ V₂ : Subgroup G}
variable (c : ReducedConfiguration Yplus S M I L V₁ V₂)
include c

/-- Construct both actual permutation markings from the degree-four source data. -/
theorem middle_marking {z : G} (hz : SourceInvolution S M z)
    (hs : IsSimpleGroup L) (iso : ClassicalGroup.IsPSL L 4 2) (hi : ActsInner L z) :
    Nonempty (MiddlePermutationMarking c) := by
  have hp := quotientParabolic c hs (by decide : 0 < 4) iso
  obtain ⟨node⟩ := middle_node_of_parabolic c hz hs iso hi hp
  obtain ⟨e, b, hpair, _⟩ :=
    Theory.SpecificGroups.SymmetricEight.PairFlagParabolic.simultaneous_comparison
  exact middle_marking_of_comparison c node e b hpair

/-- The actual degree-four extension contradicts the original normal four-group. -/
theorem not_linear_four {z : G} (hz : SourceInvolution S M z)
    (hs : IsSimpleGroup L) (iso : ClassicalGroup.IsPSL L 4 2) (hi : ActsInner L z) :
    False := by
  obtain ⟨mark⟩ := middle_marking c hz hs iso hi
  exact not_middle_eight c mark.equiv mark.extended_intersection

/-- The actual degree-five maximal invariant parabolic is impossible. -/
theorem not_linear_five {z : G} (hz : SourceInvolution S M z)
    (hs : IsSimpleGroup L) (iso : ClassicalGroup.IsPSL L 5 2) (hi : ActsInner L z) :
    False := by
  exact not_linear_five_of_parabolic c hz hs iso hi
    (quotientParabolic c hs (by decide : 0 < 5) iso)

/-- Exclude exactly the binary linear inputs of `RemainingModel.linear`. -/
theorem not_linear {z : G} (hz : SourceInvolution S M z) (hs : IsSimpleGroup L)
    {d : ℕ} (hd : d = 4 ∨ d = 5) (iso : ClassicalGroup.IsPSL L d 2)
    (hi : ActsInner L z) : False := by
  rcases hd with rfl | rfl
  · exact not_linear_four c hz hs iso hi
  · exact not_linear_five c hz hs iso hi

end CFSG.Quasithin.Chapter15.Section03.RankOne.EvenModels.BinaryInspection.LinearInspection
