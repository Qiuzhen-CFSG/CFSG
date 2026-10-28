module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.LargeCenterRadicals.Reductions
public import Theory.GroupTheory.MaximalTwoLocalOvergroups

/-!
# The maximal-local reduction for large-center radicals

Every nontrivial native radical has a maximal two-local overgroup containing
its full normalizer.  The certified max2 and max4 center bounds then remove
those two local branches from this overgroup.  This is the exact reduction
needed before the remaining Mathieu, linear-five and alternating rows can be
handled by the native cover; it does not identify a maximal two-local by an
ambient coatom argument.

Source: An--O'Brien--Wilson (2003), Section 4, p.122, together with
Kleidman--Wilson (1988), Section 2, and the native center bounds in
`CoreOvergroupCenter`.
-/

public section
open Subgroup Theory.GroupTheory
namespace Janko4.LocalStructure.LargeCenterRadicals

open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData

/-- A large-center radical lies in a maximal two-local overgroup of its whole
normalizer, and that overgroup is neither the native max2 nor native max4
branch. -/
theorem exists_maximal_overgroup_not_small
    (P : Subgroup Model) (hP : IsPRadical 2 P)
    (hlarge : 64 ≤ Nat.card (center P)) :
    ∃ M : Subgroup Model, IsMaximalTwoLocal M ∧
      normalizer (P : Set Model) ≤ M ∧
      ¬ Nonempty (M ≃* sourceSubgroup) ∧
      ¬ Nonempty (M ≃* SymmetricLinear.max4Subgroup) := by
  have hlocal : IsTwoLocal (normalizer (P : Set Model)) :=
    ⟨P, hP.1, hP.isPGroup, rfl⟩
  obtain ⟨M, hNM, hM⟩ := Finite.exists_le_maximal hlocal
  refine ⟨M, hM, hNM, ?_, ?_⟩
  · rintro ⟨e⟩
    exact normalizer_not_le_max2 P M hP hlarge e hNM
  · rintro ⟨e⟩
    exact normalizer_not_le_max4 P M hP hlarge e hNM

end Janko4.LocalStructure.LargeCenterRadicals
