module

public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.Contracts
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.OrbitTools
public import Theory.SpecificGroups.Held.Automorphisms.Realization.MarkedConjugacy.NormalizedPairs.ClassA.Checking

/-!
# From the first-class row certificate to the actual conjugacy class

The generator-closed family of actual Held words contains every conjugate
of `a`. The point evaluator supplies exactly the four base images and the
relator or fixed-point witnesses consumed by `OrbitTools`.
Source: `Held/Model/Source/HeG1-P1.M`, including its literal marked subgroup.
-/

namespace Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA

/-- Application of all checked rows to the entire actual conjugacy class. -/
public theorem classCalculation_of_facts (h : ∀ i, facts i) : ClassCalculation a := by
  apply classCalculation_of_four_point_checks family a
  · exact ⟨0, fun _ => rfl⟩
  · intro i
    exact ⟨index (data i.val).2.1, (edgeTest_sound _ _ _ (h i).1).1⟩
  · intro i
    exact ⟨index (data i.val).2.2.1, (edgeTest_sound _ _ _ (h i).1).2⟩
  · intro k hk i
    rcases hk with rfl | rfl
    · exact rowTest_sound _ _ _ _ (h i).2.1
    · exact rowTest_sound _ _ _ _ (h i).2.2

end Held.Realization.MarkedConjugacy.NormalizedPairs.ClassA
