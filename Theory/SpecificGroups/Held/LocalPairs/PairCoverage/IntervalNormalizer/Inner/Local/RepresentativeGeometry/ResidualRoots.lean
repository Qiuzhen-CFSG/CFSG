module

public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.Orbits
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Structure
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Images
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair00
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair01
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair10
public import Theory.SpecificGroups.Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.Local.RepresentativeGeometry.ResidualRoots.Pair11

/-!
# Two root images in the actual Held residual core

For each literal pair K = R ∨ T, eight explicit words generate a normal
two-subgroup contained in O²(K). Their fourth powers and conjugations are
checked in the fixed faithful Held representation. Maximality of the
intrinsic O₂(O²(K)) puts these words in the exact embedded residual core.
Their images in the marked six-point action give both specified double
transpositions, including the outer S₆ twist used for the second pair.

This argument needs neither the native action kernel nor an order certificate
for T, and makes no identification of subgroups from their orders.
Sources: GLS3 Table 5.3p; unchanged ATLAS degree-2058 and max3/max4 words;
the additional Held calculation for quasithin printed pp.509–511 and 747–748.
-/

public section
open Subgroup
namespace Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry
open ResidualRoots

/-- The concrete word subgroup lies in the two-core of the actual residual. -/
theorem residualWordGroup_le_pairTwoCore (i : Bool) (j : Fin 2) :
    ResidualRoots.group i j ≤ pairTwoCore i j := by
  apply group_le_pairTwoCore_of_relations
  · cases i <;> fin_cases j
    · exact Pair00.fourth
    · exact Pair01.fourth
    · exact Pair10.fourth
    · exact Pair11.fourth
  · cases i <;> fin_cases j
    · exact Pair00.internal
    · exact Pair01.internal
    · exact Pair10.internal
    · exact Pair11.internal
  · cases i <;> fin_cases j
    · exact Pair00.conjugate
    · exact Pair01.conjugate
    · exact Pair10.conjugate
    · exact Pair11.conjugate

private theorem generatorImage_mem (i : Bool) (j : Fin 2) (k : Fin 8) :
    generatorImage i j k ∈ ((pairTwoCore i j).subgroupOf (localOvergroup i)).map (action i j) := by
  refine ⟨liftGenerator i j k, ?_, action_liftGenerator i j k⟩
  change (liftGenerator i j k : Held.He) ∈ pairTwoCore i j
  rw [liftGenerator_val]
  exact residualWordGroup_le_pairTwoCore i j (subset_closure (Set.mem_range_self k))

/-- First required double transposition, unconditionally for all four pairs. -/
theorem rootOne_mem_pairTwoCore_image (i : Bool) (j : Fin 2) :
    rootOne i j ∈ ((pairTwoCore i j).subgroupOf (localOvergroup i)).map (action i j) := by
  rw [← rootOne_product]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  exact generatorImage_mem i j k

/-- Second required double transposition, unconditionally for all four pairs. -/
theorem rootTwo_mem_pairTwoCore_image (i : Bool) (j : Fin 2) :
    rootTwo i j ∈ ((pairTwoCore i j).subgroupOf (localOvergroup i)).map (action i j) := by
  rw [← rootTwo_product]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hx
  exact generatorImage_mem i j k

end Held.LocalPairs.PairCoverage.IntervalNormalizer.Inner.RepresentativeGeometry
