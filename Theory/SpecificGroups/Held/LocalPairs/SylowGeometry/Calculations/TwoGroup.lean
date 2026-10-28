module

public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.Representative
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations.TwoGroup.Relations
public import Theory.GroupTheory.PGroup.GeneratorSeries
import Mathlib.Tactic.FinCases

/-!
# The fixed Held representative is a two-group

Reverse the ten short words of the retained polycyclic sequence. The checked
fourth powers make each cyclic extension a two-group; checked triangular
conjugates make the preceding subgroup normal in that extension. The four
original generators occur, up to inversion, in this sequence, and all ten
words lie in their closure. Hence the two closures are equal.

Every finite identity is certified in the degree-2058 Held carrier. No order,
simplicity, Sylow, or normalizer assumption is used.
Source: ATLAS HeG1-p2058B0 and HeG1-max3W1; GLS3 Table 5.3p motivates the
local subgroup. Retained discovery data is in `TwoGroup/Source/`.
-/

namespace Held.LocalPairs.SylowGeometry.Calculations
namespace TwoGroup

private theorem conjugateWord_lt : ∀ (k j t : Fin 10),
    t ∈ conjugateWord k j → t.val < k.val := by decide +kernel

/-- Each word normalizes the closure of the preceding words. -/
public theorem pcGenerator_normalizes_prefix (k : Fin 10) :
    pcGenerator k ∈ Subgroup.normalizer
      (Subgroup.generatorPrefix pcGenerator k.val : Set He) := by
  unfold Subgroup.generatorPrefix
  apply Subgroup.mem_normalizer_closure_of_conjugates
  rintro _ ⟨j, hj, rfl⟩
  rw [pcGenerator_conjugate k j hj]
  apply Subgroup.list_prod_mem
  intro x hx
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
  exact Subgroup.subset_closure ⟨t, conjugateWord_lt k j t ht, rfl⟩

/-- The short words generate precisely the original four-word closure. -/
public theorem pcClosure_eq_representative :
    Subgroup.closure (Set.range pcGenerator) = representative := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    fin_cases i <;> change _ ∈ representative
    · exact (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.inv_mem (generator_mem 2)) (generator_mem 1)) (generator_mem 0)) (generator_mem 1)) (generator_mem 2)) (representative.inv_mem (generator_mem 1))) (representative.inv_mem (generator_mem 0))) (representative.inv_mem (generator_mem 1)))
    · exact (representative.inv_mem (generator_mem 0))
    · exact (representative.mul_mem (representative.mul_mem (representative.inv_mem (generator_mem 3)) (representative.inv_mem (generator_mem 3))) (representative.inv_mem (generator_mem 0)))
    · exact (representative.mul_mem (representative.mul_mem (representative.inv_mem (generator_mem 1)) (representative.inv_mem (generator_mem 0))) (representative.inv_mem (generator_mem 1)))
    · exact (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.inv_mem (generator_mem 3)) (generator_mem 1)) (generator_mem 0)) (generator_mem 1)) (generator_mem 3))
    · exact (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.mul_mem (representative.inv_mem (generator_mem 2)) (representative.inv_mem (generator_mem 3))) (representative.inv_mem (generator_mem 0))) (generator_mem 1)) (generator_mem 0)) (generator_mem 1)) (representative.inv_mem (generator_mem 3))) (representative.inv_mem (generator_mem 1))) (representative.inv_mem (generator_mem 0))) (representative.inv_mem (generator_mem 2))) (representative.inv_mem (generator_mem 1)))
    · exact (representative.inv_mem (generator_mem 1))
    · exact (representative.mul_mem (representative.mul_mem (representative.inv_mem (generator_mem 3)) (generator_mem 1)) (generator_mem 3))
    · exact (representative.inv_mem (generator_mem 2))
    · exact (generator_mem 3)
  · apply (Subgroup.closure_le _).mpr
    rintro _ ⟨i, rfl⟩
    have hm (j : Fin 10) : pcGenerator j ∈ Subgroup.closure (Set.range pcGenerator) :=
      Subgroup.subset_closure (Set.mem_range_self j)
    fin_cases i
    · change generator 0 ∈ Subgroup.closure (Set.range pcGenerator)
      have h := (Subgroup.closure (Set.range pcGenerator)).inv_mem (hm 1)
      change ((generator 0)⁻¹)⁻¹ ∈ Subgroup.closure (Set.range pcGenerator) at h
      rw [inv_inv] at h
      exact h
    · change generator 1 ∈ Subgroup.closure (Set.range pcGenerator)
      have h := (Subgroup.closure (Set.range pcGenerator)).inv_mem (hm 6)
      change ((generator 1)⁻¹)⁻¹ ∈ Subgroup.closure (Set.range pcGenerator) at h
      rw [inv_inv] at h
      exact h
    · change generator 2 ∈ Subgroup.closure (Set.range pcGenerator)
      have h := (Subgroup.closure (Set.range pcGenerator)).inv_mem (hm 8)
      change ((generator 2)⁻¹)⁻¹ ∈ Subgroup.closure (Set.range pcGenerator) at h
      rw [inv_inv] at h
      exact h
    · exact hm 9

end TwoGroup

/-- The closure of the four published literal Held words is a two-group. -/
public theorem representative_isPGroup : IsPGroup 2 representative := by
  rw [← TwoGroup.pcClosure_eq_representative]
  exact Subgroup.isPGroup_closure_of_normalizing_generators TwoGroup.pcGenerator
    (fun i => ⟨2, TwoGroup.pcGenerator_pow_four i⟩)
    TwoGroup.pcGenerator_normalizes_prefix

end Held.LocalPairs.SylowGeometry.Calculations
