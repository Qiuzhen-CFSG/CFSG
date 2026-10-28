module

public import Theory.SpecificGroups.Held.TwoRank.Coloring
public import Theory.SpecificGroups.Held.LocalPairs.SylowGeometry.Calculations
public import Theory.GroupTheory.PrimeRankSylow

/-!
# Transport of the Held extension rank to the full normalizer

Held's certified Sylow subgroup is self-normalizing. Under the independent
bound of two on the full permutation-normalizer quotient, its normalizer
is a Sylow subgroup of the full permutation normalizer. The concrete outside
element lies in this subgroup, and the two cosets exhaust it. The checked
coloring therefore gives rank six, including for elementary subgroups
meeting the outside coset.

The full-normalizer quotient bound remains an explicit producer premise;
no selected extension is identified with the full normalizer without it.
Source: Aschbacher--Smith, G.7.3(2), printed p.348, and the actual degree-2058
Held Sylow calculations.
-/

public section
namespace Held.TwoRank
open Subgroup LocalPairs LocalPairs.SylowGeometry
open LocalPairs.SylowGeometry.Calculations

/-- The outside element normalizes the literal embedded Held Sylow subgroup. -/
theorem outside_mem_normalizer : outside ∈ normalizer (innerSylow : Set PermutationNormalizer) := by
  have hi : outside⁻¹ ∈ normalizer (innerSylow : Set PermutationNormalizer) := by
    rw [mem_normalizer_iff_map_conj_eq]
    apply eq_of_le_of_card_ge
    · apply map_le_iff_le_comap.mpr
      intro k hk
      change outside⁻¹ * k * (outside⁻¹)⁻¹ ∈ innerSylow
      rw [inv_inv]
      exact outside_inverse_conjugates k hk
    · exact (Nat.card_congr ((MulAut.conj outside⁻¹).subgroupMap innerSylow).toEquiv).le
  simpa only [inv_inv] using (normalizer (innerSylow : Set PermutationNormalizer)).inv_mem hi

private theorem inner_of_normalizes (x : PermutationNormalizer)
    (hx : x ∈ normalizer (innerSylow : Set PermutationNormalizer))
    (hi : x ∈ innerSubgroup) : x ∈ innerSylow := by
  have hi' : x ∈ innerEmbedding.range := innerEmbedding_range.symm ▸ hi
  obtain ⟨g, rfl⟩ := hi'
  have hg : g ∈ (normalizer (innerSylow : Set PermutationNormalizer)).comap innerEmbedding := hx
  rw [innerSylow, normalizer_comap_inner, InnerNormalizer.normalizer_eq] at hg
  exact mem_map_of_mem innerEmbedding hg

/-- Under the full quotient bound, these two cosets are the entire Sylow normalizer. -/
theorem extendedSylow_eq_normalizer
    (hb : Nat.card PermutationNormalizerQuotient ≤ 2) :
    extendedSylow = normalizer (innerSylow : Set PermutationNormalizer) := by
  have hi : innerSubgroup.index = 2 := by
    have hne : innerSubgroup.index ≠ 1 := by
      intro h
      apply outside_not_inner
      rw [index_eq_one.mp h]
      exact mem_top _
    have hpos : 0 < innerSubgroup.index := Nat.card_pos (α := PermutationNormalizerQuotient)
    change innerSubgroup.index ≤ 2 at hb
    omega
  apply le_antisymm
  · intro x hx
    rcases hx with hx | ⟨k, hk, rfl⟩
    · exact innerSylow.le_normalizer hx
    · exact mul_mem outside_mem_normalizer (innerSylow.le_normalizer hk)
  · intro x hx
    by_cases hin : x ∈ innerSubgroup
    · exact Or.inl (inner_of_normalizes x hx hin)
    · have hin' : outside⁻¹ * x ∈ innerSubgroup := by
        rw [innerSubgroup.mul_mem_iff_of_index_two hi, inv_mem_iff]
        simp only [outside_not_inner, hin]
      have hn' : outside⁻¹ * x ∈ normalizer (innerSylow : Set PermutationNormalizer) :=
        mul_mem (inv_mem outside_mem_normalizer) hx
      exact Or.inr ⟨outside⁻¹ * x, inner_of_normalizes _ hn' hin', by simp⟩

/-- The full permutation normalizer has two-rank at most six once its relative
quotient by Held has order at most two. The extension rank is discharged. -/
theorem normalizer_twoRank_le_six
    (hb : Nat.card PermutationNormalizerQuotient ≤ 2) :
    primeRank 2 PermutationNormalizer ≤ 6 := by
  obtain ⟨S, hS⟩ := exists_representative_sylow representative_isPGroup InnerNormalizer.normalizer_eq
  obtain ⟨T, hT, _⟩ := exists_normalizer_sylow_of_self_normalizing hb S
    (by change normalizer (S.toSubgroup : Set He) = S.toSubgroup; rw [hS]; exact InnerNormalizer.normalizer_eq)
  have hT' : T.toSubgroup = extendedSylow := by
    rw [hT, hS]
    exact (extendedSylow_eq_normalizer hb).symm
  rw [T.primeRank_eq]
  change primeRank 2 T.toSubgroup ≤ 6
  rw [hT']
  exact extendedSylow_twoRank_le_six

end Held.TwoRank
