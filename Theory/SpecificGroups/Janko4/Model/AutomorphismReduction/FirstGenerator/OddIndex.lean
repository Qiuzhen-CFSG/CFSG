module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.SylowCandidate
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FirstGenerator.OddIndex.CentralizerSylow

/-!
# Odd index of the literal ATLAS max1 subgroup of J₄

The fixed subgroup `twoSubgroup` has certified order 2²¹ and odd relative
index 239085 in the literal ATLAS `max1Subgroup`. Sylow's normalizer-index
congruence shows that the latter subgroup has odd ambient index exactly when
the relative index of `twoSubgroup` in its ambient normalizer is odd.
In particular, containment of this normalizer in `max1Subgroup` suffices.

The unconditional theorem follows separately from the full involution
centralizer: `OddIndex.CentralizerSylow` proves that every ambient Sylow
two-subgroup has order 2²¹. The certified max1 order then forces its index
to be odd. The conditional normalizer reductions remain available for the
fixed fifteen-generator subgroup. No simplicity, perfectness, full group
order, or automorphism-table result is assumed.

Source: GLS3 Table 5.3i, `refs/KGroup/GLS3/Chapter5(sec3-).tex`, gives the
two-part 2²¹. The matrix and local-word provenance is retained in
`Cardinality.Subgroup` and `OddIndex.SylowCandidate`.
-/

public section

namespace Janko4.OuterReduction.OddIndex

open Cardinality

/-- The index of a p-subgroup and its relative normalizer index are congruent
modulo p. The certified odd local index transfers that criterion to `max1`. -/
theorem max1_odd_index_iff_normalizer_relIndex :
    ¬2 ∣ (max1Subgroup matrixA_mul_self matrixB_pow_four).index ↔
      ¬2 ∣ twoSubgroup.relIndex (Subgroup.normalizer (twoSubgroup : Set Model)) := by
  have hcongr := Sylow.card_quotient_normalizer_modEq_card_quotient twoSubgroup_card
  have hdiv : 2 ∣ twoSubgroup.relIndex (Subgroup.normalizer (twoSubgroup : Set Model)) ↔
      2 ∣ twoSubgroup.index := hcongr.dvd_iff dvd_rfl
  have hi := Subgroup.relIndex_mul_index twoSubgroup_le
  rw [twoSubgroup_relIndex] at hi
  rw [hdiv, ← hi]
  simp only [Nat.prime_two.dvd_mul, show ¬2 ∣ 239085 by decide, false_or]

/-- Ambient normalizer containment suffices. This is a conditional reduction;
the containment must be established in the actual matrix model. -/
theorem max1_odd_index_of_normalizer_le
    (hN : (Subgroup.normalizer (twoSubgroup : Set Model)) ≤ max1Subgroup matrixA_mul_self matrixB_pow_four) :
    ¬2 ∣ (max1Subgroup matrixA_mul_self matrixB_pow_four).index := by
  apply max1_odd_index_iff_normalizer_relIndex.mpr
  intro h
  have hd : twoSubgroup.relIndex (Subgroup.normalizer (twoSubgroup : Set Model)) ∣
      twoSubgroup.relIndex (max1Subgroup matrixA_mul_self matrixB_pow_four) :=
    dvd_of_mul_right_eq _ (Subgroup.relIndex_mul_relIndex _ _ _
      twoSubgroup.le_normalizer hN)
  rw [twoSubgroup_relIndex] at hd
  exact (by decide : ¬2 ∣ 239085) (h.trans hd)

end Janko4.OuterReduction.OddIndex

namespace Janko4.OuterReduction

/-- The literal ATLAS max1 subgroup has odd ambient index. This follows from
the certified local centralizer and max1 orders, without assuming simplicity. -/
theorem max1_odd_index :
    ¬2 ∣ (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four).index := by
  intro h
  apply OddIndex.model_two_part_bound
  rw [← (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four).card_mul_index,
    Cardinality.max1Subgroup_card]
  obtain ⟨k, hk⟩ := h
  rw [hk]
  exact ⟨239085 * k, by ring⟩

/-- An explicit unconditional export for consumers that do not assume the
matrix model is simple or perfect. -/
theorem max1_odd_index_unconditional :
    ¬2 ∣ (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four).index :=
  max1_odd_index

end Janko4.OuterReduction
