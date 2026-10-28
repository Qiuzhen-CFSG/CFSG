module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction
public import Theory.SpecificGroups.Janko4.Model.Simplicity.PrimeCoverage.Involutions.Max1Fusion
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder
public import Theory.GroupTheory.SylowElementConjugacy

/-!
# The first J₄ generator and the two-part of the model order

The checked local fusion theorem places every involution of the literal ATLAS
`max1Subgroup` in the model-conjugacy class of `a` or `(ababb)^5`. If this
subgroup has odd index, it contains a Sylow two-subgroup of the model. Sylow
conjugacy then gives the same two-class bound for every model involution.
Automorphisms preserve the order of `a`, so the two-class reduction proves
that their squares preserve its conjugacy class.

Only the odd index remains a hypothesis. The certified local order shows
that this is equivalent to `¬ 2^22 ∣ Nat.card Model`; the exact global order
and the distinction between the two involution classes are unnecessary.
Neither this two-part bound nor the unconditional square-conjugacy assertion
is proved here.

Source: GLS3, Table 5.3i, `refs/KGroup/GLS3/Chapter5(sec3-).tex`, lists the
two involution classes and the stronger result Out(J₄) = 1. The consumer is
the outer-group inspection in Aschbacher–Smith, `refs/quasithin.pdf`, printed
p.510, for the list on printed p.33. The concrete subgroup and fusion
certificates retain their ATLAS provenance in the imported modules.
-/

public section

namespace Janko4.OuterReduction

private theorem certified_local_a : Simplicity.a matrixA_mul_self = a := by
  apply toMatrix_injective
  rfl

private theorem certified_local_b : Simplicity.b matrixB_pow_four = b := by
  apply toMatrix_injective
  rfl

private theorem certified_local_word :
    Simplicity.word (Simplicity.a matrixA_mul_self) (Simplicity.b matrixB_pow_four)
      "ababb" = a * b * a * b * b := by
  rw [certified_local_a, certified_local_b]
  simp [Simplicity.word, mul_assoc]

/-- The proved local fusion gives global involution conjugacy once the
concrete local subgroup has odd index. All conjugators belong to `Model`. -/
theorem involution_isConj_of_max1_odd_index
    (hindex : ¬2 ∣ (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four).index)
    {x : Model} (hx : orderOf x = 2) :
    IsConj a x ∨ IsConj ((a * b * a * b * b) ^ 5) x := by
  let H := Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four
  let P : Sylow 2 H := Sylow.nonempty.some
  have hQ : ¬2 ∣ ((P : Subgroup H).map H.subtype).index := by
    rw [Subgroup.index_map_subtype]
    exact Nat.Prime.not_dvd_mul Fact.out P.not_dvd_index hindex
  let S : Sylow 2 Model := (P.2.map H.subtype).toSylow hQ
  obtain ⟨y, hxy⟩ := S.exists_isConj_of_orderOf_eq_prime_pow
    (hx.trans (pow_one 2).symm)
  have hy : (y : Model) ∈ H := Subgroup.map_subtype_le (P : Subgroup H) y.property
  have hyo : orderOf (y : Model) = 2 := by
    obtain ⟨c, hc⟩ := isConj_iff.mp hxy
    rw [← hc]
    exact (MulEquiv.orderOf_eq (MulAut.conj c) x).trans hx
  obtain ⟨g, hg | hg⟩ := Simplicity.max1InvolutionFusion
    matrixA_mul_self matrixB_pow_four y hy hyo
  · rw [certified_local_a] at hg
    exact Or.inl ((isConj_iff.mpr ⟨g, hg.symm⟩).symm.trans hxy.symm)
  · rw [certified_local_word] at hg
    exact Or.inr ((isConj_iff.mpr ⟨g, hg.symm⟩).symm.trans hxy.symm)

/-- Odd index is sufficient for the requested automorphism-square assertion;
no global order or separate class-invariance calculation is used. -/
theorem firstGeneratorSquareConjugacy_of_max1_odd_index
    (hindex : ¬2 ∣ (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four).index) :
    FirstGeneratorSquareConjugacy := by
  apply firstGeneratorSquareConjugacy_of_two_classes ((a * b * a * b * b) ^ 5)
  intro α
  exact involution_isConj_of_max1_odd_index hindex
    ((MulEquiv.orderOf_eq α a).trans orderOf_a)

/-- The checked local order has two-part `2^21`. Thus the precise missing
index condition requires only the corresponding upper bound for the model. -/
theorem max1_odd_index_iff_two_part_bound :
    ¬2 ∣ (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four).index ↔
      ¬2 ^ 22 ∣ Nat.card Model := by
  rw [← (Cardinality.max1Subgroup matrixA_mul_self matrixB_pow_four).card_mul_index,
    Cardinality.max1Subgroup_card]
  rw [show 2 ^ 22 = 2 ^ 21 * 2 by norm_num,
    show 501397585920 = 2 ^ 21 * 239085 by norm_num, mul_assoc,
    Nat.mul_dvd_mul_iff_left (by decide : 0 < 2 ^ 21)]
  simp only [Nat.prime_two.dvd_mul, show ¬2 ∣ 239085 by decide, false_or]

/-- The first-generator obligation follows from a two-part upper bound,
which remains an explicit input rather than a claimed order certificate. -/
theorem firstGeneratorSquareConjugacy_of_two_part_bound
    (hbound : ¬2 ^ 22 ∣ Nat.card Model) : FirstGeneratorSquareConjugacy :=
  firstGeneratorSquareConjugacy_of_max1_odd_index
    (max1_odd_index_iff_two_part_bound.mpr hbound)

end Janko4.OuterReduction
