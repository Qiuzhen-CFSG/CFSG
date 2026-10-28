module
public import Theory.GroupAction.NoncentralTwoChiefLength.Native
public section
open Subgroup
open scoped commutatorElement
namespace NoncentralChiefRefinement.CubicComparison
variable {G : Type*} [Group G] [Finite G]

/-- A normalized two-subgroup containing every cubic displacement has the same
cubic fixed index as the original two-group. -/
theorem length_eq_of_commutator_le (A Q P : Subgroup G)
    (hA : IsPGroup 3 A) (hQ : IsPGroup 2 Q)
    (hPQ : P ≤ Q) (hAQ : A ≤ normalizer (Q : Set G))
    (hAP : A ≤ normalizer (P : Set G)) [(P.subgroupOf Q).Normal]
    (hcomm : ⁅Q,A⁆ ≤ P) :
    conjugationCubicLength A P = conjugationCubicLength A Q := by
  let := quotientConjugationAction A Q P hAQ hAP
  have hz : FixedPoints.cubicLength A (Q ⧸ P.subgroupOf Q) = 0 := by
    apply FixedPoints.cubicLength_eq_zero_of_trivial
    intro a x
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (P.subgroupOf Q) x
    apply QuotientGroup.eq_iff_div_mem.mpr
    change (a : G) * (q : G) * (a : G)⁻¹ / (q : G) ∈ P
    rw [commutator_comm] at hcomm
    simpa only [commutatorElement_def, div_eq_mul_inv] using
      hcomm (commutator_mem_commutator a.property q.property)
  have he := sectionCubicLength_eq_quotient_of_twoGroup A Q P hA hQ hPQ hAQ hAP
  rw [hz] at he
  have hm := conjugationCubicLength_mono A hPQ
  unfold sectionCubicLength at he
  omega

/-- Both intersections with a common normal two-group contain all cubic
commutators when that two-group normalizes the two source overgroups. -/
theorem intersection_length_eq (A Q H : Subgroup G)
    (hA : IsPGroup 3 A) (hQ : IsPGroup 2 Q)
    (hAH : A ≤ H) (hQH : Q ≤ normalizer (H : Set G))
    (hHQ : H ≤ normalizer (Q : Set G)) :
    conjugationCubicLength A (Q ⊓ H) = conjugationCubicLength A Q := by
  have hAP : A ≤ normalizer ((Q ⊓ H : Subgroup G) : Set G) :=
    (le_inf (hAH.trans hHQ) (hAH.trans H.le_normalizer)).trans
      inf_normalizer_le_normalizer_inf
  have hQP : Q ≤ normalizer ((Q ⊓ H : Subgroup G) : Set G) :=
    (le_inf Q.le_normalizer hQH).trans
      inf_normalizer_le_normalizer_inf
  let : ((Q ⊓ H).subgroupOf Q).Normal :=
    (normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hQP
  apply length_eq_of_commutator_le A Q (Q ⊓ H) hA hQ inf_le_left
    (hAH.trans hHQ) hAP
  exact le_inf (le_normalizer_iff_commutator_le_left.mp (hAH.trans hHQ))
    ((commutator_mono le_rfl hAH).trans
      (le_normalizer_iff_commutator_le_right.mp hQH))

/-- The literal common-actor invariant for the S₃/A₄ chief-count comparison. -/
theorem intersection_lengths_eq (A Q I L : Subgroup G)
    (hA : IsPGroup 3 A) (hQ : IsPGroup 2 Q)
    (hAI : A ≤ I) (hAL : A ≤ L)
    (hQI : Q ≤ normalizer (I : Set G)) (hQL : Q ≤ normalizer (L : Set G))
    (hIQ : I ≤ normalizer (Q : Set G)) (hLQ : L ≤ normalizer (Q : Set G)) :
    conjugationCubicLength A (Q ⊓ I) = conjugationCubicLength A (Q ⊓ L) :=
  (intersection_length_eq A Q I hA hQ hAI hQI hIQ).trans
    (intersection_length_eq A Q L hA hQ hAL hQL hLQ).symm
end NoncentralChiefRefinement.CubicComparison

