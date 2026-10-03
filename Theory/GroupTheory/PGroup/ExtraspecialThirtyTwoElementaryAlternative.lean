module

public import Theory.GroupTheory.PGroup.ExtraspecialSmallOrder

/-!
# Elementary subgroups in an extraspecial group of order thirty-two

The commutator pairing bounds every elementary subgroup by eight. Adjoining
the center preserves elementary abelianness, so an elementary subgroup of
order eight contains the center and is normal in the extraspecial group.
Consequently either every elementary subgroup has order below eight or there
is a normal elementary eight containing the center.

This is an intrinsic alternative: normality here is only in the extraspecial
group, not in an overgroup. It supplies the two core branches in
Janko–Thompson (1970), §4, printed pp.389–392.
-/

open Subgroup

namespace IsExtraspecial

variable {P : Type*} [Group P] [Finite P] [IsExtraspecial 2 P]

/-- Every elementary subgroup of an extraspecial group of order 32 has order
at most eight, whether or not it initially contains the center. -/
public theorem elementary_card_le_eight_of_card_thirty_two
    (hP : Nat.card P = 32) (E : Subgroup P) [IsElementaryAbelian 2 E] :
    Nat.card E ≤ 8 := by
  let : IsElementaryAbelian 2 (center P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      simpa only [center_order_p 2 P] using (pow_card_eq_one' (x := z)) }
  let : IsElementaryAbelian 2 (E ⊔ center P : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer (center_le_centralizer _)
  have hsq := extraspecial_two_elementary_card_sq_le (E ⊔ center P) le_sup_right
  have hle := card_le_of_le (show E ≤ E ⊔ center P from le_sup_left)
  rw [hP] at hsq
  nlinarith

/-- An elementary eight contains the center and is normal in the extraspecial
group. This does not assert normality in any overgroup. -/
public theorem elementary_eight_normal_and_center_le_of_card_thirty_two
    (hP : Nat.card P = 32) (E : Subgroup P) [IsElementaryAbelian 2 E]
    (hE : Nat.card E = 8) : E.Normal ∧ center P ≤ E := by
  let : IsElementaryAbelian 2 (center P) := {
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr fun z => by
      simpa only [center_order_p 2 P] using (pow_card_eq_one' (x := z)) }
  let : IsElementaryAbelian 2 (E ⊔ center P : Subgroup P) :=
    IsElementaryAbelian.sup_of_le_centralizer (center_le_centralizer _)
  have heq : E = E ⊔ center P := eq_of_le_of_card_ge le_sup_left (by
    rw [hE]
    exact elementary_card_le_eight_of_card_thirty_two hP _)
  have hZE : center P ≤ E := heq.symm ▸ le_sup_right
  refine ⟨normalizer_eq_top_iff.mp (top_unique ?_), hZE⟩
  apply le_normalizer_iff_commutator_le_right.mpr
  exact (commutator_mono le_rfl le_top).trans
    ((quotient_elementary_abelian 2 P).commutator_le_center_of_central_quotient.trans hZE)

/-- The two elementary-rank branches exhaust order-32 extraspecial groups. -/
public theorem rank_two_or_normal_elementary_eight_of_card_thirty_two
    (hP : Nat.card P = 32) :
    (∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8) ∨
      ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧
        Nat.card E = 8 ∧ center P ≤ E := by
  classical
  by_cases hrank : ∀ E : Subgroup P, IsElementaryAbelian 2 E → Nat.card E < 8
  · exact Or.inl hrank
  · right
    push Not at hrank
    obtain ⟨E, hEe, hE⟩ := hrank
    let : IsElementaryAbelian 2 E := hEe
    have hcard := Nat.le_antisymm
      (elementary_card_le_eight_of_card_thirty_two hP E) hE
    obtain ⟨hEn, hZE⟩ := elementary_eight_normal_and_center_le_of_card_thirty_two hP E hcard
    exact ⟨E, hEn, hEe, hcard, hZE⟩

end IsExtraspecial
