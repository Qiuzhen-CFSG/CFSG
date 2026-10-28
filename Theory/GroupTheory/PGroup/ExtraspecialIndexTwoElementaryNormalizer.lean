module

public import Theory.GroupTheory.PGroup.ExtraspecialThirtyTwoElementaryAlternative
public import Theory.GroupTheory.NormalCenterQuotient
public import Theory.GroupTheory.IndexTwoIntersection

/-!
# Elementary-eight normalizers in an order-sixty-four group

Without normal elementary eights, an elementary eight has a proper normalizer,
so its normalizer has order at most thirty-two. If the eight is contained in
an extraspecial subgroup of order thirty-two, it contains that subgroup's
center and is normal there. Its normalizer therefore has order exactly
thirty-two. A crossing elementary eight meets the core in a normal four:
adjoining the core center first makes this intersection normal, and the
normal-only bound prevents its growth. These arguments do not impose an
elementary-rank restriction.

Source: the core-contained part of the index-two argument in
Janko–Thompson, Math. Z. 113 (1970), §4, printed p.389.
-/

namespace Subgroup

open scoped IsMulCommutative

/-- In order sixty-four the absence of normal elementary eights bounds
all elementary-eight normalizers by thirty-two. -/
public theorem card_normalizer_le_thirty_two_of_no_normal_eight
    {P : Type*} [Group P] [Finite P] (hP : Nat.card P = 64)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (F : Subgroup P) [IsElementaryAbelian 2 F] (hF : Nat.card F = 8) :
    Nat.card (normalizer (F : Set P)) ≤ 32 := by
  have hproper : normalizer (F : Set P) ≠ ⊤ := by
    intro h
    exact hno ⟨F, normalizer_eq_top_iff.mp h, inferInstance, hF.ge⟩
  have hi : 2 ≤ (normalizer (F : Set P)).index := by
    have hn := (normalizer (F : Set P)).index_ne_zero_of_finite
    have hne : (normalizer (F : Set P)).index ≠ 1 :=
      fun h => hproper (index_eq_one.mp h)
    omega
  have hmul := (normalizer (F : Set P)).card_mul_index
  rw [hP] at hmul
  nlinarith

/-- An elementary eight contained in an extraspecial order-thirty-two
subgroup has normalizer of order thirty-two under the normal-only bound. -/
public theorem card_normalizer_eq_thirty_two_of_elementary_eight_le_extraspecial
    {P : Type*} [Group P] [Finite P] (hP : Nat.card P = 64)
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (H : Subgroup P) [IsExtraspecial 2 H] (hH : Nat.card H = 32)
    (F : Subgroup P) [IsElementaryAbelian 2 F] (hF : Nat.card F = 8)
    (hFH : F ≤ H) : Nat.card (normalizer (F : Set P)) = 32 := by
  let K := F.subgroupOf H
  let : IsElementaryAbelian 2 K := IsElementaryAbelian.subgroupOf hFH
  have hK : Nat.card K = 8 :=
    (Nat.card_congr (subgroupOfEquivOfLe hFH).toEquiv).trans hF
  let : K.Normal :=
    (IsExtraspecial.elementary_eight_normal_and_center_le_of_card_thirty_two hH K hK).1
  have hHN : H ≤ normalizer (F : Set P) := by
    have hh := K.le_normalizer_map H.subtype
    have hKF : K.map H.subtype = F := map_subgroupOf_eq_of_le hFH
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype,
      hKF] using hh
  exact Nat.le_antisymm
    (card_normalizer_le_thirty_two_of_no_normal_eight hP hno F hF)
    (hH ▸ card_le_of_le hHN)

private theorem elementary_of_le {P : Type*} [Group P]
    (E D : Subgroup P) [IsElementaryAbelian 2 D] (hED : E ≤ D) :
    IsElementaryAbelian 2 E := by
  refine {
    toIsMulCommutative := isMulCommutative_iff.mpr ?_
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr ?_ }
  · intro a b
    exact Subtype.ext (congrArg (fun x : D => (x : P))
      (mul_comm (⟨a, hED a.property⟩ : D) (⟨b, hED b.property⟩ : D)))
  · intro a
    exact Subtype.ext (elemPow_eq_one_of_isElementaryAbelian (A := D) a (hED a.property))

/-- An elementary eight crossing an index-two extraspecial subgroup meets
it in a normal elementary four and contains its central involution. -/
public theorem elementary_eight_crossing_extraspecial_intersection {P : Type*} [Group P] [Finite P]
    (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (H : Subgroup P) [IsExtraspecial 2 H] (hi : H.index = 2)
    (F : Subgroup P) [IsElementaryAbelian 2 F] (hF : Nat.card F = 8)
    (hout : ¬ F ≤ H) :
    (H ⊓ F : Subgroup P).Normal ∧ IsElementaryAbelian 2 (H ⊓ F : Subgroup P) ∧
      Nat.card (H ⊓ F : Subgroup P) = 4 ∧
      (center H).map H.subtype ≤ F := by
  let : H.Normal := H.normal_of_index_eq_two hi
  let Z := (center H).map H.subtype
  let : Z.Normal := ConjAct.normal_of_characteristic_of_normal
  have hZcard : Nat.card Z = 2 :=
    (card_map_of_injective H.subtype_injective).trans (IsExtraspecial.center_order_p 2 H)
  have hZC : Z ≤ center P := central_of_normal_card_two Z hZcard
  let : IsElementaryAbelian 2 Z := {
    toIsMulCommutative := isMulCommutative_iff.mpr (by
      intro a b
      exact Subtype.ext (mem_center_iff.mp (hZC a.property) b).symm)
    exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr (by
      intro a
      simpa only [hZcard] using pow_card_eq_one' (x := a)) }
  let D := F ⊔ Z
  let : IsElementaryAbelian 2 D :=
    IsElementaryAbelian.sup_of_le_centralizer (hZC.trans (center_le_centralizer _))
  let J := H ⊓ D
  let : IsElementaryAbelian 2 J := elementary_of_le J D inf_le_right
  let K := J.subgroupOf H
  have hZK : center H ≤ K := by
    intro x hx
    exact ⟨x.property, (le_sup_right : Z ≤ D) (mem_map_of_mem H.subtype hx)⟩
  let : K.Normal := by
    apply normalizer_eq_top_iff.mp
    apply top_unique
    apply le_normalizer_iff_commutator_le_right.mpr
    exact (commutator_mono le_top le_top).trans
      ((IsExtraspecial.quotient_elementary_abelian 2 H).commutator_le_center_of_central_quotient.trans hZK)
  have hHN : H ≤ normalizer (J : Set P) := by
    have hh := K.le_normalizer_map H.subtype
    have hKJ : K.map H.subtype = J := map_subgroupOf_eq_of_le inf_le_left
    simpa only [normalizer_eq_top, ← MonoidHom.range_eq_map, H.range_subtype, hKJ] using hh
  have hFN : F ≤ normalizer (J : Set P) := by
    apply le_trans _ (centralizer_le_normalizer _)
    intro f hf j hj
    exact congrArg (fun d : D => (d : P))
      (mul_comm (⟨j, hj.2⟩ : D) (⟨f, (le_sup_left : F ≤ D) hf⟩ : D))
  have hJn : J.Normal := by
    apply normalizer_eq_top_iff.mp
    apply index_eq_one.mp
    have hdiv : (normalizer (J : Set P)).index ∣ 2 := hi ▸ index_dvd_of_le hHN
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h | h
    · exact h
    · exfalso
      have hm := (normalizer (J : Set P)).card_mul_index
      have hmH := H.card_mul_index
      rw [h] at hm
      rw [hi] at hmH
      have heq : H = normalizer (J : Set P) := eq_of_le_of_card_ge hHN (by omega)
      exact hout (heq ▸ hFN)
  have hJsmall : Nat.card J < 8 := by
    by_contra! h
    exact hno ⟨J, hJn, inferInstance, h⟩
  have hIcard : Nat.card (H ⊓ F : Subgroup P) = 4 := by
    have hh := (H.subgroupOf F).card_mul_index
    rw [H.subgroupOf_index_eq_two F hi hout, hF] at hh
    have heq : (H.subgroupOf F).map F.subtype = H ⊓ F := subgroupOf_map_subtype H F
    have hc : Nat.card ((H.subgroupOf F).map F.subtype) = Nat.card (H.subgroupOf F) :=
      card_map_of_injective F.subtype_injective
    rw [heq] at hc
    omega
  have hIJ : H ⊓ F ≤ J := inf_le_inf_left H le_sup_left
  have hdiv : 4 ∣ Nat.card J := hIcard ▸ card_dvd_of_le hIJ
  have hIJ_eq : H ⊓ F = J := eq_of_le_of_card_ge hIJ (by omega)
  refine ⟨hIJ_eq.symm ▸ hJn, elementary_of_le _ F inf_le_right, hIcard, ?_⟩
  intro z hz
  have hzJ : z ∈ J := ⟨map_subtype_le _ hz, (le_sup_right : Z ≤ D) hz⟩
  exact (show z ∈ H ⊓ F by rwa [hIJ_eq]).2

end Subgroup
