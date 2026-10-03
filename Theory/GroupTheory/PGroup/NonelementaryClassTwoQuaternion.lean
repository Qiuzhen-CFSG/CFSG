module

public import Theory.GroupTheory.Commutator.CentralElementaryFourQuotient
public import Theory.GroupTheory.QuaternionGenerated
public import Theory.GroupTheory.PGroup.NonelementaryCenterQuotientBound
public import Theory.GroupTheory.PGroup.NonelementarySmallQuotientQuaternionLifts

/-!
# Quaternion supplements from a central quotient of order four

Two lifts satisfying the quaternion-eight relations generate an internal
quaternion subgroup. In an elementary central quotient of order four,
noncommutation forces their cosets to be distinct nonidentity elements;
those cosets generate the quotient. The quaternion subgroup therefore
supplements the center. The central elementary-four extension theorem also
gives derived order two.

This is the final presentation step toward the nonelementary-center case of
the three-involution problem, motivated by MacWilliams, Trans. AMS 150
(1970), §3(iv), pp.367–369. The module also assembles the independently
proved quotient bound and odd-automorphism lift extraction into the intrinsic
structural theorem.
-/

open Subgroup
open scoped IsMulCommutative

namespace IsPGroup

private theorem pair_sup_center_eq_top_of_noncommuting
    {P : Type*} [Group P] [Finite P]
    (hquot : IsElementaryAbelian 2 (P ⧸ center P))
    (hcard : Nat.card (P ⧸ center P) = 4)
    (x y : P) (hxy : ¬ Commute x y) :
    closure ({x, y} : Set P) ⊔ center P = ⊤ := by
  classical
  let _ := hquot
  let V := P ⧸ center P
  let q : P →* V := QuotientGroup.mk' (center P)
  let _ : Nontrivial V := (Finite.one_lt_card_iff_nontrivial).mp (by rw [hcard]; decide)
  let _ : IsKleinFour V := ⟨hcard, IsElementaryAbelian.exponent_eq_prime⟩
  let _ : Fintype V := Fintype.ofFinite V
  have hx : q x ≠ 1 := by
    intro h
    exact hxy (mem_center_iff.mp ((QuotientGroup.eq_one_iff x).mp h) y).symm
  have hy : q y ≠ 1 := by
    intro h
    exact hxy (mem_center_iff.mp ((QuotientGroup.eq_one_iff y).mp h) x)
  have hne : q x ≠ q y := by
    intro h
    have hc : Commute x (x⁻¹ * y) := mem_center_iff.mp (QuotientGroup.eq.mp h) x
    have hh := (Commute.refl x).mul_right hc
    simp only [mul_inv_cancel_left] at hh
    exact hxy hh
  let H := closure ({x, y} : Set P) ⊔ center P
  have hxH : x ∈ H := mem_sup_left (subset_closure (by simp))
  have hyH : y ∈ H := mem_sup_left (subset_closure (by simp))
  have transfer (g a : P) (ha : a ∈ H) (h : q g = q a) : g ∈ H := by
    have hm := H.mul_mem ha (mem_sup_right (QuotientGroup.eq.mp h.symm))
    simpa only [mul_inv_cancel_left] using hm
  apply top_unique
  intro g _
  have hm : q g ∈ ({q x * q y, q x, q y, 1} : Finset V) := by
    rw [IsKleinFour.eq_finset_univ hx hy hne]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm | hm | hm
  · exact transfer g (x*y) (H.mul_mem hxH hyH) (by simpa only [map_mul] using hm)
  · exact transfer g x hxH hm
  · exact transfer g y hyH hm
  · exact transfer g 1 H.one_mem (by simpa only [map_one] using hm)

/-- A nonabelian group with elementary central quotient of order four has
derived subgroup of order two. -/
public theorem card_commutator_eq_two_of_elementary_center_quotient_four
    {P : Type*} [Group P] [Finite P]
    (hnonab : ¬ IsMulCommutative P)
    (hquot : IsElementaryAbelian 2 (P ⧸ center P))
    (hcard : Nat.card (P ⧸ center P) = 4) :
    Nat.card (commutator P) = 2 := by
  let _ := hquot
  have hle := card_commutator_le_two_of_central_elementary_four_quotient
    (center P) le_rfl hcard
  have hpos : 0 < Nat.card (commutator P) := Nat.card_pos
  have hne : Nat.card (commutator P) ≠ 1 := by
    intro h
    exact hnonab ((commutator_eq_bot_iff P).mp (card_eq_one.mp h))
  omega

/-- Quaternion relations on two lifts of an elementary central quotient of
order four produce an internal quaternion supplement to the center. -/
public theorem quaternion_supplement_of_center_quotient_four_of_relations
    {P : Type*} [Group P] [Finite P]
    (hquot : IsElementaryAbelian 2 (P ⧸ center P))
    (hcard : Nat.card (P ⧸ center P) = 4)
    (c d : P) (hc : orderOf c = 4) (hsq : d ^ 2 = c ^ 2)
    (hinv : d * c * d⁻¹ = c⁻¹) :
    Nat.card (commutator P) = 2 ∧
      ∃ R : Subgroup P, Nonempty (R ≃* QuaternionGroup 2) ∧ R ⊔ center P = ⊤ := by
  have hnc : ¬ Commute c d := by
    intro h
    have hi : c = c⁻¹ := by
      calc
        c = d * c * d⁻¹ := by rw [h.eq.symm]; group
        _ = c⁻¹ := hinv
    have htwo : c ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [hi]
      exact inv_mul_cancel c
    have hd := orderOf_dvd_of_pow_eq_one htwo
    rw [hc] at hd
    norm_num at hd
  have hout : d ∉ zpowers c := by
    rintro ⟨i, rfl⟩
    exact hnc (Commute.self_zpow c i)
  have hnonab : ¬ IsMulCommutative P := by
    intro h
    let _ := h
    exact hnc (Commute.all c d)
  refine ⟨card_commutator_eq_two_of_elementary_center_quotient_four hnonab hquot hcard,
    closure ({c,d} : Set P), ?_, pair_sup_center_eq_top_of_noncommuting hquot hcard c d hnc⟩
  exact (QuaternionGroup.closure_equiv_of_relations (by decide : 0 < 2)
    c d hc hsq hinv hout).2

/-- A nonelementary center together with a non-two-group automorphism group
forces the quaternion supplement promised by the three-involution argument.
The quotient bound and the extraction of quaternion lifts are kept in their
dedicated modules; this theorem is the intrinsic assembly point. -/
public theorem quaternion_supplement_of_nonelementary_center
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hquot : IsElementaryAbelian 2 (P ⧸ center P))
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (hbad : ¬ IsElementaryAbelian 2 (center P))
    (hAut : ¬ IsPGroup 2 (MulAut P)) :
    Nat.card (commutator P) = 2 ∧
      ∃ R : Subgroup P, Nonempty (R ≃* QuaternionGroup 2) ∧ R ⊔ center P = ⊤ := by
  have hbound := hP.card_center_quotient_le_eight_of_nonelementary_center
    hquot hcentral hthree hbad
  obtain ⟨hfour, c, d, hc, hsq, hinv⟩ :=
    hP.exists_quaternion_lifts_of_nonelementary_center_of_quotient_card_le_eight
      hnonab hquot hcentral hthree hbad hAut hbound
  exact quaternion_supplement_of_center_quotient_four_of_relations
    hquot hfour c d hc hsq hinv

/- Alias emphasizing the class-two central-quotient hypotheses. -/
public theorem quaternion_supplement_of_nonelementary_center_of_class_two
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (hnonab : ¬ IsMulCommutative P)
    (hquot : IsElementaryAbelian 2 (P ⧸ center P))
    (hcentral : ∀ x : P, x ^ 2 = 1 → x ∈ center P)
    (hthree : Nat.card {x : P // orderOf x = 2} = 3)
    (hbad : ¬ IsElementaryAbelian 2 (center P))
    (hAut : ¬ IsPGroup 2 (MulAut P)) :
    Nat.card (commutator P) = 2 ∧
      ∃ R : Subgroup P, Nonempty (R ≃* QuaternionGroup 2) ∧ R ⊔ center P = ⊤ := by
  exact quaternion_supplement_of_nonelementary_center hP hnonab hquot hcentral
    hthree hbad hAut

end IsPGroup
