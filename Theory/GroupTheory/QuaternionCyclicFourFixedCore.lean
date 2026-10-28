module

public import Theory.GroupTheory.QuaternionCentralProductSquareAction
public import Theory.GroupTheory.QuaternionCentralProductOuterInvolution
public import Theory.GroupTheory.QuaternionOuterInvolutionFixed
public import Mathlib.GroupTheory.IndexNormal

/-!
# The fixed four in a cyclic-four quaternion extension

An outside involution in a cyclic quotient of order four is the square of a
quotient lift.  Conjugation on the quaternion core is therefore an inner twist
of the square of a two-power-order automorphism.  The intrinsic square-action
calculation makes both quaternion restrictions outer, and its fixed points are
the required elementary four.
-/

open Subgroup

namespace Subgroup

private theorem quotient_card_eq_index {P : Type*} [Group P] [Finite P]
    (H : Subgroup P) [H.Normal] : Nat.card (P ⧸ H) = H.index := by
  rw [← H.index_eq_card]

private def subgroupOfInfEquiv' {P : Type*} [Group P]
    (H K : Subgroup P) : H.subgroupOf K ≃* (H ⊓ K : Subgroup P) where
  toFun x := ⟨x.1, ⟨x.2, x.1.property⟩⟩
  invFun x := ⟨⟨x.1, x.2.2⟩, x.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem elementary_of_mulEquiv' {A D : Type*} [Group A] [Group D]
    (e : A ≃* D) (h : IsElementaryAbelian 2 A) : IsElementaryAbelian 2 D := by
  let _ := h
  refine { toIsMulCommutative := ⟨⟨fun x y => e.symm.injective ?_⟩⟩
           exponent_dvd_p := ?_ }
  · simp only [map_mul]
    exact (IsMulCommutative.is_comm (M := A)).comm _ _
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro x
    apply e.symm.injective
    rw [map_pow, map_one]
    exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p 2 A) _

/-- In a cyclic-four quotient, an outside involution has elementary fixed four
in a self-centralizing quaternion central product of order thirty-two. -/
public theorem quaternion_cyclic_four_fixed_core
    {P : Type*} [Group P] [Finite P] (hP : IsPGroup 2 P)
    (H : Subgroup P) [H.Normal] [IsExtraspecial 2 H]
    (_hH : Nat.card H = 32) (hself : centralizer (H : Set P) ≤ H)
    (hindex : H.index = 4) [IsCyclic (P ⧸ H)]
    (B C : Subgroup H)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hsup : B ⊔ C = ⊤) (hinter : Nat.card (B ⊓ C : Subgroup H) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b * c = c * b)
    (t : P) (ht : orderOf t = 2) (hout : t ∉ H) :
    IsElementaryAbelian 2 (H ⊓ centralizer ({t} : Set P) : Subgroup P) ∧
      Nat.card (H ⊓ centralizer ({t} : Set P) : Subgroup P) = 4 := by
  classical
  let tn : normalizer (H : Set P) :=
    ⟨t, by rw [H.normalizer_eq_top]; trivial⟩
  let e : MulAut H := H.normalizerMonoidHom tn
  have ht2 : t ^ 2 = 1 := ht ▸ pow_orderOf_eq_one t
  have he2 : e ^ 2 = 1 := by
    change (H.normalizerMonoidHom tn) ^ 2 = 1
    rw [← map_pow]
    exact congrArg H.normalizerMonoidHom (Subtype.ext ht2) |>.trans (map_one H.normalizerMonoidHom)
  have heouter : ¬ ∃ p : H, e = MulAut.conj p :=
    normalizer_action_not_inner_of_self_centralizing H hself tn hout
  let qH := QuotientGroup.mk' H
  have hquot : Nat.card (P ⧸ H) = 4 := by
    rw [quotient_card_eq_index, hindex]
  have hqt : (qH t) ^ 2 = 1 := by rw [← map_pow, ht2, map_one]
  have hroot : ∃ b : P ⧸ H, b ^ 2 = qH t := by
    by_cases ht1 : qH t = 1
    · exact ⟨1, by simp [ht1]⟩
    obtain ⟨b, hb⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P ⧸ H)
    rw [hquot] at hb
    have hb2 : orderOf (b ^ 2) = 2 := by rw [orderOf_pow, hb]; norm_num
    exact ⟨b, IsCyclic.eq_of_orderOf_eq_two hb2 (orderOf_eq_prime hqt ht1)⟩
  obtain ⟨b, hb⟩ := hroot
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective H b
  have hsH : t * (s ^ 2)⁻¹ ∈ H := by
    apply (QuotientGroup.eq_one_iff _).mp
    change qH (t * (s ^ 2)⁻¹) = 1
    rw [map_mul, map_inv, map_pow, hb, mul_inv_cancel]
  let p : H := ⟨t * (s ^ 2)⁻¹, hsH⟩
  have htp : t = (p : P) * s ^ 2 := by simp [p]
  let sn : normalizer (H : Set P) :=
    ⟨s, by rw [H.normalizer_eq_top]; trivial⟩
  let β : MulAut H := H.normalizerMonoidHom sn
  obtain ⟨n, hn⟩ : ∃ n : ℕ, s ^ (2 ^ n) = 1 := hP.exists_pow_pow_eq_one s
  have hβ : β ^ (2 ^ n) = 1 := by
    have hsn : sn ^ (2 ^ n) = 1 := Subtype.ext hn
    rw [← map_pow, hsn, map_one]
  have heq : e = MulAut.conj p * β ^ 2 := by
    ext x
    change t * (x : P) * t⁻¹ = _
    rw [htp]
    simp only [MulAut.mul_apply, pow_two, MulAut.conj_apply]
    change (p : P) * (s * s) * (x : P) * ((p : P) * (s * s))⁻¹ =
      (p : P) * ((β (β x) : H) : P) * (p : P)⁻¹
    change (p : P) * (s * s) * (x : P) * ((p : P) * (s * s))⁻¹ =
      (p : P) * (s * (s * (x : P) * s⁻¹) * s⁻¹) * (p : P)⁻¹
    group
  obtain ⟨hBB, hCC, hBO, hCO⟩ := quaternion_central_product_square_action
    B C hB hC hsup hinter hcomm e β p n hβ heq heouter
  obtain ⟨helem, hcard, _⟩ := quaternion_central_product_outer_involution
    B C hB hC hsup hinter hcomm e he2 hBB hCC hBO hCO
  let E := (normalizerActionFixedEquiv H tn).trans
    (subgroupOfInfEquiv' H (centralizer ({t} : Set P)))
  have helem' : IsElementaryAbelian 2 (H ⊓ centralizer ({t} : Set P) : Subgroup P) :=
    elementary_of_mulEquiv' E helem
  have hcard' : Nat.card (H ⊓ centralizer ({t} : Set P) : Subgroup P) = 4 := by
    rw [← Nat.card_congr E.toEquiv]
    exact hcard
  exact ⟨helem', hcard'⟩

end Subgroup
