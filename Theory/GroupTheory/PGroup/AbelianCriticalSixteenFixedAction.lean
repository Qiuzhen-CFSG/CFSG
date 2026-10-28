module

public import Theory.GroupTheory.PGroup.AbelianCriticalSixteenSetup

/-!
# The fixed subgroup of a free cubic action on a critical sixteen

A nonidentity element fixed by the cubic automorphism is an outside
involution. The normal-eight obstruction makes it invert a primitive base
element. Its conjugation action commutes with the cubic base action; composing
with inversion therefore fixes a primitive element and must be the identity.
Thus every nonidentity fixed element inverts the whole C₄-square.

Conjugation on the base is faithful on the fixed subgroup. All its
nonidentity elements induce the same inversion, so it has order at most two.
This sharpens the earlier bound of four without a generator-rank assumption.

Source: MacWilliams, Trans. AMS 150 (1970), Case 1.2, the argument following
(xxii), printed p.382, DOI 10.1090/S0002-9947-1970-0276324-3.
-/

open Subgroup
open scoped IsMulCommutative
namespace IsCriticalPSubgroup
variable {P : Type*} [Group P] [Finite P] {C : Subgroup P}
  (hC : IsCriticalPSubgroup 2 C) [IsMulCommutative C]
  (hno : ¬ ∃ E : Subgroup P, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
  (hZ : Nat.card (omega₁ (center P) (p := 2)) = 4)
  (e : C ≃* C4SquareExtension.Model)
  (a : MulAut P) (ha : orderOf a = 3)
  (hfree : ∀ c ∈ C, a c = c → c = 1)
include hC hno hZ e a ha hfree
/-- A nonidentity cubic-fixed element inverts the entire critical C₄-square. -/
public theorem fixed_element_inverts_c4_square
    (x : P) (hx : a x = x) (hne : x ≠ 1) : ∀ c ∈ C, x * c * x⁻¹ = c⁻¹ := by
  let : C.Characteristic := hC.characteristic
  have hxC : x ∉ C := fun hc => hne (hfree x hc hx)
  have hx2 : x ^ 2 = 1 := by
    let : IsElementaryAbelian 2 a.fixedSubgroup := hC.fixedSubgroup_elementary_of_c4_square hno hZ e a hfree
    exact elemPow_eq_one_of_isElementaryAbelian x ((MulAut.mem_fixedSubgroup a x).mpr hx)
  obtain ⟨v, hv, hv4, hinv⟩ := hC.exists_inverted_order_four_of_involution_not_mem
    hno hZ e (orderOf_eq_prime hx2 hne) hxC
  let b : MulAut C := MulAut.characteristic C a
  let c : MulAut C := MulAut.conjNormal x
  let d : MulAut C := c * MulEquiv.inv C
  have hb3 : b ^ 3 = 1 := by
    change (MulAut.characteristic C a) ^ 3 = 1
    rw [← map_pow, show a ^ 3 = 1 from ha ▸ pow_orderOf_eq_one a, map_one]
  have hbne : b ≠ 1 := by
    intro hb
    have hav : a v = v := congrArg (fun f : MulAut C => (f ⟨v, hv⟩ : P)) hb
    have hv1 := hfree v hv hav
    simp only [hv1, orderOf_one] at hv4
    omega
  have hcb : Commute c b := by
    apply MulEquiv.ext
    intro z
    apply Subtype.ext
    change x * a (z : P) * x⁻¹ = a (x * (z : P) * x⁻¹)
    rw [map_mul, map_mul, map_inv, hx]
  have hdb : Commute d b := by
    apply MulEquiv.ext
    intro z
    change c (b z)⁻¹ = b (c z⁻¹)
    simp only [map_inv]
    exact congrArg Inv.inv (DFunLike.congr_fun hcb.eq z)
  have hdv : d (⟨v, hv⟩ : C) = ⟨v, hv⟩ := by
    change c (⟨v, hv⟩ : C)⁻¹ = ⟨v, hv⟩
    rw [map_inv]
    have hh : c (⟨v, hv⟩ : C) = (⟨v, hv⟩ : C)⁻¹ := Subtype.ext hinv
    rw [hh, inv_inv]
  have hd1 : d = 1 := by
    by_contra hd
    have hs := c4_square_fixed_point_square_eq_one_of_commuting_three
      ⟨e⟩ b hb3 hbne d hd hdb (⟨v, hv⟩ : C) hdv
    have hv2 : v ^ 2 = 1 := congrArg Subtype.val hs
    have hh : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one hv2
    rw [hv4] at hh
    norm_num at hh
  intro z hz
  have hh := congrArg (fun f : MulAut C => (f (⟨z, hz⟩ : C)⁻¹ : P)) hd1
  simp only [d, MulAut.mul_apply, MulEquiv.inv_apply, inv_inv, MulAut.one_apply] at hh
  exact hh

/-- At most one nonidentity element is fixed by the cubic automorphism. -/
public theorem fixedSubgroup_card_le_two_of_c4_square : Nat.card a.fixedSubgroup ≤ 2 := by
  classical
  let : C.Characteristic := hC.characteristic
  have unique (x y : a.fixedSubgroup) (hx : (x : P) ≠ 1) (hy : (y : P) ≠ 1) : x = y := by
    have hxfix := (MulAut.mem_fixedSubgroup a x).mp x.property
    have hyfix := (MulAut.mem_fixedSubgroup a y).mp y.property
    have hact : MulAut.conjNormal (H := C) (x : P) = MulAut.conjNormal (y : P) := by
      apply MulEquiv.ext
      intro c
      apply Subtype.ext
      exact (hC.fixed_element_inverts_c4_square hno hZ e a ha hfree x hxfix hx c c.property).trans
        (hC.fixed_element_inverts_c4_square hno hZ e a ha hfree y hyfix hy c c.property).symm
    have hxyC : (x : P) * (y : P)⁻¹ ∈ C := by
      rw [← conjNormal_ker_eq_of_selfCentralizing_abelian C hC.centralizer_eq_self_of_abelian.le]
      apply MonoidHom.mem_ker.mpr
      rw [map_mul, map_inv, hact, mul_inv_cancel]
    have hxy := hfree _ hxyC (by rw [map_mul, map_inv, hxfix, hyfix])
    exact Subtype.ext (mul_inv_eq_one.mp hxy)
  let f : a.fixedSubgroup → Bool := fun x => decide ((x : P) = 1)
  have hf : Function.Injective f := by
    intro x y hxy
    have hiff : ((x : P) = 1) ↔ ((y : P) = 1) := by
      simpa only [f, decide_eq_decide] using hxy
    by_cases hx : (x : P) = 1
    · exact Subtype.ext (hx.trans (hiff.mp hx).symm)
    · exact unique x y hx (fun hy => hx (hiff.mpr hy))
  simpa using Nat.card_le_card_of_injective f hf
end IsCriticalPSubgroup
