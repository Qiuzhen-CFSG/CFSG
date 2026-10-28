module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# A central product of three conjugate inverters

Conjugates of an element inverting a normal subgroup also invert it. A product
of three such conjugates therefore inverts the subgroup. If that product also
centralizes it, every element has order dividing two; an odd-order subgroup
must then be trivial.

Application: the three singular vectors of the binary A₅ centralizer module
have product v. This gives the odd-core step of Aschbacher–Smith, combined
1 March 2004 manuscript, 13.6.6, printed pp.926–927.
-/

namespace Subgroup

variable {G : Type*} [Group G]

private theorem conjugate_inverts (O : Subgroup G) [O.Normal] (z c x : G)
    (hx : x ∈ O) (hi : ∀ y ∈ O, MulAut.conj z y = y⁻¹) :
    MulAut.conj (MulAut.conj c z) x = x⁻¹ := by
  have hm : MulAut.conj c⁻¹ x ∈ O :=
    Subgroup.Normal.conj_mem inferInstance x hx c⁻¹
  have h := congrArg (MulAut.conj c) (hi _ hm)
  simpa [MulAut.conj_apply, mul_assoc] using h

/-- An odd-order normal subgroup inverted by z is trivial if a product of
three conjugates of z centralizes it. The conjugating elements are actual
elements of the ambient group. -/
public theorem eq_bot_of_conjugate_inverters [Finite G]
    (O : Subgroup G) [O.Normal] (hodd : Nat.Coprime 2 (Nat.card O))
    (z c d : G) (hi : ∀ x ∈ O, MulAut.conj z x = x⁻¹)
    (hc : z * MulAut.conj c z * MulAut.conj d z ∈ centralizer (O : Set G)) :
    O = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  have ht : MulAut.conj (z * MulAut.conj c z * MulAut.conj d z) x = x⁻¹ := by
    rw [map_mul, map_mul]
    simp only [MulAut.mul_apply, conjugate_inverts O z d x hx hi, map_inv,
      conjugate_inverts O z c x hx hi, inv_inv, hi x hx]
  have hfix : MulAut.conj (z * MulAut.conj c z * MulAut.conj d z) x = x := by
    change (z * MulAut.conj c z * MulAut.conj d z) * x *
      (z * MulAut.conj c z * MulAut.conj d z)⁻¹ = x
    rw [← mem_centralizer_iff.mp hc x hx, mul_assoc, mul_inv_cancel, mul_one]
  have hs : (⟨x, hx⟩ : O) ^ 2 = 1 := by
    apply Subtype.ext
    change x ^ 2 = 1
    rw [pow_two]
    nth_rw 1 [hfix.symm.trans ht]
    exact inv_mul_cancel x
  have horder : orderOf (⟨x, hx⟩ : O) = 1 :=
    Nat.eq_one_of_dvd_coprimes hodd (orderOf_dvd_of_pow_eq_one hs)
      (_root_.orderOf_dvd_natCard _)
  exact congrArg Subtype.val (orderOf_eq_one_iff.mp horder)

end Subgroup
