module

public import Theory.SpecificGroups.PSL3.CartanActions.SixCommutators.Actors
public import Theory.GroupTheory.PCoreLocalSetup

/-!
# Two-elements among linear automorphisms

Raising a GL₃ matrix to the order of the field unit group gives determinant one,
so the corresponding power of its conjugation automorphism is inner. Over the
field of order 64 this is an odd power. A two-element with an inner odd power
is itself inner, for both the special and projective special linear carriers.
Source: GLS3 §2.7; the exclusion used in Aschbacher–Smith 13.8.20, printed p.954.
-/

public section

open scoped MatrixGroups
open Subgroup Matrix Matrix.PSL3.OuterSolvable
namespace Matrix.PSL3.CartanActions.SixCommutators
variable (F : Type*) [Field F]

theorem linearConjSL_toGL_inner (x : SL(3,F)) :
    linearConjSL F (SpecialLinearGroup.toGL x) = MulAut.conj x := by
  apply MulEquiv.ext
  intro y
  apply SpecialLinearGroup.toGL_injective
  rw [linearConjSL_toGL]
  change _ = SpecialLinearGroup.toGL (x * y * x⁻¹)
  rw [map_mul,map_mul,map_inv]

theorem linearConjSL_pow_inner (m : GL (Fin 3) F) :
    (linearConjSL F m) ^ Nat.card Fˣ ∈ MulAut.innerSubgroup SL(3,F) := by
  let v : (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker :=
    ⟨m ^ Nat.card Fˣ, by rw [MonoidHom.mem_ker, map_pow, pow_card_eq_one']⟩
  have hv : SpecialLinearGroup.toGL ((slEquivDetKernel F).symm v) = m ^ Nat.card Fˣ :=
    slEquivDetKernel_symm_toGL F v
  rw [← map_pow, ← hv, linearConjSL_toGL_inner]
  exact ⟨_,rfl⟩

theorem linearConj_pow_inner (m : GL (Fin 3) F) :
    (linearConj F m) ^ Nat.card Fˣ ∈ MulAut.innerSubgroup PSL(3,F) := by
  let v : (GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker :=
    ⟨m ^ Nat.card Fˣ, by rw [MonoidHom.mem_ker, map_pow, pow_card_eq_one']⟩
  have hv : SpecialLinearGroup.toGL ((slEquivDetKernel F).symm v) = m ^ Nat.card Fˣ :=
    slEquivDetKernel_symm_toGL F v
  rw [← map_pow, ← hv, linearConj_toGL]
  exact ⟨_,rfl⟩

private theorem inner_of_two_power_of_odd_power {G : Type*} [Group G]
    (α : MulAut G) (hα : ∃ k : ℕ, α ^ (2 ^ k) = 1)
    {n : ℕ} (hn : Odd n) (hi : α ^ n ∈ MulAut.innerSubgroup G) :
    α ∈ MulAut.innerSubgroup G := by
  let q := QuotientGroup.mk' (MulAut.innerSubgroup G)
  have hi' : q α ^ n = 1 := by
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr hi
  obtain ⟨k,hk⟩ := hα
  have hk' : q α ^ (2 ^ k) = 1 := by rw [← map_pow,hk,map_one]
  have he : orderOf (q α) = 1 := Nat.eq_one_of_dvd_coprimes
    (hn.coprime_two_right.pow_right k)
    (orderOf_dvd_of_pow_eq_one hi') (orderOf_dvd_of_pow_eq_one hk')
  exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp he)

theorem special_linear_two_element_inner (hF : Nat.card F = 2 ^ 6)
    (m : GL (Fin 3) F) (hm : ∃ k : ℕ, (linearConjSL F m) ^ (2 ^ k) = 1) :
    linearConjSL F m ∈ MulAut.innerSubgroup SL(3,F) := by
  apply inner_of_two_power_of_odd_power _ hm _ (linearConjSL_pow_inner F m)
  rw [Nat.card_units,hF]
  decide

theorem projective_linear_two_element_inner (hF : Nat.card F = 2 ^ 6)
    (m : GL (Fin 3) F) (hm : ∃ k : ℕ, (linearConj F m) ^ (2 ^ k) = 1) :
    linearConj F m ∈ MulAut.innerSubgroup PSL(3,F) := by
  apply inner_of_two_power_of_odd_power _ hm _ (linearConj_pow_inner F m)
  rw [Nat.card_units,hF]
  decide
end Matrix.PSL3.CartanActions.SixCommutators
