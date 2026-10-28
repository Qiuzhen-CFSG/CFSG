module
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Algebra.CharP.Two

/-!
# Odd-order determinant-one operators move at least two dimensions

An operator with displacement rank at most one is a dilatation or a
transvection. Its determinant is one plus the value of the defining
functional on its displacement vector. Determinant one makes that value
zero; in characteristic two the resulting transvection has square one.
An odd-order operator is therefore the identity.

This supplies the inner linear case in Aschbacher--Smith H.2, printed p.378.
-/
public section
namespace LinearEquiv
open Module
variable {F W : Type*} [Field F] [CharP F 2] [AddCommGroup W] [Module F W]
  [FiniteDimensional F W]

/-- An odd-order determinant-one operator cannot have displacement rank one. -/
theorem two_le_displacement_of_odd_det_one (e : W ≃ₗ[F] W)
    (hne : e ≠ 1) (ho : Odd (orderOf e)) (hd : e.det = 1) :
    2 ≤ finrank F (LinearMap.range (e.toLinearMap - LinearMap.id)) := by
  by_contra! hsmall
  obtain ⟨f,v,he⟩ := mem_dilatransvections_iff_finrank.mpr (show
    finrank F (LinearMap.range (e.toLinearMap - LinearMap.id)) ≤ 1 by omega)
  have hf : f v = 0 := by
    have hh := congrArg Units.val hd
    rw [LinearEquiv.coe_det] at hh
    rw [he, LinearMap.transvection.det] at hh
    exact add_left_cancel (hh.trans (add_zero (1 : F)).symm)
  have he2 : e^2 = 1 := by
    ext w
    have hew : ∀ w, e w = w + f w • v := fun w => LinearMap.congr_fun he w
    change e (e w) = w
    rw [hew,hew]
    simp only [map_add, LinearMap.map_smul, hf, smul_zero, add_zero]
    rw [add_assoc, ←add_smul, CharTwo.add_self_eq_zero,zero_smul,add_zero]
  have hd2 : orderOf e ∣ 2 := orderOf_dvd_of_pow_eq_one he2
  have hd1 : orderOf e ∣ 1 := by
    simpa only [ho.coprime_two_right.gcd_eq_one] using Nat.dvd_gcd (dvd_refl (orderOf e)) hd2
  exact hne (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd1))
end LinearEquiv
