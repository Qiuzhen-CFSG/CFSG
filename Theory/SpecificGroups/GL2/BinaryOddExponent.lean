module
public import Theory.AtlasPort.LinearGroups.SL2Order
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Algebra.CharP.Two

/-!
# Odd orders in GL₂ over finite fields of characteristic two

Write a matrix as a scalar times a determinant-one matrix by taking the
unique square root of its determinant. Both commuting factors have odd
order. The formula |SL₂(q)| = q(q²−1) bounds the second factor's odd order,
while q−1 bounds the scalar factor. Their least common multiple divides
q²−1, including the nonsplit case.

This supplies the two-dimensional block estimate in the natural parabolic
calculation used for Aschbacher–Smith 8.2.3, printed pp.715–716. The SL₂
order formula is the existing attributed ATLAS port.
-/

public noncomputable section
open Matrix
open scoped MatrixGroups
namespace Matrix.GeneralLinearGroup
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

/-- The odd exponent of GL₂ over a binary field divides q²−1. -/
theorem odd_order_dvd_card_sq_sub_one (A : GL (Fin 2) F) (hA : Odd (orderOf A)) :
    orderOf A ∣ Nat.card F ^ 2 - 1 := by
  let := Fintype.ofFinite F
  obtain ⟨m, _, hm⟩ := FiniteField.card F 2
  have hq : Nat.card F = 2 ^ (m : ℕ) := by simpa only [Nat.card_eq_fintype_card] using hm
  have hoddq : Odd (Nat.card F - 1) := by
    apply Nat.Even.sub_odd (by have := Finite.one_lt_card (α := F); omega) _ (by decide)
    rw [hq]
    exact even_iff_two_dvd.mpr (dvd_pow_self 2 m.ne_zero)
  obtain ⟨c, hc⟩ := surjective_frobenius F 2 (det A).val
  have hc2 : c ^ 2 = (det A).val := hc
  have hc0 : c ≠ 0 := by
    intro h
    exact (det A).ne_zero (by simpa [h] using hc2.symm)
  let u : Fˣ := Units.mk0 c hc0
  have hu : u ^ 2 = det A := Units.ext hc2
  let S := scalar (Fin 2) u
  have hoS : Odd (orderOf S) := hoddq.of_dvd_nat
    ((orderOf_map_dvd (scalar (Fin 2)) u).trans (by
      simpa only [Nat.card_units] using orderOf_dvd_natCard u))
  let B := S⁻¹ * A
  have hdB : det B = 1 := by
    simp only [B,S,map_mul,map_inv,det_scalar,Fintype.card_fin,hu,inv_mul_cancel]
  let b : SL(2,F) := ⟨B.val, Units.ext_iff.mp hdB⟩
  have hb : SpecialLinearGroup.toGL b = B := by ext : 1; rfl
  have hoB : Odd (orderOf B) := by
    apply ((by simpa only [orderOf_inv] using hoS : Odd (orderOf S⁻¹)).mul hA).of_dvd_nat
    exact (show Commute S⁻¹ A from (show Commute S A from scalar_commute u A).inv_left).orderOf_mul_dvd_mul_orderOf
  have hob : Odd (orderOf b) := by
    rwa [← hb, orderOf_injective SpecialLinearGroup.toGL SpecialLinearGroup.toGL_injective] at hoB
  have hdb : orderOf b ∣ Nat.card F ^ 2 - 1 := by
    have hh := orderOf_dvd_natCard b
    rw [Atlas.card_sl_two, hq] at hh
    rw [hq]
    exact ((Nat.coprime_two_right.mpr hob).pow_right (m : ℕ)).dvd_of_dvd_mul_left hh
  have hdS : orderOf S ∣ Nat.card F ^ 2 - 1 := by
    apply (orderOf_map_dvd (scalar (Fin 2)) u).trans
    apply (by simpa only [Nat.card_units] using orderOf_dvd_natCard u :
      orderOf u ∣ Nat.card F - 1).trans
    exact Nat.sub_dvd_pow_sub_pow (Nat.card F) 1 2
  have hdB' : orderOf B ∣ Nat.card F ^ 2 - 1 := by
    rw [←hb]
    exact (orderOf_map_dvd SpecialLinearGroup.toGL b).trans hdb
  have he : A = S * B := by dsimp [B]; group
  rw [he]
  exact (show Commute S B from by
    dsimp [B]
    exact (Commute.inv_right (Commute.refl S)).mul_right (scalar_commute u A)).orderOf_mul_dvd_lcm.trans
      (Nat.lcm_dvd hdS hdB')
end Matrix.GeneralLinearGroup
