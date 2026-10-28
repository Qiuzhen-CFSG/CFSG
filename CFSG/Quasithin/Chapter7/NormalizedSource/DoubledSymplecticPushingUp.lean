module
public import CFSG.Quasithin.Chapter7.NormalizedSource.DoubledSymplecticLocal
public import Theory.SpecificGroups.SymplecticFour.Sylow.CentralRootGeometry.Coordinates

/-!
# Nonbinary symplectic inputs to the source pushing-up exclusions

The standard unipotent coordinates exhibit a two-element with nonidentity
square. The exact symplectic group order is greater than 20160 and cannot
divide |SL₅(2)|: degree two has order 979200, and every larger degree already
exceeds |SL₅(2)|. These are the concrete premises consumed by the ordinary
and constrained C.2.8 exclusions on the original doubled orbit.

Source: Aschbacher--Smith C.2.7 and 4.2.12--13, printed pp.146--147,
610--612, applied to 4.4.6 and 7.3.4, refs/quasithin.pdf.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter7.NormalizedSource
open Theory.SpecificGroups.SymplecticFour
variable {F : Type*} [Field F] [Finite F] [CharP F 2]

theorem doubledSymplectic_not_two_exponent {n : ℕ} (hF : Nat.card F = 2^n) :
    ¬ ∀ P : Subgroup (Sp F), IsPGroup 2 P → ∀ x : P, x ^ 2 = 1 := by
  intro h
  have hx := h unipotent (isPGroup_unipotent hF) (CentralRootGeometry.element 1 0 0 1)
  rw [CentralRootGeometry.element_square] at hx
  have he : CentralRootGeometry.element (0 : F) 1 1 0 =
      CentralRootGeometry.element 0 0 0 0 := by
    rw [CentralRootGeometry.element_zero]
    simpa only [one_pow,one_mul,CentralRootGeometry.theta] using hx
  exact one_ne_zero ((CentralRootGeometry.element_eq_iff _ _ _ _ _ _ _ _).mp he).2.1

omit [CharP F 2] in
private theorem card_sp_lower_bound (q : ℕ) (hq : q ≤ Nat.card F) :
    q^4 * (q^2-1) * (q^4-1) ≤ Nat.card (Sp F) := by
  rw [card_sp]
  exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.pow_le_pow_left hq 4)
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1))
    (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 4) 1)

omit [CharP F 2] in
theorem doubledSymplectic_card_gt_20160 {n : ℕ} (hF : Nat.card F = 2^n) (hn : 1 < n) :
    20160 < Nat.card (Sp F) := by
  have hq : 4 ≤ Nat.card F := by
    rw [hF]
    exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 2 ≤ n)
  have hh := card_sp_lower_bound (F := F) 4 hq
  norm_num at hh
  omega

omit [CharP F 2] in
theorem doubledSymplectic_card_not_dvd_linear_five_two {n : ℕ}
    (hF : Nat.card F = 2^n) (hn : 1 < n) : ¬ Nat.card (Sp F) ∣ 9999360 := by
  by_cases htwo : n = 2
  · rw [card_sp,hF,htwo]
    norm_num
  · have hq : 8 ≤ Nat.card F := by
      rw [hF]
      exact Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (by omega : 3 ≤ n)
    have hh := card_sp_lower_bound (F := F) 8 hq
    norm_num at hh
    intro hd
    have := Nat.le_of_dvd (by decide : 0 < 9999360) hd
    omega
end CFSG.Quasithin.Chapter7.NormalizedSource
