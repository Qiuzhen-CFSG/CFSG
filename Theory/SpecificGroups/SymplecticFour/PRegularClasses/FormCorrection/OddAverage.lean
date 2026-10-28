module

public import Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection.AlternatingHalf
public import Mathlib.Algebra.CharP.Two
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Equivariant linear halves in characteristic two

The conjugation average of a linear half still solves the same linear equation.
An odd cyclic group has cardinality one in the coefficient field, so the sum
needs no normalization. This is the sole use of odd order in the form-correction
argument; it applies also on the eigenvalue-one summand.
-/

namespace Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection

open Matrix
open scoped BigOperators
variable {F : Type*} [Field F]
variable {n : Type*} [Fintype n] [DecidableEq n]
variable {K : Type*} [Group K] [Fintype K]

private theorem average_half (ρ : K →* Matrix n n F) (A Z₀ : Matrix n n F)
    (hA : ∀ k, (ρ k).transpose * A * ρ k = A)
    (hZ₀ : Z₀.transpose * A + A * Z₀ = A)
    (hc : (Fintype.card K : F) = 1) :
    ∃ Z : Matrix n n F, (∀ k, Commute Z (ρ k)) ∧ Z.transpose * A + A * Z = A := by
  classical
  have hleft (k : K) : A * ρ k = (ρ k⁻¹).transpose * A := by
    calc
      A * ρ k = ((ρ k⁻¹).transpose * A * ρ k⁻¹) * ρ k := by rw [hA]
      _ = (ρ k⁻¹).transpose * A := by rw [mul_assoc, ← map_mul]; simp
  have hright (k : K) : (ρ k).transpose * A = A * ρ k⁻¹ := by
    calc
      (ρ k).transpose * A = ((ρ k).transpose * A) * (ρ k * ρ k⁻¹) := by
        rw [← map_mul]; simp
      _ = ((ρ k).transpose * A * ρ k) * ρ k⁻¹ := by simp only [mul_assoc]
      _ = _ := by rw [hA]
  let Z := ∑ k : K, ρ k * Z₀ * ρ k⁻¹
  have hconj (k : K) : ρ k * Z * ρ k⁻¹ = Z := by
    simp only [Z, Finset.mul_sum, Finset.sum_mul]
    apply Fintype.sum_equiv (Equiv.mulLeft k)
    intro j
    change ρ k * (ρ j * Z₀ * ρ j⁻¹) * ρ k⁻¹ = ρ (k * j) * Z₀ * ρ (k * j)⁻¹
    simp only [map_mul, _root_.mul_inv_rev, mul_assoc]
  refine ⟨Z, ?_, ?_⟩
  · intro k
    change Z * ρ k = ρ k * Z
    calc
      Z * ρ k = (ρ k * Z * ρ k⁻¹) * ρ k := by rw [hconj]
      _ = ρ k * Z := by rw [mul_assoc, ← map_mul]; simp
  · have hterm (k : K) :
        (ρ k * Z₀ * ρ k⁻¹).transpose * A + A * (ρ k * Z₀ * ρ k⁻¹) = A := by
      calc
        _ = (ρ k⁻¹).transpose * (Z₀.transpose * A + A * Z₀) * ρ k⁻¹ := by
          simp only [transpose_mul, mul_add, add_mul, mul_assoc]
          rw [hright,
            ← mul_assoc A (ρ k), hleft k]
          simp only [mul_assoc]
        _ = _ := by rw [hZ₀, hA]
    calc
      Z.transpose * A + A * Z =
          ∑ k : K, ((ρ k * Z₀ * ρ k⁻¹).transpose * A + A * (ρ k * Z₀ * ρ k⁻¹)) := by
        simp only [Z, transpose_sum, Finset.sum_mul, Finset.mul_sum, Finset.sum_add_distrib]
      _ = ∑ _k : K, A := by simp_rw [hterm]
      _ = A := by simp [← Nat.cast_smul_eq_nsmul F, hc]
variable [CharP F 2] {G : Type*} [Group G] [Finite G]
/-- Averaging a linear half over an odd cyclic group makes it equivariant. -/
public theorem exists_odd_invariant_half (ρ : G →* Matrix n n F) (g : G) (hg : ¬ 2 ∣ orderOf g)
    (A : Matrix n n F) (hA : A.toBilin'.IsAlt)
    (hinv : (ρ g).transpose * A * ρ g = A) :
    ∃ Z : Matrix n n F, Commute Z (ρ g) ∧ Z.transpose * A + A * Z = A := by
  classical
  let H : Subgroup G := {
    carrier := {k | (ρ k).transpose * A * ρ k = A}
    one_mem' := by simp
    mul_mem' := by
      intro a b ha hb
      change (ρ (a * b)).transpose * A * ρ (a * b) = A
      rw [map_mul, transpose_mul]
      calc
        (ρ b).transpose * (ρ a).transpose * A * (ρ a * ρ b) =
            (ρ b).transpose * ((ρ a).transpose * A * ρ a) * ρ b := by simp only [mul_assoc]
        _ = A := by rw [ha, hb]
    inv_mem' := by
      intro a ha
      change (ρ a⁻¹).transpose * A * ρ a⁻¹ = A
      calc
        _ = (ρ a⁻¹).transpose * ((ρ a).transpose * A * ρ a) * ρ a⁻¹ := by rw [ha]
        _ = ((ρ a * ρ a⁻¹).transpose) * A * (ρ a * ρ a⁻¹) := by
          simp only [transpose_mul, mul_assoc]
        _ = A := by rw [← map_mul]; simp }
  have hsub : Subgroup.zpowers g ≤ H := Subgroup.zpowers_le.mpr hinv
  let := Fintype.ofFinite (Subgroup.zpowers g)
  obtain ⟨Z₀, hZ₀⟩ := exists_alternating_half A hA
  obtain ⟨Z, hZ, hZA⟩ := average_half (ρ.comp (Subgroup.zpowers g).subtype) A Z₀
    (fun k : Subgroup.zpowers g => hsub k.property) hZ₀ (by
      rw [← Nat.card_eq_fintype_card, Nat.card_zpowers]
      exact natCast_eq_one_of_odd_of_two_eq_zero (Nat.not_even_iff_odd.mp (by simpa only [even_iff_two_dvd] using hg)) CharTwo.two_eq_zero)
  exact ⟨Z, hZ ⟨g, Subgroup.mem_zpowers g⟩, hZA⟩
end Theory.SpecificGroups.SymplecticFour.PRegularClasses.FormCorrection
