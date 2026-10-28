module

/-
Copyright (c) 2026 Gerald Höhn. All rights reserved.
Covered by the ATLAS Research and Attribution License 1.0 (LICENSES/ATLAS.txt).
Adapted from Atlas/FieldTheory/ReeTitsAutomorphism.lean at
8eabb35afe2b5e45bf913a2d05c53e558d2e2917.
Changes: project module/public-import conventions; Lean 4.33 compatibility.
-/

public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.Tactic

/-! Frobenius powers for the small Ree construction. The inverse identities use
only the actual field cardinality, and are independent of all group constructions. -/
@[expose] public section

noncomputable section
namespace Atlas.ReeG2
variable (F : Type*) [Field F] [Finite F] [CharP F 3]

/-- The inverse Tits automorphism, x ↦ x ^ (3 ^ m). -/
def theta (m : ℕ) : F ≃+* F := iterateFrobeniusEquiv F 3 m
/-- The Tits automorphism, x ↦ x ^ (3 ^ (m + 1)). -/
def sigma (m : ℕ) : F ≃+* F := iterateFrobeniusEquiv F 3 (m + 1)

@[simp] theorem theta_apply (m : ℕ) (x : F) : theta F m x = x ^ (3 ^ m) := rfl
@[simp] theorem sigma_apply (m : ℕ) (x : F) : sigma F m x = x ^ (3 ^ (m + 1)) := rfl

variable {F} {m : ℕ}
theorem frobenius_period (hcard : Nat.card F = 3 ^ (2 * m + 1)) (x : F) :
    iterateFrobeniusEquiv F 3 (2 * m + 1) x = x := by
  let := Fintype.ofFinite F
  rw [iterateFrobeniusEquiv_def, ← hcard, Nat.card_eq_fintype_card]
  exact FiniteField.pow_card x

@[simp] theorem sigma_theta (hcard : Nat.card F = 3 ^ (2 * m + 1)) (x : F) :
    sigma F m (theta F m x) = x := by
  change iterateFrobeniusEquiv F 3 (m + 1) (iterateFrobeniusEquiv F 3 m x) = x
  rw [← iterateFrobeniusEquiv_add_apply]
  convert frobenius_period hcard x using 1
  congr 2
  omega

@[simp] theorem theta_sigma (hcard : Nat.card F = 3 ^ (2 * m + 1)) (x : F) :
    theta F m (sigma F m x) = x := by
  change iterateFrobeniusEquiv F 3 m (iterateFrobeniusEquiv F 3 (m + 1) x) = x
  rw [← iterateFrobeniusEquiv_add_apply]
  convert frobenius_period hcard x using 1
  congr 2
  omega

theorem sigma_eq_theta_symm (hcard : Nat.card F = 3 ^ (2 * m + 1)) :
    sigma F m = (theta F m).symm := by
  ext x
  apply (theta F m).injective
  simp only [theta_sigma hcard, RingEquiv.apply_symm_apply]

theorem sigma_eq_theta_cube (x : F) : sigma F m x = (theta F m x) ^ 3 := by
  rw [sigma_apply, theta_apply, ← pow_mul, pow_succ]

theorem sigma_square (hcard : Nat.card F = 3 ^ (2 * m + 1)) (x : F) :
    sigma F m (sigma F m x) = x ^ 3 := by
  rw [sigma_eq_theta_cube, theta_sigma hcard]

theorem theta_square_cube (hcard : Nat.card F = 3 ^ (2 * m + 1)) (x : F) :
    (theta F m (theta F m x)) ^ 3 = x := by
  rw [← sigma_eq_theta_cube, sigma_theta hcard]

variable {K : Type*} [Field K] [Finite K] [CharP K 3]
theorem map_theta (e : F ≃+* K) (m : ℕ) (x : F) :
    e (theta F m x) = theta K m (e x) := by simp only [theta_apply, map_pow]
theorem map_sigma (e : F ≃+* K) (m : ℕ) (x : F) :
    e (sigma F m x) = sigma K m (e x) := by simp only [sigma_apply, map_pow]

/-- The public parameter range starts at 27; the field lemmas themselves need no lower bound. -/
structure Parameters (F : Type*) [Field F] [Finite F] (m : ℕ) : Prop where
  positive : 1 ≤ m
  cardinality : Nat.card F = 3 ^ (2 * m + 1)

omit [CharP F 3] in
theorem card_ge_27 (h : Parameters F m) : 27 ≤ Nat.card F := by
  rw [h.cardinality]
  calc
    27 = 3 ^ 3 := by norm_num
    _ ≤ 3 ^ (2 * m + 1) := Nat.pow_le_pow_right (by omega) (by have := h.positive; omega)
end Atlas.ReeG2
