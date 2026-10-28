module

public import Theory.SpecificGroups.ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals.SplitExchanges

/-!
# Remaining short angular exchanges in the concrete Ree group

The existing split-root exchange laws collect the nine main-curve pairs not
covered by the normal-generation calculation. The factors include the central
curves of the nonabelian B₂ blocks. Indices are zero based.

Source: GLS3, Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
-/

public section
open Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals
open Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open Parabolics MatrixRelations MatrixRelations.LongCommutators
open Parabolics.RadicalCoordinates.FixedCoordinates
noncomputable section

private theorem fieldEnd_half (m : ℕ) (i : Fin 8) :
    rootFieldEnd m (longRoot i) = halfFrobenius m := by
  simp only [rootFieldEnd, if_pos (longRoot_isLong i), halfFrobenius]

private theorem word_0 (m : ℕ) (t : CoefficientField m) :
    rootWord m 0 t = X m 0 t * X m 1 (halfFrobenius m t) * X m 2 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_1 (m : ℕ) (t : CoefficientField m) :
    rootWord m 1 t = X m 4 t * X m 5 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change X m 4 t * X m 5 (halfFrobenius m t) * 1 = _
  exact mul_one _

private theorem word_2 (m : ℕ) (t : CoefficientField m) :
    rootWord m 2 t = X m 6 t * X m 7 (halfFrobenius m t) * X m 8 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_3 (m : ℕ) (t : CoefficientField m) :
    rootWord m 3 t = X m 10 t * X m 11 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change X m 10 t * X m 11 (halfFrobenius m t) * 1 = _
  exact mul_one _

private theorem word_4 (m : ℕ) (t : CoefficientField m) :
    rootWord m 4 t = X m 12 t * X m 13 (halfFrobenius m t) * X m 14 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_5 (m : ℕ) (t : CoefficientField m) :
    rootWord m 5 t = X m 16 t * X m 17 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change X m 16 t * X m 17 (halfFrobenius m t) * 1 = _
  exact mul_one _

private theorem word_6 (m : ℕ) (t : CoefficientField m) :
    rootWord m 6 t = X m 18 t * X m 19 (halfFrobenius m t) * X m 20 (t * halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  rfl

private theorem word_7 (m : ℕ) (t : CoefficientField m) :
    rootWord m 7 t = X m 22 t * X m 23 (halfFrobenius m t) := by
  simp only [rootWord, fieldEnd_half]
  change X m 22 t * X m 23 (halfFrobenius m t) * 1 = _
  exact mul_one _

private theorem central_4 (m : ℕ) (t : CoefficientField m) :
    centralWord m 4 t = X m 15 t * X m 14 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]
  rfl

private theorem commutator_of_swap {G : Type*} [Group G] {a b c : G}
    (h : a * b = b * a * c) : a⁻¹ * b⁻¹ * a * b = c := by
  calc
    _ = a⁻¹ * b⁻¹ * (a * b) := by simp only [mul_assoc]
    _ = c := by rw [h]; simp only [mul_assoc, inv_mul_cancel_left]


private theorem central_2 (m : ℕ) (t : CoefficientField m) :
    centralWord m 2 t = X m 9 t * X m 8 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]
  rfl

private theorem central_6 (m : ℕ) (t : CoefficientField m) :
    centralWord m 6 t = X m 21 t * X m 20 (halfFrobenius m t) := by
  simp only [centralWord, fieldEnd_half]
  rfl

attribute [local irreducible] X

/-- Source right commutator for positions 1 and 3. -/
theorem rootWord_commutator_0_2 (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 0 t)⁻¹ * (rootWord m 2 u)⁻¹ * rootWord m 0 t * rootWord m 2 u =
      rootWord m 1 (t * u) := by
  apply commutator_of_swap
  rw [word_0, word_2, word_1]
  simp only [map_mul]
  simpa only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using
    collect_0_2 m t (halfFrobenius m t) u (halfFrobenius m u)

/-- Source right commutator for positions 3 and 5. -/
theorem rootWord_commutator_2_4 (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 2 t)⁻¹ * (rootWord m 4 u)⁻¹ * rootWord m 2 t * rootWord m 4 u =
      rootWord m 3 (t * u) := by
  apply commutator_of_swap
  rw [word_2, word_4, word_3]
  simp only [map_mul]
  simpa only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using
    collect_2_4 m t (halfFrobenius m t) u (halfFrobenius m u)

/-- Source right commutator for positions 5 and 7. -/
theorem rootWord_commutator_4_6 (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 4 t)⁻¹ * (rootWord m 6 u)⁻¹ * rootWord m 4 t * rootWord m 6 u =
      rootWord m 5 (t * u) := by
  apply commutator_of_swap
  rw [word_4, word_6, word_5]
  simp only [map_mul]
  simpa only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using
    collect_4_6 m t (halfFrobenius m t) u (halfFrobenius m u)

/-- Source right commutator for positions 2 and 5. -/
theorem rootWord_commutator_1_4 (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 1 t)⁻¹ * (rootWord m 4 u)⁻¹ * rootWord m 1 t * rootWord m 4 u =
      centralWord m 2 (t * u) := by
  apply commutator_of_swap
  rw [word_1, word_4, central_2]
  simp only [map_mul]
  simpa only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using
    collect_1_4 m t (halfFrobenius m t) u (halfFrobenius m u)

/-- Source right commutator for positions 3 and 6. -/
theorem rootWord_commutator_2_5 (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 2 t)⁻¹ * (rootWord m 5 u)⁻¹ * rootWord m 2 t * rootWord m 5 u =
      centralWord m 4 (t * u) := by
  apply commutator_of_swap
  rw [word_2, word_5, central_4]
  simp only [map_mul]
  simpa only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using
    collect_2_5 m t (halfFrobenius m t) u (halfFrobenius m u)

/-- Source right commutator for positions 4 and 7. -/
theorem rootWord_commutator_3_6 (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 3 t)⁻¹ * (rootWord m 6 u)⁻¹ * rootWord m 3 t * rootWord m 6 u =
      centralWord m 4 (t * u) := by
  apply commutator_of_swap
  rw [word_3, word_6, central_4]
  simp only [map_mul]
  simpa only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using
    collect_3_6 m t (halfFrobenius m t) u (halfFrobenius m u)

/-- Source right commutator for positions 5 and 8. -/
theorem rootWord_commutator_4_7 (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 4 t)⁻¹ * (rootWord m 7 u)⁻¹ * rootWord m 4 t * rootWord m 7 u =
      centralWord m 6 (t * u) := by
  apply commutator_of_swap
  rw [word_4, word_7, central_6]
  simp only [map_mul]
  simpa only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using
    collect_4_7 m t (halfFrobenius m t) u (halfFrobenius m u)

/-- Source right commutator for positions 2 and 7. -/
theorem rootWord_commutator_1_6 (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 1 t)⁻¹ * (rootWord m 6 u)⁻¹ * rootWord m 1 t * rootWord m 6 u =
      rootWord m 3 (t * titsEnd m u) * centralWord m 2 (titsEnd m t * u) := by
  apply commutator_of_swap
  rw [word_1, word_6, word_3, central_2]
  simp only [map_mul, halfFrobenius_titsEnd]
  simpa only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using
    collect_1_6 m t (halfFrobenius m t) u (halfFrobenius m u)

/-- Source right commutator for positions 3 and 8. -/
theorem rootWord_commutator_2_7 (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 2 t)⁻¹ * (rootWord m 7 u)⁻¹ * rootWord m 2 t * rootWord m 7 u =
      rootWord m 5 (titsEnd m t * u) * centralWord m 6 (t * titsEnd m u) := by
  apply commutator_of_swap
  rw [word_2, word_7, word_5, central_6]
  simp only [map_mul, halfFrobenius_titsEnd]
  simpa only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using
    collect_2_7 m t (halfFrobenius m t) u (halfFrobenius m u)

end
end ReeF4.CentralCovers.TwoPrimary.TailRelations.BaseIntervals
