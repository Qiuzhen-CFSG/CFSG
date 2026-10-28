module

public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.Relations
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.WeylGeometry
public import Theory.SpecificGroups.ReeF4.ParabolicAmalgam.OuterLocal.SuzukiCommutators.NormalGeneration.MatrixRelations.LongCommutators.Collection

/-!
# The two long right commutators of Ree root words

The split-root calculations in `LongCommutators.Collection` exchange the
first word with the eighth and seventh words. Specializing their four scalar
parameters to t, θ(t), u, θ(u) gives the relative-root factors. Here θ is
`halfFrobenius`, θ(t)² is `titsEnd m t`, and θ composed with `titsEnd` is the
identity. The inverse third-root word is expanded in reverse split-root order;
the central fifth-root word retains its high-root factor before its mixed-root
factor. Thus the displayed products have exactly the source order.

These are equalities in the existing split F₄ matrix group for every m,
including zero. They require no root-relations, generation, order, or
perfectness hypothesis. Together with the short commutators they supply the
commutator clauses for the separate `RootRelations` assembly.

Source: GLS3, Table 2.4 and 2.4.5(d), `refs/KGroup/GLS3/chapter2.tex`.
Application: Aschbacher–Smith F.1.12(II)(i), printed pp.263–264 of
`refs/quasithin.pdf`.
-/

public section

open Theory.AlgebraicGroup StandardRootSystem
namespace ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
open MatrixRelations MatrixRelations.LongCommutators RadicalCoordinates.FixedCoordinates
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

attribute [local irreducible] X

private theorem eighth_second (m : ℕ) (t u : CoefficientField m) :
    rootWord m 1 ((t ^ 2 * titsEnd m t) * u) =
      X m 4 (t ^ 2 * (halfFrobenius m t) ^ 2 * u) *
        X m 5 (t * (halfFrobenius m t) ^ 2 * (halfFrobenius m u)) := by
  rw [word_1]
  simp only [map_mul, map_pow, halfFrobenius_titsEnd]
  simp only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm]

private theorem eighth_third (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 2 ((t * titsEnd m t) * u))⁻¹ =
      X m 8 (t ^ 2 * (halfFrobenius m t) ^ 3 * u * (halfFrobenius m u)) *
        X m 7 (t * (halfFrobenius m t) * (halfFrobenius m u)) *
        X m 6 (t * (halfFrobenius m t) ^ 2 * u) := by
  rw [word_2]
  simp only [mul_inv_rev, xi, map_mul, halfFrobenius_titsEnd]
  simp only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm]

private theorem eighth_fourth (m : ℕ) (t u : CoefficientField m) :
    rootWord m 3 ((t ^ 2 * titsEnd m t ^ 2) * (u * titsEnd m u)) =
      X m 10 (t ^ 2 * (halfFrobenius m t) ^ 4 * u * (halfFrobenius m u) ^ 2) *
        X m 11 (t ^ 2 * (halfFrobenius m t) ^ 2 * u * (halfFrobenius m u)) := by
  rw [word_3]
  simp only [map_mul, map_pow, halfFrobenius_titsEnd]
  simp only [← halfFrobenius_sq]
  apply congrArg₂ (· * ·) <;> apply congrArg (X m _) <;> ring

private theorem eighth_central (m : ℕ) (t u : CoefficientField m) :
    centralWord m 4 ((t ^ 3 * titsEnd m t ^ 2) * (u ^ 2 * titsEnd m u)) =
      X m 15 (t ^ 3 * (halfFrobenius m t) ^ 4 * u ^ 2 * (halfFrobenius m u) ^ 2) *
        X m 14 (t ^ 2 * (halfFrobenius m t) ^ 3 * u * (halfFrobenius m u) ^ 2) := by
  rw [central_4]
  simp only [map_mul, map_pow, halfFrobenius_titsEnd]
  simp only [← halfFrobenius_sq]
  apply congrArg₂ (· * ·) <;> apply congrArg (X m _) <;> ring

private theorem eighth_sixth (m : ℕ) (t u : CoefficientField m) :
    rootWord m 5 ((t ^ 2 * titsEnd m t) * (u * titsEnd m u)) =
      X m 16 (t ^ 2 * (halfFrobenius m t) ^ 2 * u * (halfFrobenius m u) ^ 2) *
        X m 17 (t * (halfFrobenius m t) ^ 2 * u * (halfFrobenius m u)) := by
  rw [word_5]
  simp only [map_mul, map_pow, halfFrobenius_titsEnd]
  simp only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm]

private theorem eighth_seventh (m : ℕ) (t u : CoefficientField m) :
    rootWord m 6 (t * u) =
      X m 18 (t * u) *
        X m 19 ((halfFrobenius m t) * (halfFrobenius m u)) *
        X m 20 (t * (halfFrobenius m t) * u * (halfFrobenius m u)) := by
  rw [word_6]
  simp only [map_mul]
  simp only [mul_assoc, mul_left_comm, mul_comm]

/-- The first-eighth right commutator, with all six source factors in order. -/
theorem rootWord_first_eighth_commutator (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 0 t)⁻¹ * (rootWord m 7 u)⁻¹ * rootWord m 0 t * rootWord m 7 u =
      rootWord m 1 ((t ^ 2 * titsEnd m t) * u) *
      (rootWord m 2 ((t * titsEnd m t) * u))⁻¹ *
      rootWord m 3 ((t ^ 2 * titsEnd m t ^ 2) * (u * titsEnd m u)) *
      centralWord m 4 ((t ^ 3 * titsEnd m t ^ 2) * (u ^ 2 * titsEnd m u)) *
      rootWord m 5 ((t ^ 2 * titsEnd m t) * (u * titsEnd m u)) * rootWord m 6 (t * u) := by
  apply commutator_of_swap
  rw [eighth_second, eighth_third, eighth_fourth, eighth_central,
    eighth_sixth, eighth_seventh, word_0, word_7]
  simpa only [mul_assoc] using
    collect_first_eighth m t (halfFrobenius m t) u (halfFrobenius m u)

/-- The first-seventh right commutator, with the inverse third-root factor. -/
theorem rootWord_first_seventh_commutator (m : ℕ) (t u : CoefficientField m) :
    (rootWord m 0 t)⁻¹ * (rootWord m 6 u)⁻¹ * rootWord m 0 t * rootWord m 6 u =
      (rootWord m 2 (titsEnd m t * u))⁻¹ *
      rootWord m 3 ((t * titsEnd m t) * (u * titsEnd m u)) * rootWord m 4 (t * titsEnd m u) := by
  apply commutator_of_swap
  rw [word_0, word_6, word_2, word_3, word_4]
  simp only [mul_inv_rev, xi, map_mul, halfFrobenius_titsEnd]
  simpa only [← halfFrobenius_sq, pow_succ, pow_zero, mul_one,
    mul_assoc, mul_left_comm, mul_comm] using
    collect_first_seventh m t (halfFrobenius m t) u (halfFrobenius m u)

end
end ReeF4.Parabolics.OuterLocal.SuzukiCommutators.NormalGeneration
