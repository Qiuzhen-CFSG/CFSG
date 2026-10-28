module

public import Theory.SpecificGroups.PSL3.LinearThreeFlags

/-!
# Generation by the two standard degree-three parabolics

The stabilizers of the standard point and incident line generate SL₃(F),
and their images generate PSL₃(F). Every elementary transvection except
x₂₀(a) lies in one of these parabolics. The missing transvection is the
commutator of x₂₁(a) and x₁₀(1); diagonal matrices already stabilize the
flag. Gaussian elimination then proves generation over every finite field.

This is the matrix generation input to the PSL₃ case of Aschbacher--Smith,
*The Classification of Quasithin Groups*, E.1.14(1), printed p.214.
It does not assert E-generation or any local quotient calculation.
-/

public section
open Matrix
open scoped MatrixGroups
namespace Matrix.PSL3.LinearThree
variable (F : Type*) [Field F] [Finite F]
omit [Finite F] in
private theorem lower_corner (a : F) :
    SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 0 by decide) a =
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) a *
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) 1 *
      SpecialLinearGroup.transvection (show (2 : Fin 3) ≠ 1 by decide) (-a) *
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 0 by decide) (-1) := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe,
      Matrix.mul_apply, Fin.sum_univ_three, Matrix.one_apply, Matrix.single_apply]

/-- The two actual flag stabilizers generate the special linear group. -/
theorem parabolicsSL_sup_eq_top : pointParabolicSL F ⊔ lineParabolicSL F = ⊤ := by
  apply top_unique
  intro g _
  apply SpecialLinearGroup.diagonal_transvection_induction'
    (fun g => g ∈ pointParabolicSL F ⊔ lineParabolicSL F) g
  · intro i j hij c hc
    apply Subgroup.mem_sup_left
    rw [mem_pointParabolicSL_iff]
    simp [SpecialLinearGroup.diag2n_coe]
  · intro i j hij a
    by_cases hi : i = 2
    · subst i
      by_cases hj : j = 0
      · subst j
        rw [lower_corner]
        apply Subgroup.mul_mem
        · apply Subgroup.mul_mem
          · apply Subgroup.mul_mem
            · apply Subgroup.mem_sup_left
              rw [mem_pointParabolicSL_iff]
              simp [SpecialLinearGroup.transvection_coe]
            · apply Subgroup.mem_sup_right
              rw [mem_lineParabolicSL_iff]
              simp [SpecialLinearGroup.transvection_coe]
          · apply Subgroup.mem_sup_left
            rw [mem_pointParabolicSL_iff]
            simp [SpecialLinearGroup.transvection_coe]
        · apply Subgroup.mem_sup_right
          rw [mem_lineParabolicSL_iff]
          simp [SpecialLinearGroup.transvection_coe]
      · apply Subgroup.mem_sup_left
        rw [mem_pointParabolicSL_iff]
        fin_cases j <;> simp_all [SpecialLinearGroup.transvection_coe]
    · apply Subgroup.mem_sup_right
      rw [mem_lineParabolicSL_iff]
      fin_cases i <;> simp_all [SpecialLinearGroup.transvection_coe]
  · exact fun _ _ => Subgroup.mul_mem _

/-- The two actual projective flag stabilizers generate PSL₃(F). -/
theorem parabolics_sup_eq_top : pointParabolic F ⊔ lineParabolic F = ⊤ := by
  rw [pointParabolic, lineParabolic, ← Subgroup.map_sup, parabolicsSL_sup_eq_top]
  exact Subgroup.map_top_of_surjective _ (projection_surjective F)
end Matrix.PSL3.LinearThree
