module

public import Theory.SpecificGroups.ProjectiveLinear.EvenInvolution
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Tactic
/-!
# An element of order four in binary PSL3

The three-by-three unipotent Jordan matrix squares to a noncentral
transvection and has fourth power one. Its projective image therefore
has order four over every field of characteristic two. This directly
excludes an elementary Sylow two-subgroup, including the PSL3(2) endpoint.

Source application: Aschbacher--Smith F.6.17, printed p.309.
-/

public section
open Subgroup
namespace Matrix.ProjectiveSpecialLinearGroup
open scoped MatrixGroups
theorem exists_order_four_of_char_two {F : Type*} [Field F] [CharP F 2] :
    ∃ x : PSL(3,F), orderOf x = 4 := by
  let a : SL(3,F) := ⟨!![1,1,0;0,1,1;0,0,1], by simp [Matrix.det_fin_three]⟩
  let u : SL(3,F) := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) (1 : F)
  have ha : a ^ 2 = u := by
    apply Subtype.ext
    change (!![1,1,0;0,1,1;0,0,1] : Matrix (Fin 3) (Fin 3) F) ^ 2 = Matrix.transvection 0 2 1
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [pow_two, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.transvection,
        CharTwo.add_self_eq_zero]
  have hu : u ^ 2 = 1 := by
    dsimp only [u]
    rw [pow_two, ← Matrix.SpecialLinearGroup.transvection_add]
    simp [CharTwo.add_self_eq_zero]
  let q := QuotientGroup.mk' (center SL(3,F))
  have h4 : (q a) ^ 4 = 1 := by
    rw [← map_pow, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, ha, hu, map_one]
  have h2 : (q a) ^ 2 ≠ 1 := by
    intro hh
    rw [← map_pow, ha] at hh
    exact one_ne_zero ((Matrix.SpecialLinearGroup.transvection_mem_center_iff
      (by decide : (0 : Fin 3) ≠ 2) (1 : F)).mp ((QuotientGroup.eq_one_iff _).mp hh))
  refine ⟨q a, ?_⟩
  have hd := orderOf_dvd_of_pow_eq_one h4
  have hn : ¬ orderOf (q a) ∣ 2 := fun hh => h2 (orderOf_dvd_iff_pow_eq_one.mp hh)
  have hle := Nat.le_of_dvd (by decide : 0 < 4) hd
  interval_cases ho : orderOf (q a) <;> norm_num [ho] at *
end Matrix.ProjectiveSpecialLinearGroup
