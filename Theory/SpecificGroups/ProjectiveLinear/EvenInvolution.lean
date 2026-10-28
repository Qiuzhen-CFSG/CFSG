module

public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.Algebra.CharP.Two

/-!
# Involutions in projective linear groups in characteristic two

An elementary transvection has square one and is not central. Its image in
PSL therefore remains a nonidentity involution in every dimension at least two.
This supplies even-order witnesses without an order formula or simplicity.

Source: the elementary matrix construction underlying Aschbacher--Smith,
*The Classification of Quasithin Groups*, E.1.14(1).
-/

public section
namespace Matrix.ProjectiveSpecialLinearGroup

/-- The image of a transvection is an involution in characteristic two. -/
theorem exists_involution_of_char_two {F : Type*} [Field F] [CharP F 2]
    {n : ℕ} (hn : 2 ≤ n) :
    ∃ x : ProjectiveSpecialLinearGroup (Fin n) F, x ≠ 1 ∧ x ^ 2 = 1 := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  let u := SpecialLinearGroup.transvection hij (1 : F)
  let q := QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin n) F))
  refine ⟨q u, ?_, ?_⟩
  · intro h
    exact one_ne_zero ((SpecialLinearGroup.transvection_mem_center_iff hij (1 : F)).mp
      ((QuotientGroup.eq_one_iff _).mp h))
  · have hu : u ^ 2 = 1 := by
      rw [pow_two, ← SpecialLinearGroup.transvection_add]
      simp [CharTwo.add_self_eq_zero]
    rw [← map_pow, hu, map_one]

end Matrix.ProjectiveSpecialLinearGroup
