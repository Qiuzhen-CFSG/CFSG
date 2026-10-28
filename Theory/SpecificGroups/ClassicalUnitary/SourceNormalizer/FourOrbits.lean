module
public import Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourSingularity
public import Theory.Representation.OrthogonalFourMinusFirstCohomology.FiniteModel.Geometry

/-!
# Determinant fibers of the unitary-four residual action

Every nonzero Hermitian two-by-two matrix is carried by an actual SL₂
matrix to diag(1, det X). A nonfixed field element first produces a
nonzero diagonal entry; a lower transvection removes the off-diagonal
entry, and a fixed-field square root normalizes the leading entry.
Consequently the nonzero residual orbits are exactly determinant fibers.
This retains all field parameters, including the smallest quadratic field.

These are the native orbit calculations for Aschbacher–Smith F.4.35,
printed p.292 of `refs/quasithin.pdf`. Fusion of distinct nonzero
values uses the larger parabolic torus separately.
-/

@[expose] public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOrbits
open Matrix Matrix.SpecialLinearGroup
open Representation.OrthogonalFourMinus Representation.OrthogonalFourMinus.FiniteModel
open Representation.OrthogonalFourMinus.CartanFixed
variable (m : ℕ) [NeZero m]

private theorem nonzero_leading (X : Space m) (hX : X ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 2) (Field m), (action m g X).val 0 0 ≠ 0 := by
  by_cases ha : X.val 0 0 = 0
  · by_cases hb : X.val 1 1 = 0
    · have hz : X.val 0 1 ≠ 0 := by
        intro hz
        apply hX
        apply Subtype.ext
        ext i j
        fin_cases i <;> fin_cases j <;> simp [ha,hb,hz,←entry_conjugate m X 1 0]
      obtain ⟨t,ht⟩ := exists_conjugation_ne m
      let u := X.val 0 1 * t
      refine ⟨transvection (show (0:Fin 2) ≠ 1 by decide) u,?_⟩
      have he : (action m (transvection (show (0:Fin 2) ≠ 1 by decide) u) X).val 0 0 =
          X.val 0 1 * conjugation m (X.val 0 1) * (t + conjugation m t) := by
        rw [action_apply]
        simp [transvection_coe,adjoint,Matrix.mul_apply,Fin.sum_univ_two,ha,hb,
          u,←entry_conjugate m X 1 0]
        ring
      rw [he]
      apply mul_ne_zero (mul_ne_zero hz (by simpa using hz))
      intro hh
      apply ht
      exact (eq_neg_of_add_eq_zero_right hh).trans (CharTwo.neg_eq _)
    · let g : SpecialLinearGroup (Fin 2) (Field m) :=
        ⟨!![0,1;1,0],by simp [Matrix.det_fin_two,CharTwo.neg_eq]⟩
      refine ⟨g,?_⟩
      have he : (action m g X).val 0 0 = X.val 1 1 := by
        rw [action_apply]
        simp [g,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,Fin.sum_univ_two]
      rwa [he]
  · exact ⟨1,by simpa using ha⟩

/-- The canonical nonzero vector of prescribed Hermitian determinant. -/
def representative (c : fixedField m) : Space m := (coordinates m).symm ((1,c),0)

theorem representative_form (c : fixedField m) : form m (representative m c) = c := by
  rw [representative,form_coordinates]
  apply Subtype.ext
  simp [FiniteModel.norm]

theorem representative_ne_zero (c : fixedField m) : representative m c ≠ 0 := by
  intro he
  have hh := congrArg (fun X : Space m => X.val 0 0) he
  exact one_ne_zero hh

private theorem normalize_leading (X : Space m) (ha : X.val 0 0 ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 2) (Field m),
      action m g X = representative m (form m X) := by
  let a : fixedField m := ⟨X.val 0 0,entry_fixed m X 0⟩
  have ha0 : a ≠ 0 := fun he => ha (congrArg Subtype.val he)
  obtain ⟨s,hs⟩ := (frobeniusEquiv (fixedField m) 2).surjective a⁻¹
  have hs2 : s^2 = a⁻¹ := hs
  have hs0 : s ≠ 0 := by
    intro he
    have he' : a⁻¹ = 0 := by simpa [he] using hs2.symm
    exact (inv_ne_zero ha0) he'
  have hsf : (s : Field m) ≠ 0 := Subtype.coe_ne_coe.mpr hs0
  have hsfix : conjugation m (s : Field m) = s := s.property
  have hsval : (s : Field m) * s * X.val 0 0 = 1 := by
    have hh := congrArg Subtype.val hs2
    change (s : Field m)^2 = (X.val 0 0)⁻¹ at hh
    rw [←pow_two,hh,inv_mul_cancel₀ ha]
  let u := X.val 1 0 / X.val 0 0
  let k := transvection (show (1:Fin 2) ≠ 0 by decide) u
  let g := diagonal m (Units.mk0 (s : Field m) hsf) * k
  let Y := action m g X
  have hY00 : Y.val 0 0 = 1 := by
    change (action m (diagonal m (Units.mk0 (s : Field m) hsf) * k) X).val 0 0 = 1
    rw [map_mul,Module.End.mul_apply,action_apply,action_apply]
    simpa [Representation.OrthogonalFourMinus.CartanFixed.diagonal,diag2_coe',k,transvection_coe,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,
      Fin.sum_univ_two,hsfix,mul_assoc,mul_comm,mul_left_comm] using hsval
  have huc : conjugation m u = X.val 0 1 / X.val 0 0 := by
    simp only [u,map_div₀,entry_conjugate]
  have hz : X.val 0 0 * conjugation m u + X.val 0 1 = 0 := by
    rw [huc,mul_div_cancel₀ _ ha,CharTwo.add_self_eq_zero]
  have hY01 : Y.val 0 1 = 0 := by
    change (action m (diagonal m (Units.mk0 (s : Field m) hsf) * k) X).val 0 1 = 0
    rw [map_mul,Module.End.mul_apply,action_apply,action_apply]
    simp [Representation.OrthogonalFourMinus.CartanFixed.diagonal,diag2_coe',k,transvection_coe,adjoint,Matrix.mul_apply,Matrix.vecMul,dotProduct,
      Fin.sum_univ_two,hsfix,hz]
  have hY10 : Y.val 1 0 = 0 := by rw [←entry_conjugate m Y 1 0,hY01,map_zero]
  have hY11 : Y.val 1 1 = (form m X : Field m) := by
    have he := congrArg Subtype.val (form_preserved m g X)
    change Y.val.det = (form m X : Field m) at he
    simpa [Matrix.det_fin_two,hY00,hY01,hY10] using he
  refine ⟨g,?_⟩
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [←show Y = action m g X from rfl,representative,coordinates_symm_val,hY00,hY01,hY10,hY11]

/-- Every nonzero Hermitian vector is conjugate to its determinant representative. -/
theorem normalize (X : Space m) (hX : X ≠ 0) :
    ∃ g : SpecialLinearGroup (Fin 2) (Field m),
      action m g X = representative m (form m X) := by
  obtain ⟨g,hg⟩ := nonzero_leading m X hX
  obtain ⟨k,hk⟩ := normalize_leading m (action m g X) hg
  refine ⟨k*g,?_⟩
  rw [map_mul,Module.End.mul_apply,hk,form_preserved]

/-- The residual SL₂-orbits on nonzero core vectors are exactly determinant fibers. -/
theorem orbit_iff (X Y : Space m) (hX : X ≠ 0) (hY : Y ≠ 0) :
    (∃ g : SpecialLinearGroup (Fin 2) (Field m), action m g X = Y) ↔
      form m X = form m Y := by
  constructor
  · rintro ⟨g,rfl⟩
    exact (form_preserved m g X).symm
  · intro he
    obtain ⟨g,hg⟩ := normalize m X hX
    obtain ⟨k,hk⟩ := normalize m Y hY
    refine ⟨k⁻¹*g,?_⟩
    rw [map_mul,Module.End.mul_apply,hg,he,←hk]
    exact Representation.inv_self_apply _ _ _

end Theory.SpecificGroups.ClassicalUnitary.SourceNormalizer.FourOrbits
