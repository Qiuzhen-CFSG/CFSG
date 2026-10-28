module
public import Theory.Representation.OrthogonalFourPlusMatrix.SmallActors

/-!
# Singularity in the full binary tensor normalizer

A binary normalizer element is semilinear over the coefficient field. Pulling
back the determinant and undoing that field automorphism gives a quadratic
form invariant under both special linear factors. The invariant-form theorem
identifies it with a nonzero scalar multiple of the determinant, so every
normalizer element preserves singularity.

For an involution of binary displacement rank at most two, the field-linear
lift is an isometry with a one-dimensional displacement space. Nondegeneracy
of the determinant polarization excludes every nonzero singular vector from
that displacement space.

Source: Aschbacher–Smith 9.1.2 and the singular-center contradiction in
9.4.4–5, combined manuscript of 1 March 2004, printed pp.729,736–737.
-/

public section

open Module Matrix
namespace ClassicalOrthogonal.FourPlusMatrix.Binary

private def transportedForm (t : V ≃ₗ[ZMod 2] V) (σ : F ≃+* F)
    (hσ : ∀ (a : F) (x : V), t (a • x) = σ a • t x) : QuadraticForm F V := by
  let q : V → F := fun x => σ.symm (determinantForm (t x))
  have hp (x y : V) : QuadraticMap.polar q x y =
      σ.symm (QuadraticMap.polar determinantForm (t x) (t y)) := by
    simp only [QuadraticMap.polar, q, map_add, map_sub]
  apply QuadraticMap.ofPolar q
  · intro a x
    dsimp only [q]
    rw [hσ, QuadraticMap.map_smul]
    simp only [smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]
  · intro x y z
    rw [hp, map_add, QuadraticMap.polar_add_left, map_add, hp, hp]
  · intro a x y
    rw [hp, hσ, QuadraticMap.polar_smul_left, hp]
    simp only [smul_eq_mul, map_mul, RingEquiv.symm_apply_apply]

/-- Every element of the full binary tensor normalizer preserves singularity. -/
theorem normalizer_det_zero_iff (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (x : V) : (t x).det = 0 ↔ x.det = 0 := by
  obtain ⟨σ,hσ⟩ := normalizer_semilinear t ht
  let q := transportedForm t σ hσ
  have hq (g : G) (M : V) : q (matrixAction g M) = q M := by
    obtain ⟨h,hh⟩ := (Subgroup.mem_normalizer_iff.mp ht (linearAction g)).mp ⟨g,rfl⟩
    have he (N : V) : t (action g N) = action h (t N) := by
      have hi := LinearEquiv.congr_fun hh (t N)
      simpa using hi.symm
    change σ.symm (determinantForm (t (action g M))) =
      σ.symm (determinantForm (t M))
    rw [he, determinantForm_apply, determinantForm_apply]
    exact congrArg σ.symm (matrixAction_det h (t M))
  obtain ⟨c,hc⟩ := invariant_quadratic_eq_det (QuadraticAlgebra.omega : F)
    (by decide +kernel) (by decide +kernel) q hq
  have hc' (M : V) : σ.symm ((t M).det) = c * M.det := by
    simpa only [q, transportedForm, QuadraticMap.ofPolar, QuadraticMap.coe_mk, determinantForm_apply] using hc M
  have hcn : c ≠ 0 := by
    intro hz
    have hh := hc' (t.symm 1)
    rw [LinearEquiv.apply_symm_apply, Matrix.det_one, map_one, hz, zero_mul] at hh
    exact one_ne_zero hh
  rw [← σ.symm.map_eq_zero_iff, hc', mul_eq_zero]
  exact or_iff_right hcn

/-- A low-rank involution cannot move a nonzero singular vector. -/
theorem low_rank_involution_singular_not_mem_displacement (t : V ≃ₗ[ZMod 2] V)
    (ht : t ∈ Subgroup.normalizer (linearAction.range : Set (V ≃ₗ[ZMod 2] V)))
    (hr : finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) ≤ 2)
    (ht2 : t ^ 2 = 1) (s : V) (hs : s ≠ 0) (hsd : s.det = 0) :
    s ∉ LinearMap.range (t.toLinearMap - LinearMap.id) := by
  obtain ⟨u,hu⟩ := low_rank_field_equiv t ht hr
  have hu2 (v : V) : u (u v) = v := by
    have hh := LinearEquiv.congr_fun ht2 v
    change t (t v) = v at hh
    simpa only [← hu, LinearEquiv.restrictScalars_apply] using hh
  have hdet := field_involution_preserves_det u (by rwa [hu]) hu2
  have hh := QuadraticForm.singular_not_mem_displacement_degree_two finrank_field
    determinantForm determinant_polar_separating u
      (by simpa only [determinantForm_apply] using hdet) (by rwa [hu]) s hs (by simpa only [determinantForm_apply] using hsd)
  rwa [hu] at hh

end ClassicalOrthogonal.FourPlusMatrix.Binary
