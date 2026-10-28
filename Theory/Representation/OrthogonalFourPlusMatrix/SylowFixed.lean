module

public import Theory.Representation.OrthogonalFourPlusMatrix.Binary
public import Theory.SpecificGroups.SL2.UpperUnipotent

/-!
# Singular fixed vectors of determinant-group Sylow subgroups

Extend the upper unipotents of the first SL₂ factor to a Sylow subgroup,
then conjugate it to the specified Sylow subgroup. A fixed matrix for the
upper transvection has zero second row, hence zero determinant. The
left-right action preserves that determinant under the conjugation transport.

This supplies the singular F₄-point containing the actual Sylow-fixed line
in Aschbacher--Smith 14.4.6(b), combined manuscript (1 March 2004), p.1008.
-/

public section
namespace ClassicalOrthogonal.FourPlusMatrix.Binary
open Matrix
open scoped Pointwise

private theorem det_eq_zero_of_upper_fixed (M : V)
    (hM : action (SpecialLinearGroup.transvection zero_ne_one (1 : F), 1) M = M) :
    M.det = 0 := by
  change (SpecialLinearGroup.transvection zero_ne_one (1 : F)).val * M *
    (1 : SpecialLinearGroup (Fin 2) F)⁻¹.val = M at hM
  simp only [inv_one] at hM
  change (SpecialLinearGroup.transvection zero_ne_one (1 : F)).val * M * (1 : V) = M at hM
  rw [mul_one] at hM
  have hz (j : Fin 2) : M 1 j = 0 := by
    have h := congrArg (fun N : V => N 0 j) hM
    simpa [SpecialLinearGroup.transvection_coe, Matrix.mul_apply,
      Fin.sum_univ_two] using h
  simp [Matrix.det_fin_two, hz]

/-- Every vector fixed by a Sylow two-subgroup of the determinant group is singular. -/
theorem sylow_fixed_singular (P : Sylow 2 G) (M : V)
    (hM : ∀ g ∈ P, action g M = M) : M.det = 0 := by
  let S := SpecialLinearGroup.upperUnipotentSylow F 2
  let i : SpecialLinearGroup (Fin 2) F →* G := MonoidHom.inl _ _
  obtain ⟨Q, hQ⟩ := (S.isPGroup'.map i).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G Q P
  let u : G := (SpecialLinearGroup.transvection zero_ne_one (1 : F), 1)
  have hu : u ∈ Q := by
    apply hQ
    refine ⟨SpecialLinearGroup.transvection zero_ne_one (1 : F), ?_, rfl⟩
    exact ⟨Multiplicative.ofAdd 1, rfl⟩
  have hconj : g * u * g⁻¹ ∈ P := by
    rw [← hg]
    change g * u * g⁻¹ ∈ MulAut.conj g • (Q : Set G)
    exact ⟨u, hu, rfl⟩
  have hfix : action u (action g⁻¹ M) = action g⁻¹ M := by
    have hm (x y : G) (N : V) : action (x * y) N = action x (action y N) :=
      congrArg (fun f : Module.End (ZMod 2) V => f N) (action.map_mul x y)
    calc
      action u (action g⁻¹ M) = action (u * g⁻¹) M := (hm u g⁻¹ M).symm
      _ = action (g⁻¹ * (g * u * g⁻¹)) M := by rw [mul_assoc g u g⁻¹, inv_mul_cancel_left]
      _ = action g⁻¹ (action (g * u * g⁻¹) M) := hm _ _ _
      _ = action g⁻¹ M := congrArg (action g⁻¹) (hM _ hconj)
  have hz := det_eq_zero_of_upper_fixed (action g⁻¹ M) hfix
  have he : (action g⁻¹ M).det = M.det := matrixAction_det g⁻¹ M
  exact he.symm.trans hz
end ClassicalOrthogonal.FourPlusMatrix.Binary
