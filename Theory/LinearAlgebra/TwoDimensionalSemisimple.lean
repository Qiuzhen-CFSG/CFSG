module

public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Determinant-one eigenbases in dimension two

A semisimple endomorphism over an algebraically closed field has an eigenbasis
whose change-of-basis matrix has determinant one. Choose a nonzero eigenvector,
then use the eigenspace decomposition to find an eigenvector with nonzero
alternating pairing against it. Rescale the second vector to normalize the
determinant. This supplies a conjugating element in SL₂ when diagonalizing
an actual two-dimensional group action.

The argument uses the eigenspace decomposition from Mathlib's semisimplicity
API and elementary two-dimensional linear algebra.
-/

public section

open Matrix
open scoped MatrixGroups
namespace Module.End
variable {K : Type*} [Field K] [IsAlgClosed K]

theorem exists_specialLinear_eigenbasis_fin_two
    (f : Module.End K (Fin 2 → K)) (hs : f.IsSemisimple) :
    ∃ Q : SL(2, K), ∃ a b : K,
      f ![Q.val 0 0, Q.val 1 0] = a • ![Q.val 0 0, Q.val 1 0] ∧
      f ![Q.val 0 1, Q.val 1 1] = b • ![Q.val 0 1, Q.val 1 1] := by
  classical
  obtain ⟨a, ha⟩ := f.exists_eigenvalue
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp ha
  have hu' : f u = a • u := Module.End.mem_eigenspace_iff.mp hu
  let cross : (Fin 2 → K) →ₗ[K] K :=
    { toFun := fun v => u 0 * v 1 - u 1 * v 0
      map_add' := by intro v w; simp; ring
      map_smul' := by intro r v; simp; ring }
  obtain ⟨b, v, hv, hd⟩ : ∃ b : K, ∃ v : Fin 2 → K,
      f v = b • v ∧ cross v ≠ 0 := by
    by_contra h
    push Not at h
    have hker : (⊤ : Submodule K (Fin 2 → K)) ≤ cross.ker := by
      rw [← hs.iSup_eigenspace_eq_top]
      refine iSup_le fun b => ?_
      intro v hv
      exact h b v (Module.End.mem_eigenspace_iff.mp hv)
    have h0 := hker (Submodule.mem_top : ![0, 1] ∈ (⊤ : Submodule K (Fin 2 → K)))
    have h1 := hker (Submodule.mem_top : ![1, 0] ∈ (⊤ : Submodule K (Fin 2 → K)))
    change cross ![0, 1] = 0 at h0
    change cross ![1, 0] = 0 at h1
    simp only [cross, LinearMap.coe_mk, AddHom.coe_mk, cons_val_zero,
      cons_val_one, mul_one, mul_zero, zero_sub, sub_zero, neg_eq_zero] at h0 h1
    apply hu0
    ext i
    fin_cases i <;> assumption
  let Q : SL(2, K) :=
    ⟨!![u 0, (cross v)⁻¹ * v 0; u 1, (cross v)⁻¹ * v 1], by
      rw [det_fin_two]
      change u 0 * ((cross v)⁻¹ * v 1) - (cross v)⁻¹ * v 0 * u 1 = 1
      calc
        _ = (cross v)⁻¹ * cross v := by dsimp [cross]; ring
        _ = 1 := inv_mul_cancel₀ hd⟩
  refine ⟨Q, a, b, ?_, ?_⟩
  · change f ![u 0, u 1] = a • ![u 0, u 1]
    have he : ![u 0, u 1] = u := by ext i; fin_cases i <;> rfl
    rw [he, hu']
  · change f ![(cross v)⁻¹ * v 0, (cross v)⁻¹ * v 1] =
      b • ![(cross v)⁻¹ * v 0, (cross v)⁻¹ * v 1]
    have he : ![(cross v)⁻¹ * v 0, (cross v)⁻¹ * v 1] = (cross v)⁻¹ • v := by
      ext i; fin_cases i <;> rfl
    rw [he, map_smul, hv, smul_comm]

end Module.End
