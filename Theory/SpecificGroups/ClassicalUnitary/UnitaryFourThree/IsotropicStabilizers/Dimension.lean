module

public import Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry
public import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Dimensions of totally isotropic subspaces over Nine

Conjugation sends a subspace semilinearly to a subspace of the same dimension.
The Hermitian perpendicular is the ordinary dot-product perpendicular of this
conjugate space. Nondegeneracy of the dot product therefore gives the exact
perpendicular dimension and bounds every totally isotropic subspace by half
the ambient dimension. In dimension four, a nonzero such space is a line or
a plane; an isotropic plane equals its perpendicular.

This is the geometric dimension reduction for the unitary stabilizers used in
condition K of Aschbacher–Smith, Theorem 0.1.2(4), printed pp.4 and 482 of
`refs/quasithin.pdf`. The Hermitian conventions are those of GLS3, chapter 2,
section on the classical groups.
-/

open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree
open Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.ReducibleGeometry
open Matrix
open Module
public noncomputable section
namespace Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
variable {n : ℕ}

private def conjugateSpace (W : Submodule FiniteField.Nine (Space n)) :=
  W.map (starLinearEquiv FiniteField.Nine : Space n ≃ₗ⋆[FiniteField.Nine] Space n).toLinearMap

private theorem finrank_conjugateSpace (W : Submodule FiniteField.Nine (Space n)) :
    finrank FiniteField.Nine (conjugateSpace W) = finrank FiniteField.Nine W := by
  let e := (starLinearEquiv FiniteField.Nine : Space n ≃ₗ⋆[FiniteField.Nine] Space n).submoduleMap W
  exact (congrArg Cardinal.toNat
    (rank_eq_of_equiv_equiv (star : FiniteField.Nine → FiniteField.Nine) e.toAddEquiv
      star_involutive.bijective (fun r w => e.map_smulₛₗ r w))).symm

private theorem orthogonal_eq (W : Submodule FiniteField.Nine (Space n)) :
    orthogonal W = LinearMap.BilinForm.orthogonal
      (dotProductBilin FiniteField.Nine FiniteField.Nine :
        LinearMap.BilinForm FiniteField.Nine (Space n)) (conjugateSpace W) := by
  ext v
  constructor
  · intro hv w hw
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw
    exact hv x hx
  · intro hv w hw
    exact hv (star w) (Submodule.mem_map.mpr ⟨w, hw, rfl⟩)

private theorem dotProduct_nondegenerate :
    (dotProductBilin FiniteField.Nine FiniteField.Nine :
      LinearMap.BilinForm FiniteField.Nine (Space n)).Nondegenerate := by
  constructor
  · intro v hv
    exact dotProduct_eq_zero v hv
  · intro v hv
    exact dotProduct_eq_zero v (fun w => by
      simpa only [dotProductBilin, LinearMap.coe_mk, AddHom.coe_mk, dotProduct_comm] using hv w)

/-- The identity Hermitian form is nondegenerate, with the expected perpendicular dimension. -/
theorem finrank_orthogonal (W : Submodule FiniteField.Nine (Space n)) :
    finrank FiniteField.Nine (orthogonal W) = n - finrank FiniteField.Nine W := by
  rw [orthogonal_eq, LinearMap.BilinForm.finrank_orthogonal dotProduct_nondegenerate,
    finrank_conjugateSpace]
  simp [Space]

/-- A totally isotropic space has at most half the ambient dimension. -/
theorem finrank_le_half (W : Submodule FiniteField.Nine (Space n))
    (hW : W ≤ orthogonal W) : 2 * finrank FiniteField.Nine W ≤ n := by
  have h := Submodule.finrank_mono hW
  rw [finrank_orthogonal] at h
  have hb := W.finrank_le
  simp only [Space, Module.finrank_pi, Fintype.card_fin] at hb
  omega

/-- The point and plane cases exhaust all nonzero totally isotropic subspaces. -/
theorem finrank_one_or_two (W : Submodule FiniteField.Nine (Space 4))
    (hW0 : W ≠ ⊥) (hW : W ≤ orthogonal W) :
    finrank FiniteField.Nine W = 1 ∨ finrank FiniteField.Nine W = 2 := by
  have hd := finrank_le_half W hW
  have hn : finrank FiniteField.Nine W ≠ 0 := by
    exact fun h => hW0 (Submodule.finrank_eq_zero.mp h)
  omega

/-- A totally isotropic plane in dimension four is its own perpendicular. -/
theorem plane_eq_orthogonal (W : Submodule FiniteField.Nine (Space 4))
    (hW : W ≤ orthogonal W) (hd : finrank FiniteField.Nine W = 2) :
    W = orthogonal W := by
  apply Submodule.eq_of_le_of_finrank_eq hW
  rw [finrank_orthogonal, hd]

end Theory.SpecificGroups.ClassicalUnitary.UnitaryFourThree.IsotropicStabilizers
