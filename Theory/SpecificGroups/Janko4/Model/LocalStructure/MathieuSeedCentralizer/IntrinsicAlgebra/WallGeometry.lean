module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.WallGeometry.Geometry
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Action
public import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# The intrinsic Wall form of the literal seed

The certified adapted coordinates identify the actual kernel with the image
of the square-zero displacement. The kernel is totally isotropic for the
ambient invariant form. Consequently `B(x, N y)` depends only on `N x` and
`N y` and defines a bilinear form on that kernel. Its matrix in the prescribed
basis is the symmetric invertible `wallMatrix`. Preservation by the full
centralizer follows from preservation of `B` and commutation with `N`.

Source: the intrinsic construction in
`IntrinsicAlgebra/source/README.md` and the witness exploration described
there; the numerical premises are proved in `WallGeometry.Certificates`.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

private theorem form_block (r s : Fin 56 → Fin 112) :
    (adaptedMatrix.submatrix id r)ᵀ * invariantForm * adaptedMatrix.submatrix id s =
      (adaptedMatrixᵀ * invariantForm * adaptedMatrix).submatrix r s := by
  rw [Matrix.transpose_submatrix]
  have h := Matrix.submatrix_mul adaptedMatrixᵀ invariantForm r id id Function.bijective_id
  simp only [Matrix.submatrix_id_id] at h
  rw [← h, ← Matrix.submatrix_mul _ _ r id s Function.bijective_id]

/-- The actual kernel is totally isotropic for the ambient invariant form. -/
theorem kernelColumns_invariantForm :
    kernelColumnsᵀ * invariantForm * kernelColumns = 0 := by
  rw [kernelColumns, form_block, adapted_form_topLeft]

/-- This upper-right block is the saved matrix from the witness. -/
theorem kernelColumns_invariantForm_liftColumns :
    kernelColumnsᵀ * invariantForm * liftColumns = wallMatrix := by
  rw [kernelColumns, liftColumns, form_block, adapted_form_topRight]

/-- This lower-left block gives the defining Wall pairing `B(x, N y)`. -/
theorem liftColumns_invariantForm_kernelColumns :
    liftColumnsᵀ * invariantForm * kernelColumns = wallMatrix := by
  rw [kernelColumns, liftColumns, form_block, adapted_form_bottomLeft]

private theorem pairing_transport (A B : Matrix (Fin 112) (Fin 56) (ZMod 2))
    (a b : SmallColumn) :
    dotProduct (A *ᵥ a) (invariantForm *ᵥ (B *ᵥ b)) =
      dotProduct a ((Aᵀ * invariantForm * B) *ᵥ b) := by
  rw [dotProduct_comm (A *ᵥ a), ← Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

/-- The symmetric Wall form on the actual displacement kernel. -/
noncomputable def beta : LinearMap.BilinForm (ZMod 2) kernelSpace :=
  wallMatrix.toBilin'.comp kernelCoordEquiv.symm.toLinearMap kernelCoordEquiv.symm.toLinearMap

/-- Exact coordinates in the unchanged literal kernel basis. -/
@[simp] theorem beta_kernelCoordEquiv (a b : SmallColumn) :
    beta (kernelCoordEquiv a) (kernelCoordEquiv b) = dotProduct a (wallMatrix *ᵥ b) := by
  simp only [beta, LinearMap.BilinForm.comp_apply, LinearEquiv.coe_coe,
    kernelCoordEquiv.symm_apply_apply, Matrix.toBilin'_apply']

theorem beta_eq_lift_pairing (v w : kernelSpace) :
    beta v w = dotProduct (kernelLift v) (invariantForm *ᵥ (w : Column)) := by
  obtain ⟨a, rfl⟩ := kernelCoordEquiv.surjective v
  obtain ⟨b, rfl⟩ := kernelCoordEquiv.surjective w
  rw [beta_kernelCoordEquiv, kernelLift_coord, kernelCoordEquiv_apply,
    pairing_transport, liftColumns_invariantForm_kernelColumns]

theorem kernelSpace_isotropic (v w : kernelSpace) :
    dotProduct (v : Column) (invariantForm *ᵥ (w : Column)) = 0 := by
  obtain ⟨a, rfl⟩ := kernelCoordEquiv.surjective v
  obtain ⟨b, rfl⟩ := kernelCoordEquiv.surjective w
  rw [kernelCoordEquiv_apply, kernelCoordEquiv_apply, pairing_transport,
    kernelColumns_invariantForm, Matrix.zero_mulVec, dotProduct_zero]

/-- The Wall pairing is independent of which preimages under `N` are used. -/
theorem beta_displacement (x y : Column) :
    beta (displacementToKernel x) (displacementToKernel y) =
      dotProduct x (invariantForm *ᵥ (displacementMatrix *ᵥ y)) := by
  rw [beta_eq_lift_pairing]
  have hk : x - kernelLift (displacementToKernel x) ∈ kernelSpace := by
    change displacement (x - kernelLift (displacementToKernel x)) = 0
    rw [map_sub, displacement_kernelLift, displacementToKernel_apply, sub_self]
  have h := kernelSpace_isotropic ⟨_, hk⟩ (displacementToKernel y)
  change dotProduct (x - kernelLift (displacementToKernel x))
    (invariantForm *ᵥ (displacementMatrix *ᵥ y)) = 0 at h
  rw [sub_dotProduct, sub_eq_zero] at h
  exact h.symm

theorem beta_isSymm : beta.IsSymm := by
  refine ⟨fun v w => ?_⟩
  obtain ⟨a, rfl⟩ := kernelCoordEquiv.surjective v
  obtain ⟨b, rfl⟩ := kernelCoordEquiv.surjective w
  rw [beta_kernelCoordEquiv, beta_kernelCoordEquiv,
    ← wallMatrix_transpose, Matrix.dotProduct_transpose_mulVec, wallMatrix_transpose]

theorem wallMatrix_nondegenerate : wallMatrix.Nondegenerate := by
  rw [Matrix.nondegenerate_iff_forall_vecMul_and_mulVec_eq_zero]
  constructor
  · intro v hv
    have h := congrArg (fun w => w ᵥ* wallInverse) hv
    simpa only [Matrix.vecMul_vecMul, wallMatrix_mul_wallInverse,
      Matrix.vecMul_one, Matrix.zero_vecMul] using h
  · intro v hv
    have h := congrArg (fun w => wallInverse *ᵥ w) hv
    simpa only [Matrix.mulVec_mulVec, wallInverse_mul_wallMatrix,
      Matrix.one_mulVec, Matrix.mulVec_zero] using h

theorem beta_nondegenerate : beta.Nondegenerate := by
  constructor
  · intro v hv
    obtain ⟨a, rfl⟩ := kernelCoordEquiv.surjective v
    have ha : a = 0 := wallMatrix_nondegenerate.toBilin'.1 a (by
      intro b
      simpa only [Matrix.toBilin'_apply', beta_kernelCoordEquiv] using hv (kernelCoordEquiv b))
    simp only [ha, map_zero]
  · intro v hv
    obtain ⟨b, rfl⟩ := kernelCoordEquiv.surjective v
    have hb : b = 0 := wallMatrix_nondegenerate.toBilin'.2 b (by
      intro a
      simpa only [Matrix.toBilin'_apply', beta_kernelCoordEquiv] using hv (kernelCoordEquiv a))
    simp only [hb, map_zero]

theorem kernelAction_displacementToKernel (c : centralizer) (x : Column) :
    (kernelAction c : Module.End (ZMod 2) kernelSpace) (displacementToKernel x) =
      displacementToKernel ((centralizerUnit c : BinaryMatrix) *ᵥ x) := by
  apply Subtype.ext
  rw [kernelAction_apply, displacementToKernel_apply, displacementToKernel_apply]
  change (centralizerUnit c : BinaryMatrix) *ᵥ (displacementMatrix *ᵥ x) =
    displacementMatrix *ᵥ ((centralizerUnit c : BinaryMatrix) *ᵥ x)
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, centralizer_commutes_displacement]

/-- The existing action of the full seed centralizer preserves the Wall form. -/
theorem kernelAction_preserves_beta (c : centralizer) (v w : kernelSpace) :
    beta ((kernelAction c : Module.End (ZMod 2) kernelSpace) v)
      ((kernelAction c : Module.End (ZMod 2) kernelSpace) w) = beta v w := by
  obtain ⟨x, rfl⟩ := displacementToKernel_surjective v
  obtain ⟨y, rfl⟩ := displacementToKernel_surjective w
  rw [kernelAction_displacementToKernel, kernelAction_displacementToKernel,
    beta_displacement, beta_displacement]
  have hF : (centralizerUnit c : BinaryMatrix)ᵀ * invariantForm *
      (centralizerUnit c : BinaryMatrix) = invariantForm :=
    model_preserves_invariantForm c
  rw [Matrix.mulVec_mulVec y displacementMatrix (centralizerUnit c : BinaryMatrix),
    centralizer_commutes_displacement,
    ← Matrix.mulVec_mulVec]
  rw [dotProduct_comm ((centralizerUnit c : BinaryMatrix) *ᵥ x),
    ← Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hF]

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
