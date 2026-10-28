module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.WallGeometry
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.CoordinateAction
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Multiplication.Structure

/-!
# Full-centralizer action on the Wall-adjoint operator space

The exhaustive radical certificate and the kernel geometry give the literal
basis of the intrinsic ten-dimensional form space. Inverse pullback defines
`rho` on the full seed centralizer. Descent along the displacement is independent
of lifts; preservation of the Wall pairing then identifies this form action
with conjugation on its adjoint operators. The kernel therefore centralizes
each operator pointwise. The cyclic commutant theorem places its restriction
in the exact saved algebra, without asserting an order bound.

All coordinates retain `IntrinsicAlgebra/source/README.md` conventions. The
matrix construction motivated by GLS3 Table 5.3i (2B), rather than that table
or a centralizer identification, supplies the mathematical inputs.
-/

@[expose] public section
set_option maxRecDepth 2048
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
attribute [local irreducible] kernelCoordEquiv kernelAction radicalAction
  adaptedMatrix adaptedInverse wallMatrix wallInverse kernelColumns liftColumns
  ambientRadicalForm operator seed displacementMatrix centralizer

noncomputable def kernelMatrixAction : centralizer →* SmallMatrixˣ :=
  (Units.map ((kernelCoordEquiv.symm.conjAlgEquiv (ZMod 2)).trans
    LinearMap.toMatrixAlgEquiv').toMonoidHom).comp kernelAction

theorem kernelMatrixAction_mulVec (c : centralizer) (v : SmallColumn) :
    (kernelMatrixAction c : SmallMatrix) *ᵥ v =
      kernelCoordEquiv.symm ((kernelAction c : Module.End (ZMod 2) kernelSpace)
        (kernelCoordEquiv v)) := by
  change Matrix.toLinAlgEquiv' (LinearMap.toMatrixAlgEquiv'
    ((kernelCoordEquiv.symm.conjAlgEquiv (ZMod 2))
      (kernelAction c : Module.End (ZMod 2) kernelSpace))) v = _
  rw [Matrix.toLinAlgEquiv'_toMatrixAlgEquiv']
  rfl

theorem kernelMatrixAction_coord (c : centralizer) (v : SmallColumn) :
    kernelCoordEquiv ((kernelMatrixAction c : SmallMatrix) *ᵥ v) =
      (kernelAction c : Module.End (ZMod 2) kernelSpace) (kernelCoordEquiv v) := by
  rw [kernelMatrixAction_mulVec, kernelCoordEquiv.apply_symm_apply]

private theorem block_product (A B D : BinaryMatrix) (r s : Fin 56 → Fin 112) :
    (A * B * D).submatrix r s = A.submatrix r id * B * D.submatrix id s := by
  have h := Matrix.submatrix_mul A B r id id Function.bijective_id
  simp only [Matrix.submatrix_id_id] at h
  rw [Matrix.submatrix_mul _ _ r id s Function.bijective_id, h]

private theorem restrictionBlock_eq (g : BinaryMatrix) :
    restrictionBlock g = kernelCoordinateMatrix * g * kernelColumns := by
  unfold restrictionBlock kernelCoordinateMatrix kernelColumns
  exact block_product adaptedInverse g adaptedMatrix firstIndex firstIndex

theorem kernelMatrixAction_eq_restrictionBlock (c : centralizer) :
    (kernelMatrixAction c : SmallMatrix) = restrictionBlock (toMatrix (c : Model)) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [kernelMatrixAction_mulVec, kernelCoordEquiv_symm_apply, kernelAction_apply,
    kernelCoordEquiv_apply, restrictionBlock_eq]
  simp only [← Matrix.mulVec_mulVec]
  rfl
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

noncomputable def intrinsicBasis : Module.Basis (Fin 10) (ZMod 2) radicalForms :=
  radicalBasis kernelSpace_eq_range_kernelColumns

theorem intrinsicBasis_apply (i : Fin 10) :
    (intrinsicBasis i : BinaryMatrix) = ambientRadicalForm i :=
  radicalBasis_apply _ i

noncomputable def rho : centralizer →* TenMatrixˣ := radicalMatrixAction intrinsicBasis

attribute [local irreducible] intrinsicBasis

noncomputable def radicalCoordinates : (Fin 10 → ZMod 2) ≃ₗ[ZMod 2] radicalForms :=
  intrinsicBasis.equivFun.symm

theorem radicalCoordinates_apply (v : Fin 10 → ZMod 2) :
    (radicalCoordinates v : BinaryMatrix) = ∑ i, v i • ambientRadicalForm i := by
  simp only [radicalCoordinates, Module.Basis.equivFun_symm_apply, Submodule.coe_sum,
    Submodule.coe_smul, intrinsicBasis_apply]

theorem rho_coordinates (c : centralizer) (v : Fin 10 → ZMod 2) :
    radicalCoordinates ((rho c : TenMatrix) *ᵥ v) =
      (radicalAction c : Module.End (ZMod 2) radicalForms) (radicalCoordinates v) := by
  apply intrinsicBasis.equivFun.injective
  have h := radicalMatrixAction_mulVec intrinsicBasis c (radicalCoordinates v)
  simpa only [rho, radicalCoordinates, LinearEquiv.apply_symm_apply,
    ← Module.Basis.equivFun_apply] using h

/-- Descent of a radical form along the displacement, using a specified lift. -/
noncomputable def descendedPairing (R : radicalForms) (v w : kernelSpace) : ZMod 2 :=
  dotProduct (kernelLift v) ((R : BinaryMatrix) *ᵥ kernelLift w)

private theorem lift_difference_mem (x : Column) :
    x - kernelLift (displacementToKernel x) ∈ kernelSpace := by
  change displacement (x - kernelLift (displacementToKernel x)) = 0
  rw [map_sub, displacement_kernelLift, displacementToKernel_apply, sub_self]

theorem descendedPairing_displacement (R : radicalForms) (x y : Column) :
    descendedPairing R (displacementToKernel x) (displacementToKernel y) =
      dotProduct x ((R : BinaryMatrix) *ᵥ y) := by
  have hy := R.property.2 _ (lift_difference_mem y)
  rw [Matrix.mulVec_sub, sub_eq_zero] at hy
  have hx := R.property.2 _ (lift_difference_mem x)
  have hl : dotProduct (x - kernelLift (displacementToKernel x))
      ((R : BinaryMatrix) *ᵥ kernelLift (displacementToKernel y)) = 0 := by
    rw [← Matrix.dotProduct_transpose_mulVec, ambientForms_transpose R.property.1, hx,
      dotProduct_zero]
  rw [sub_dotProduct, sub_eq_zero] at hl
  rw [descendedPairing, ← hl, ← hy]

private theorem matrix_pairing_pullback {m n : Type*} [Fintype m] [Fintype n]
    (g : Matrix m n (ZMod 2)) (R : Matrix m m (ZMod 2)) (x y : n → ZMod 2) :
    dotProduct (g *ᵥ x) (R *ᵥ (g *ᵥ y)) =
      dotProduct x ((gᵀ * R * g) *ᵥ y) := by
  rw [dotProduct_comm (g *ᵥ x), ← Matrix.dotProduct_transpose_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

private theorem unit_pairing_inverse_pullback (g : BinaryMatrixˣ) (R : BinaryMatrix)
    (x y : Column) :
    dotProduct ((g : BinaryMatrix) *ᵥ x)
      (formPullback g⁻¹ R *ᵥ ((g : BinaryMatrix) *ᵥ y)) =
      dotProduct x (R *ᵥ y) := by
  rw [formPullback, ← matrix_pairing_pullback]
  simp only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

theorem descendedPairing_action (c : centralizer) (R : radicalForms) (v w : kernelSpace) :
    descendedPairing ((radicalAction c : Module.End (ZMod 2) radicalForms) R)
      ((kernelAction c : Module.End (ZMod 2) kernelSpace) v)
      ((kernelAction c : Module.End (ZMod 2) kernelSpace) w) = descendedPairing R v w := by
  obtain ⟨x, rfl⟩ := displacementToKernel_surjective v
  obtain ⟨y, rfl⟩ := displacementToKernel_surjective w
  rw [kernelAction_displacementToKernel, kernelAction_displacementToKernel,
    descendedPairing_displacement, descendedPairing_displacement, radicalAction_apply]
  exact unit_pairing_inverse_pullback (centralizerUnit c) (R : BinaryMatrix) x y

/-- The Wall-adjoint operator of a descended radical form. -/
noncomputable def adjointMatrix : radicalForms →ₗ[ZMod 2] SmallMatrix where
  toFun R := wallInverse * (liftColumnsᵀ * (R : BinaryMatrix) * liftColumns)
  map_add' := by intro R S; simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' := by intro a R; simp

theorem adjointMatrix_pairing (R : radicalForms) (a b : SmallColumn) :
    beta (kernelCoordEquiv a) (kernelCoordEquiv (adjointMatrix R *ᵥ b)) =
      descendedPairing R (kernelCoordEquiv a) (kernelCoordEquiv b) := by
  rw [beta_kernelCoordEquiv, descendedPairing, kernelLift_coord, kernelLift_coord,
    matrix_pairing_pullback]
  change dotProduct a (wallMatrix *ᵥ ((wallInverse * (liftColumnsᵀ * (R : BinaryMatrix) * liftColumns)) *ᵥ b)) = _
  rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, wallMatrix_mul_wallInverse, one_mul]

theorem adjointMatrix_basis (i : Fin 10) : adjointMatrix (intrinsicBasis i) = operator i := by
  change wallInverse * (liftColumnsᵀ * (intrinsicBasis i : BinaryMatrix) * liftColumns) = _
  rw [intrinsicBasis_apply]
  have h : liftColumnsᵀ * ambientRadicalForm i * liftColumns = descendedRadicalForm i := by
    rw [liftColumns, Matrix.transpose_submatrix]
    have h := Matrix.submatrix_mul adaptedMatrixᵀ (ambientRadicalForm i) secondIndex id id Function.bijective_id
    simp only [Matrix.submatrix_id_id] at h
    rw [← h]
    rw [← Matrix.submatrix_mul _ _ secondIndex id secondIndex Function.bijective_id]
    exact ambientRadicalForm_pullback_second_second i
  rw [h, ← wallMatrix_mul_operator, ← Matrix.mul_assoc, wallInverse_mul_wallMatrix, one_mul]

/-- Linear combination in the exact ten-operator basis. -/
noncomputable def op : (Fin 10 → ZMod 2) →ₗ[ZMod 2] SmallMatrix :=
  adjointMatrix.comp radicalCoordinates.toLinearMap

theorem op_apply (v : Fin 10 → ZMod 2) : op v = ∑ i, v i • operator i := by
  change adjointMatrix (intrinsicBasis.equivFun.symm v) = _
  simp only [Module.Basis.equivFun_symm_apply, map_sum, map_smul, adjointMatrix_basis]

@[simp] theorem op_single (i : Fin 10) : op (Pi.single i 1) = operator i := by
  simp [op_apply, Pi.single_apply]


/-- Adjoint equivariance, with pointwise intertwining rather than just normalization. -/
theorem adjointMatrix_intertwines (c : centralizer) (R : radicalForms) :
    adjointMatrix ((radicalAction c : Module.End (ZMod 2) radicalForms) R) *
      (kernelMatrixAction c : SmallMatrix) =
      (kernelMatrixAction c : SmallMatrix) * adjointMatrix R := by
  apply Matrix.ext_iff_mulVec.mpr
  intro b
  simp only [← Matrix.mulVec_mulVec]
  apply kernelCoordEquiv.injective
  apply sub_eq_zero.mp
  apply beta_nondegenerate.2
  intro w
  obtain ⟨w, rfl⟩ := (LinearMap.GeneralLinearGroup.generalLinearEquiv
    (ZMod 2) kernelSpace (kernelAction c)).surjective w
  obtain ⟨a, rfl⟩ := kernelCoordEquiv.surjective w
  change beta ((kernelAction c : Module.End (ZMod 2) kernelSpace) (kernelCoordEquiv a)) (_ - _) = 0
  rw [map_sub, sub_eq_zero, ← kernelMatrixAction_coord, adjointMatrix_pairing,
    kernelMatrixAction_coord, kernelMatrixAction_coord, descendedPairing_action,
    kernelMatrixAction_coord, kernelAction_preserves_beta, adjointMatrix_pairing]

theorem op_rho_intertwines (c : centralizer) (v : Fin 10 → ZMod 2) :
    op ((rho c : TenMatrix) *ᵥ v) * (kernelMatrixAction c : SmallMatrix) =
      (kernelMatrixAction c : SmallMatrix) * op v := by
  change adjointMatrix (radicalCoordinates _) * _ = _ * adjointMatrix (radicalCoordinates v)
  rw [rho_coordinates]
  exact adjointMatrix_intertwines c _

/-- The inverse-pullback action corresponds to conjugation by the actual kernel action. -/
theorem op_rho_conjugation (c : centralizer) (v : Fin 10 → ZMod 2) :
    op ((rho c : TenMatrix) *ᵥ v) =
      (kernelMatrixAction c : SmallMatrix) * op v * ↑(kernelMatrixAction c)⁻¹ := by
  rw [← op_rho_intertwines, mul_assoc, Units.mul_inv, mul_one]

/-- The intrinsic radical-space dimension, with the geometric premise discharged. -/
theorem intrinsic_finrank_radicalForms : Module.finrank (ZMod 2) radicalForms = 10 :=
  finrank_radicalForms kernelSpace_eq_range_kernelColumns

theorem rho_ker : rho.ker = radicalAction.ker :=
  radicalMatrixAction_ker intrinsicBasis

/-- A kernel element centralizes each individual operator in the prescribed coordinates. -/
theorem kernelMatrixAction_commutes_of_mem_rho_ker (c : centralizer) (hc : c ∈ rho.ker)
    (i : Fin 10) :
    (kernelMatrixAction c : SmallMatrix) * operator i =
      operator i * (kernelMatrixAction c : SmallMatrix) := by
  have h := op_rho_intertwines c (Pi.single i 1)
  have hc' : rho c = 1 := hc
  rw [hc', Units.val_one, Matrix.one_mulVec, op_single] at h
  exact h.symm

/-- The exact saved restriction matrix lies in the exact saved 56-dimensional algebra.
This is an input to the separate kernel bound, with no order assertion here. -/
theorem restrictionBlock_mem_algebraSpan_of_mem_rho_ker (c : centralizer) (hc : c ∈ rho.ker) :
    restrictionBlock (toMatrix (c : Model)) ∈ algebraSpan := by
  rw [← kernelMatrixAction_eq_restrictionBlock]
  exact (commutes_operator_iff_mem_algebraSpan _).mp
    (kernelMatrixAction_commutes_of_mem_rho_ker c hc)

/-- The actual bilinear form on the displacement kernel induced by a radical form. -/
noncomputable def descendedForm (R : radicalForms) : LinearMap.BilinForm (ZMod 2) kernelSpace :=
  (R : BinaryMatrix).toBilin'.comp kernelLift kernelLift

theorem descendedForm_apply (R : radicalForms) (v w : kernelSpace) :
    descendedForm R v w = descendedPairing R v w := by
  simp only [descendedForm, LinearMap.BilinForm.comp_apply, Matrix.toBilin'_apply',
    descendedPairing]

/-- The Wall adjoints as endomorphisms of the actual kernel. -/
noncomputable def intrinsicOperator : (Fin 10 → ZMod 2) →ₗ[ZMod 2]
    Module.End (ZMod 2) kernelSpace :=
  (kernelCoordEquiv.conjAlgEquiv (ZMod 2)).toLinearMap.comp
    (Matrix.toLinAlgEquiv'.toLinearMap.comp op)

theorem intrinsicOperator_coord (v : Fin 10 → ZMod 2) (a : SmallColumn) :
    intrinsicOperator v (kernelCoordEquiv a) = kernelCoordEquiv (op v *ᵥ a) := by
  change kernelCoordEquiv (op v *ᵥ (kernelCoordEquiv.symm (kernelCoordEquiv a))) = _
  rw [kernelCoordEquiv.symm_apply_apply]

/-- The defining adjoint relation, fixing the descent and Wall conventions. -/
theorem intrinsicOperator_adjoint (v : Fin 10 → ZMod 2) (x y : kernelSpace) :
    beta x (intrinsicOperator v y) = descendedForm (radicalCoordinates v) x y := by
  obtain ⟨a, rfl⟩ := kernelCoordEquiv.surjective x
  obtain ⟨b, rfl⟩ := kernelCoordEquiv.surjective y
  rw [intrinsicOperator_coord, descendedForm_apply]
  exact adjointMatrix_pairing (radicalCoordinates v) a b

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
