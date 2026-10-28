module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.WallGeometry.Certificates
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Algebra.Field.ZMod

/-!
# The actual displacement kernel and its prescribed coordinates

The first 56 adapted columns are independent by the certified inverse. They
are images under the displacement of the last 56 columns. Square-zero and
rank-nullity then identify their span with both the image and the kernel.
The resulting coordinate equivalence retains the literal saved column basis.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra

/-- The first 56 rows of the inverse adapted matrix. -/
def kernelCoordinateMatrix : Matrix (Fin 56) (Fin 112) (ZMod 2) :=
  adaptedInverse.submatrix firstIndex id

theorem kernelCoordinateMatrix_mul_kernelColumns :
    kernelCoordinateMatrix * kernelColumns = 1 := by
  change adaptedInverse.submatrix firstIndex id * adaptedMatrix.submatrix id firstIndex = 1
  rw [← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id,
    adaptedInverse_mul_adaptedMatrix]
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.one_apply, firstIndex, Fin.ext_iff]

theorem kernelColumns_injective : Function.Injective kernelColumns.mulVecLin := by
  intro a b h
  have h' := congrArg (fun v => kernelCoordinateMatrix *ᵥ v) h
  change kernelCoordinateMatrix *ᵥ (kernelColumns *ᵥ a) =
    kernelCoordinateMatrix *ᵥ (kernelColumns *ᵥ b) at h'
  simpa only [Matrix.mulVec_mulVec, kernelCoordinateMatrix_mul_kernelColumns,
    Matrix.one_mulVec] using h'

theorem kernelColumns_range_le_displacement_range :
    LinearMap.range kernelColumns.mulVecLin ≤ LinearMap.range displacement := by
  rintro v ⟨a, rfl⟩
  refine ⟨liftColumns *ᵥ a, ?_⟩
  change displacementMatrix *ᵥ (liftColumns *ᵥ a) = kernelColumns *ᵥ a
  rw [Matrix.mulVec_mulVec, displacement_mul_liftColumns]

theorem finrank_kernelColumns_range :
    Module.finrank (ZMod 2) (LinearMap.range kernelColumns.mulVecLin) = 56 := by
  rw [LinearMap.finrank_range_of_inj kernelColumns_injective]
  simp

private theorem displacement_dimensions :
    Module.finrank (ZMod 2) (LinearMap.range displacement) = 56 ∧
      Module.finrank (ZMod 2) kernelSpace = 56 := by
  have h₁ : 56 ≤ Module.finrank (ZMod 2) (LinearMap.range displacement) := by
    rw [← finrank_kernelColumns_range]
    exact Submodule.finrank_mono kernelColumns_range_le_displacement_range
  have h₂ : Module.finrank (ZMod 2) (LinearMap.range displacement) ≤
      Module.finrank (ZMod 2) kernelSpace :=
    Submodule.finrank_mono range_displacement_le_kernel
  have h₃ := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) displacement
  change Module.finrank (ZMod 2) (LinearMap.range displacement) +
    Module.finrank (ZMod 2) kernelSpace = Module.finrank (ZMod 2) Column at h₃
  have hv : Module.finrank (ZMod 2) Column = 112 := by simp [Column]
  rw [hv] at h₃
  omega

theorem displacementMatrix_rank : displacementMatrix.rank = 56 :=
  displacement_dimensions.1

theorem finrank_kernelSpace : Module.finrank (ZMod 2) kernelSpace = 56 :=
  displacement_dimensions.2

theorem kernelSpace_eq_range_displacement : kernelSpace = LinearMap.range displacement := by
  exact (Submodule.eq_of_le_of_finrank_eq (K := ZMod 2) range_displacement_le_kernel
    (displacement_dimensions.1.trans displacement_dimensions.2.symm)).symm

theorem kernelSpace_eq_range_kernelColumns :
    kernelSpace = LinearMap.range kernelColumns.mulVecLin := by
  apply Eq.symm
  apply Submodule.eq_of_le_of_finrank_eq (K := ZMod 2)
    (kernelColumns_range_le_displacement_range.trans range_displacement_le_kernel)
  rw [finrank_kernelColumns_range, finrank_kernelSpace]

/-- Column coordinates with codomain the actual displacement kernel. -/
def kernelCoordMap : SmallColumn →ₗ[ZMod 2] kernelSpace :=
  kernelColumns.mulVecLin.codRestrict kernelSpace (by
    intro a
    rw [mem_kernelSpace]
    change displacementMatrix *ᵥ (kernelColumns *ᵥ a) = 0
    rw [Matrix.mulVec_mulVec, displacement_mul_kernelColumns, Matrix.zero_mulVec])

theorem kernelCoordMap_apply (a : SmallColumn) :
    (kernelCoordMap a : Column) = kernelColumns *ᵥ a := by
  simp only [kernelCoordMap, LinearMap.codRestrict_apply, Matrix.mulVecLin_apply]

theorem kernelCoordMap_bijective : Function.Bijective kernelCoordMap := by
  constructor
  · intro a b h
    have h' := congrArg (fun v : kernelSpace => (v : Column)) h
    simp only [kernelCoordMap_apply] at h'
    exact kernelColumns_injective h'
  · intro v
    have hv : (v : Column) ∈ LinearMap.range kernelColumns.mulVecLin :=
      kernelSpace_eq_range_kernelColumns.le v.property
    obtain ⟨a, ha⟩ := hv
    refine ⟨a, Subtype.ext ?_⟩
    simpa only [kernelCoordMap_apply, Matrix.mulVecLin_apply] using ha

set_option maxRecDepth 2048 in
/-- The prescribed literal basis, not merely an abstract dimension equivalence. -/
noncomputable def kernelCoordEquiv : SmallColumn ≃ₗ[ZMod 2] kernelSpace :=
  LinearEquiv.ofBijective kernelCoordMap kernelCoordMap_bijective

@[simp] theorem kernelCoordEquiv_apply (a : SmallColumn) :
    (kernelCoordEquiv a : Column) = kernelColumns *ᵥ a := by
  rw [kernelCoordEquiv, LinearEquiv.ofBijective_apply, kernelCoordMap_apply]

theorem kernelCoordEquiv_symm_apply (v : kernelSpace) :
    kernelCoordEquiv.symm v = kernelCoordinateMatrix *ᵥ (v : Column) := by
  obtain ⟨a, rfl⟩ := kernelCoordEquiv.surjective v
  simp only [kernelCoordEquiv.symm_apply_apply, kernelCoordEquiv_apply,
    Matrix.mulVec_mulVec, kernelCoordinateMatrix_mul_kernelColumns, Matrix.one_mulVec]

/-- A specified preimage of a kernel vector under the displacement. -/
noncomputable def kernelLift : kernelSpace →ₗ[ZMod 2] Column :=
  liftColumns.mulVecLin.comp kernelCoordEquiv.symm.toLinearMap

theorem kernelLift_coord (a : SmallColumn) :
    kernelLift (kernelCoordEquiv a) = liftColumns *ᵥ a := by
  change liftColumns *ᵥ (kernelCoordEquiv.symm (kernelCoordEquiv a)) = _
  rw [kernelCoordEquiv.symm_apply_apply]

theorem displacement_kernelLift (v : kernelSpace) : displacement (kernelLift v) = v := by
  obtain ⟨a, rfl⟩ := kernelCoordEquiv.surjective v
  rw [kernelLift_coord, kernelCoordEquiv_apply]
  change displacementMatrix *ᵥ (liftColumns *ᵥ a) = _
  rw [Matrix.mulVec_mulVec, displacement_mul_liftColumns]

/-- The displacement with codomain restricted to its actual kernel. -/
def displacementToKernel : Column →ₗ[ZMod 2] kernelSpace :=
  displacement.codRestrict kernelSpace (fun v => displacement_sq v)

@[simp] theorem displacementToKernel_apply (v : Column) :
    (displacementToKernel v : Column) = displacement v := rfl

theorem displacementToKernel_surjective : Function.Surjective displacementToKernel := by
  intro v
  exact ⟨kernelLift v, Subtype.ext (displacement_kernelLift v)⟩

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
