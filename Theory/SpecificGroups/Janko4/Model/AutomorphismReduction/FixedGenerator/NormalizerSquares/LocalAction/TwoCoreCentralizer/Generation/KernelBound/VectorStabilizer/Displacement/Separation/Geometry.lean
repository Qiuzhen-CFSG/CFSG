module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.VectorStabilizer.Displacement.Separation.Checks

/-! The nine-dimensional common image and an actual restricted exterior form.
The test form vanishes on the common image, eliminating the quadratic term.
Its membership comes from the original exterior combination numbered 1513.
Source: ../source/README.md and ../../source/README.md. -/

@[expose] public section
open scoped Matrix
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement.Separation
open OrbitCoverCoordinates OrbitCoverCoordinates.LinearMembership
open GeneratorCertificates LinearMembership.FiniteAlgebra
open PolynomialCertificate

attribute [local irreducible] factorRows selfAdjointWords selfAdjointImageRows
  imageTransposeRows formImageRows testFormRows ambientRows ambientLeftRows
  ambientWord restrictionColumns ExteriorAnnihilators.embeddingRows

def factor (i : Fin 45) : Matrix (Fin 9) (Fin 50) (ZMod 2) :=
  rectDecode 50 (factorRows.get i)

theorem basis_factor (k : Fin 45) : selfAdjointBasis k = selfAdjointImage * factor k := by
  change packedMatrix (selfAdjointWords.get k) = _
  rw [packedMatrix, ← decode_slices]
  symm
  apply product_eq
  intro i
  simpa only [slices, get_ofFn] using factor_checks k i

theorem form_isotropic : selfAdjointImageᵀ * testForm * selfAdjointImage = 0 := by
  have ht : selfAdjointImageᵀ = rectDecode 50 imageTransposeRows :=
    transpose_eq _ _ image_transpose_checks
  have hp : testForm * selfAdjointImage = rectDecode 9 formImageRows :=
    product_eq _ _ _ form_image_checks
  rw [Matrix.mul_assoc, hp, ht]
  rw [← decode_mulRows]
  ext i j
  simp [rectDecode, mulRows, get_ofFn, image_isotropic_checks, bit]

theorem form_symmetric : testFormᵀ = testForm :=
  transpose_eq _ _ form_symmetric_checks

theorem ambient_decode : rectDecode 112 ambientRows = ExteriorInvariance.flatMatrix ambientWord := by
  ext i j
  have h := ambient_rows_check i
  change bit (ambientRows.get i) j.val = _
  rw [h]
  exact ExteriorInvariance.flatRow_bit _ i j

theorem form_restriction : testForm = restrictionForm (ExteriorInvariance.flatMatrix ambientWord) := by
  have hc : rectDecode 112 restrictionColumns = restrictionEmbeddingᵀ := rfl
  have he : rectDecode 50 ExteriorAnnihilators.embeddingRows = restrictionEmbedding :=
    ExteriorAnnihilators.embeddingRows_spec
  have hl := product_eq (k := 112) _ _ _ ambient_left_checks
  have hr := product_eq (k := 50) _ _ _ ambient_restriction_checks
  rw [hc, ambient_decode] at hl
  rw [he] at hr
  rw [← hl] at hr
  exact hr.symm

theorem form_mem : testForm ∈ restrictionExteriorSpace := by
  rw [form_restriction, ambient_combination_check]
  exact restrictionForm_mem (ExteriorInvariance.combination_mem testOriginalCoefficients)

theorem basis_quadratic_zero (i j : Fin 45) :
    (selfAdjointBasis i)ᵀ * testForm * selfAdjointBasis j = 0 := by
  rw [basis_factor i, basis_factor j, Matrix.transpose_mul]
  calc
    _ = (factor i)ᵀ * (selfAdjointImageᵀ * testForm * selfAdjointImage) * factor j := by
      simp only [Matrix.mul_assoc]
    _ = 0 := by rw [form_isotropic, Matrix.mul_zero, Matrix.zero_mul]

theorem quadratic_zero {X Y : RestrictionMatrix}
    (hX : X ∈ selfAdjointSpace) (hY : Y ∈ selfAdjointSpace) : Xᵀ * testForm * Y = 0 := by
  induction hX using Submodule.span_induction with
  | mem X hX =>
    obtain ⟨i, rfl⟩ := hX
    induction hY using Submodule.span_induction with
    | mem Y hY => obtain ⟨j, rfl⟩ := hY; exact basis_quadratic_zero i j
    | zero => exact Matrix.mul_zero _
    | add Y Z _ _ hY hZ => rw [Matrix.mul_add, hY, hZ, add_zero]
    | smul r Y _ hY => rw [Matrix.mul_smul, hY, smul_zero]
  | zero => rw [Matrix.transpose_zero, Matrix.zero_mul, Matrix.zero_mul]
  | add X Z _ _ hX hZ =>
    rw [Matrix.transpose_add, Matrix.add_mul, Matrix.add_mul, hX, hZ, add_zero]
  | smul r X _ hX => rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, hX, smul_zero]

/-- The linear part of pullback by the displacement. -/
def linearResidue : RestrictionMatrix →ₗ[ZMod 2] RestrictionMatrix where
  toFun X := Xᵀ * testForm + testForm * X
  map_add' X Y := by
    simp only [Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add]
    exact add_add_add_comm _ _ _ _
  map_smul' r X := by
    simp only [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_add, RingHom.id_apply]

theorem residue_mem {X : RestrictionMatrix} (hX : X ∈ selfAdjointSpace)
    (hpres : ∀ R : RestrictionMatrix, R ∈ restrictionExteriorSpace →
      (1+X)ᵀ * R * (1+X) ∈ restrictionExteriorSpace) :
    linearResidue X ∈ restrictionExteriorSpace := by
  have h := hpres testForm form_mem
  have hq := quadratic_zero hX hX
  have hp : (1+X)ᵀ * testForm * (1+X) = testForm + linearResidue X := by
    simp only [Matrix.transpose_add, Matrix.transpose_one, Matrix.add_mul,
      Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hq, add_zero, linearResidue,
      LinearMap.coe_mk, AddHom.coe_mk]
    abel
  rw [hp] at h
  have hs := restrictionExteriorSpace.sub_mem h form_mem
  simpa only [add_sub_cancel_left] using hs

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.VectorStabilizer.Displacement.Separation
