module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.KernelBound.Coordinates.Data
public import Theory.SpecificGroups.Janko4.Model.Cardinality.LocalOrder.KernelCount.Relations.WordEvaluation
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.InvariantForm

/-!
# Certified change of basis for the literal seed

Packed binary multiplication certifies the inverse basis matrices, the equation
`t P = P [[I,I],[0,I]]`, and the transported invariant form. All arithmetic is
checked by the Lean kernel. The data source and conventions are recorded in
`Coordinates.Data`; no centralizer-size assertion enters these calculations.
-/

public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.Coordinates
open GeneratorCertificates Cardinality.KernelCount
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

set_option maxRecDepth 10000 in
private theorem inverse_basis_product :
    packedMul adaptedInverseRows adaptedRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
private theorem basis_inverse_product :
    packedMul adaptedRows adaptedInverseRows = packedOne :=
  packedMul_eq_of_rows _ _ _ (by
    simp only [packedOne, get_ofFn]
    decide +kernel)

set_option maxRecDepth 10000 in
private theorem seed_basis_product :
    packedMul e0Rows adaptedRows = seedTimesBasisRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem basis_seed_product :
    packedMul adaptedRows adaptedSeedRows = seedTimesBasisRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem transpose_form_product :
    packedMul adaptedTransposeRows invariantFormRows = transposeTimesFormRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

set_option maxRecDepth 10000 in
private theorem form_basis_product :
    packedMul transposeTimesFormRows adaptedRows = adaptedFormRows :=
  packedMul_eq_of_rows _ _ _ (by decide +kernel)

/-- The published inverse is a left inverse. -/
theorem adapted_inverse_mul :
    decodeRows adaptedInverseRows * decodeRows adaptedRows = 1 := by
  rw [← decode_packedMul, inverse_basis_product, decode_packedOne]

/-- The published inverse is a right inverse. -/
theorem adapted_mul_inverse :
    decodeRows adaptedRows * decodeRows adaptedInverseRows = 1 := by
  rw [← decode_packedMul, basis_inverse_product, decode_packedOne]

/-- The seed word has the asserted adapted matrix. -/
theorem seed_mul_adapted :
    decodeRows e0Rows * decodeRows adaptedRows =
      decodeRows adaptedRows * decodeRows adaptedSeedRows := by
  rw [← decode_packedMul, ← decode_packedMul, seed_basis_product, basis_seed_product]

/-- Calibration of the transpose needed for transporting bilinear forms. -/
theorem adapted_transpose :
    (decodeRows adaptedRows)ᵀ = decodeRows adaptedTransposeRows := by
  decide +kernel

/-- The exact invariant form in the adapted coordinates. -/
theorem adapted_invariantForm :
    (decodeRows adaptedRows)ᵀ * invariantForm * decodeRows adaptedRows =
      decodeRows adaptedFormRows := by
  rw [adapted_transpose]
  change decodeRows adaptedTransposeRows * decodeRows invariantFormRows *
    decodeRows adaptedRows = _
  rw [← decode_packedMul, transpose_form_product, ← decode_packedMul, form_basis_product]

end Janko4.LocalStructure.MathieuSeedCentralizer.KernelBound.Coordinates
