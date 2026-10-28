module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Finite00
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Finite01
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Finite02
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Finite03
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Finite04
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Finite05
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Finite06
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Finite07
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Finite08
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Finite09
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.Coordinates
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.RadicalCertificate.RawSpace

/-!
# The ten literal radical forms in adapted coordinates

The finite certificates prove annihilation of the saved kernel columns, the
complete adapted pullback identity, and the Wall-adjoint equation for each of
the ten forms. Together with their independent coordinate block this proves
that their span is ten dimensional and lies in the raw radical space.
Completeness of that containment is a separate elimination obligation.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra

theorem ambientRadicalForm_mul_kernelColumns (i : Fin 10) :
    ambientRadicalForm i * kernelColumns = 0 := by
  fin_cases i
  · exact ambientRadicalForm_mul_kernelColumns_00
  · exact ambientRadicalForm_mul_kernelColumns_01
  · exact ambientRadicalForm_mul_kernelColumns_02
  · exact ambientRadicalForm_mul_kernelColumns_03
  · exact ambientRadicalForm_mul_kernelColumns_04
  · exact ambientRadicalForm_mul_kernelColumns_05
  · exact ambientRadicalForm_mul_kernelColumns_06
  · exact ambientRadicalForm_mul_kernelColumns_07
  · exact ambientRadicalForm_mul_kernelColumns_08
  · exact ambientRadicalForm_mul_kernelColumns_09

theorem ambientRadicalForm_pullback (i : Fin 10) :
    adaptedMatrixᵀ * ambientRadicalForm i * adaptedMatrix =
      radicalAdaptedBlock (descendedRadicalForm i) := by
  fin_cases i
  · exact ambientRadicalForm_pullback_00
  · exact ambientRadicalForm_pullback_01
  · exact ambientRadicalForm_pullback_02
  · exact ambientRadicalForm_pullback_03
  · exact ambientRadicalForm_pullback_04
  · exact ambientRadicalForm_pullback_05
  · exact ambientRadicalForm_pullback_06
  · exact ambientRadicalForm_pullback_07
  · exact ambientRadicalForm_pullback_08
  · exact ambientRadicalForm_pullback_09

theorem wallMatrix_mul_operator (i : Fin 10) :
    wallMatrix * operator i = descendedRadicalForm i := by
  fin_cases i
  · exact wallMatrix_mul_operator_00
  · exact wallMatrix_mul_operator_01
  · exact wallMatrix_mul_operator_02
  · exact wallMatrix_mul_operator_03
  · exact wallMatrix_mul_operator_04
  · exact wallMatrix_mul_operator_05
  · exact wallMatrix_mul_operator_06
  · exact wallMatrix_mul_operator_07
  · exact wallMatrix_mul_operator_08
  · exact wallMatrix_mul_operator_09

theorem ambientRadicalForm_pullback_first_first (i : Fin 10) :
    (adaptedMatrixᵀ * ambientRadicalForm i * adaptedMatrix).submatrix firstIndex firstIndex = 0 := by
  rw [ambientRadicalForm_pullback, radicalAdaptedBlock_first_first]

theorem ambientRadicalForm_pullback_first_second (i : Fin 10) :
    (adaptedMatrixᵀ * ambientRadicalForm i * adaptedMatrix).submatrix firstIndex secondIndex = 0 := by
  rw [ambientRadicalForm_pullback, radicalAdaptedBlock_first_second]

theorem ambientRadicalForm_pullback_second_first (i : Fin 10) :
    (adaptedMatrixᵀ * ambientRadicalForm i * adaptedMatrix).submatrix secondIndex firstIndex = 0 := by
  rw [ambientRadicalForm_pullback, radicalAdaptedBlock_second_first]

theorem ambientRadicalForm_pullback_second_second (i : Fin 10) :
    (adaptedMatrixᵀ * ambientRadicalForm i * adaptedMatrix).submatrix secondIndex secondIndex = descendedRadicalForm i := by
  rw [ambientRadicalForm_pullback, radicalAdaptedBlock_second_second]

theorem ambientRadicalForm_mem_rawRadicalForms (i : Fin 10) :
    ambientRadicalForm i ∈ rawRadicalForms :=
  ⟨ambientRadicalForm_mem_ambientForms i, ambientRadicalForm_mul_kernelColumns i⟩

theorem rawRadicalSpan_le_rawRadicalForms : rawRadicalSpan ≤ rawRadicalForms := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact ambientRadicalForm_mem_rawRadicalForms i

theorem ambientRadicalForm_mem_radicalForms
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) (i : Fin 10) :
    ambientRadicalForm i ∈ radicalForms := by
  rw [radicalForms_eq_rawRadicalForms hK]
  exact ambientRadicalForm_mem_rawRadicalForms i

theorem rawRadicalSpan_le_radicalForms
    (hK : kernelSpace = LinearMap.range kernelColumns.mulVecLin) :
    rawRadicalSpan ≤ radicalForms := by
  rw [radicalForms_eq_rawRadicalForms hK]
  exact rawRadicalSpan_le_rawRadicalForms

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
