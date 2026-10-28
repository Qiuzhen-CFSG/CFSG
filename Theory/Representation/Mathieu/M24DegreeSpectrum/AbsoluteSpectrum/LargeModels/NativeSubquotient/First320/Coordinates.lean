module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.TensorRows
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.First320.Data
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.RemainingGeneratorOrders

/-!
# Literal native and target matrices for the saved 320a embedding

Small factor comparisons and the structural tensor-row theorem identify the
saved 484-dimensional matrices with the genuine native action. The target
comparisons reuse the already checked ATLAS square, retaining the inverse
native-generator convention. All data equalities are kernel checked.
-/

@[expose] public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.First320
open Degree220Pair.NativeActions.CertificatePacked
open SmallModels.FortyFour
open TensorCoordinates Packed

private def codeRowsA : List ℕ := [1001, 48, 160, 1055, 34, 32, 544, 36, 1459, 96, 1868]

private def kernelRowsA : List ℕ := [662396682842, 9052120679296, 12817650907147, 6102273517238, 8388608, 4437573632, 8391680, 14193890057481, 562036736, 10449251208192, 1073741904, 1073741824, 555124523008, 1073752064, 12567892665524, 18790481920, 1956895139840, 11195684039925, 2399727365617, 13652941048634, 15924135442432, 12745685033019, 14208490109814, 16, 4294967568, 14238015370592, 4190040066738, 536870960, 16612937228736, 4294967296, 2048, 11194610427125, 536870912, 15569389568, 4295002112, 753679148529, 73551314944, 11079407273984, 2549914940218, 536877056, 15633688559616, 12762327644219, 12247307830134, 256087824384]

private theorem code_matrix_A : matrix 11 11 codeRowsA = Degrees120252.Native120.codeMatrix 0 := by
  decide +kernel

private theorem kernel_matrix_A : matrix 44 44 kernelRowsA = KernelAbsolute.Data.matrix 0 := by
  decide +kernel

private theorem ambient_matrix_A :
    matrix 484 484 ambientA =
      tensorMatrix (Degrees120252.Native120.codeMatrix 0) (KernelAbsolute.Data.matrix 0) := by
  rw [← code_matrix_A, ← kernel_matrix_A]
  symm
  apply tensorMatrix_of_rows
  · decide +kernel
  · decide +kernel

theorem native_matrix_A : LinearMap.toMatrix' (action484 Degree220Pair.generatorA) =
    matrix 484 484 ambientA :=
  action484_first.trans ambient_matrix_A.symm

private def codeRowsB : List ℕ := [1986, 1784, 1421, 811, 1722, 1318, 1704, 1592, 1976, 1712, 696]

private def kernelRowsB : List ℕ := [15633680958368, 10668698764128, 13265738388720, 3143916061152, 9730984011712, 10683201486848, 1857087602688, 7132415262720, 10683655651328, 9990920470528, 186188706250, 14568763949511, 10518240233473, 15334342230620, 9836785689183, 1979104896692, 10661422473813, 2206774386695, 4707217484865, 12929124914684, 9906543252799, 12831311683140, 7696777336757, 4408784013312, 11475809326144, 8846516159392, 17366623454048, 4278024393968, 592424206816, 2846687208512, 10659233814432, 14229425370976, 5662916376816, 14240162870752, 8808984346624, 17333422260224, 10459319107584, 555127275520, 8249660669952, 8809388965888, 10455330848768, 17333925969920, 12380584017920, 555300683776]

private theorem code_matrix_B : matrix 11 11 codeRowsB = Degrees120252.Native120.codeMatrix 1 := by
  decide +kernel

private theorem kernel_matrix_B : matrix 44 44 kernelRowsB = KernelAbsolute.Data.matrix 1 := by
  decide +kernel

private theorem ambient_matrix_B :
    matrix 484 484 ambientB =
      tensorMatrix (Degrees120252.Native120.codeMatrix 1) (KernelAbsolute.Data.matrix 1) := by
  rw [← code_matrix_B, ← kernel_matrix_B]
  symm
  apply tensorMatrix_of_rows
  · decide +kernel
  · decide +kernel

theorem native_matrix_B : LinearMap.toMatrix' (action484 Degree220Pair.generatorB) =
    matrix 484 484 ambientB :=
  action484_second.trans ambient_matrix_B.symm

theorem target_matrix_A : matrix 320 320 targetA = Degree320Pair.matrixA false := by
  have h : targetA = Degree320Pair.Data.Aa.toList := by decide +kernel
  rw [h, matrix_array]
  rfl

theorem target_matrix_B : matrix 320 320 targetB = Degree320Pair.matrixB false ^ 2 := by
  have h : targetB = Degree320Pair.MatrixRelationCertificate.squareBaRows := by decide +kernel
  rw [h]
  have hd : matrix 320 320 Degree320Pair.MatrixRelationCertificate.squareBaRows =
      Thompson.BinaryMatrix.decode 320 Degree320Pair.MatrixRelationCertificate.squareBaRows.toArray := by
    ext i j
    simp only [matrix, Thompson.BinaryMatrix.decode, List.getElem!_toArray]
  rw [hd, ← Degree320Pair.MatrixRelationCertificate.transpose_matrixB_true_eq_square_candidate,
    Degree320Pair.MatrixRelationCertificate.matrixB_true_eq_transpose_square_false,
    Matrix.transpose_transpose]

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.NativeSubquotient.First320
