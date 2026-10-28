module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.PackedNumerics
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalCommutant.Reduction

/-!
# The cyclic rows and annihilator projection

The cyclic matrix consists of the zeroth rows of the certified group words.
Bitwise addition identifies the annihilator with their prescribed sum. Its
checked right multiple is a sparse projection with a two-dimensional left
kernel. Source matrices and bit convention: `Janko4/Model/Data.lean`.
-/

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
open GeneratorCertificates Matrix


theorem cyclic_rows (i : Fin 112) :
    qMatrix i = decodeRows (wordRows.get i) 0 := by
  funext j
  exact congrArg (fun n => bit n j.val) (cyclic_rows_packed i)


theorem annihilator_polynomial :
    (polynomialRows.map decodeRows).sum = rMatrix :=
  decode_sum_rows polynomialRows rRows polynomial_packed

theorem annihilator_zero_row : rMatrix 0 = 0 := by
  have h := annihilator_zero_row_packed
  funext j
  change bit (rRows.get 0) j.val = 0
  rw [h]
  simp [bit]


theorem projection_matrix : pMatrix = rowProjection := by
  funext i j
  change bit (pRows.get i) j.val = _
  rw [projection_packed, bit_xor, bit_xor]
  have hone : bit (2 ^ i.val) j.val = (1 : BinaryMatrix) i j := by
    simpa only [decodeRows, packedOne, get_ofFn] using
      congrFun (congrFun decode_packedOne i) j
  rw [hone]
  have h0 : bit (if i = 0 then 1 else 0) j.val =
      ((Pi.single (0 : Fin 112) (1 : ZMod 2) : Fin 112 → ZMod 2) i) * (1 : BinaryMatrix) 0 j := by
    by_cases hi : i = 0
    · subst i
      simp only [ite_true, Pi.single_eq_same, one_mul]
      simpa only [decodeRows, packedOne, get_ofFn, Fin.val_zero, pow_zero, bit] using
        congrFun (congrFun decode_packedOne 0) j
    · simp [hi, bit]
  have h1 : bit (if i = 1 then aRows.get 0 else 0) j.val =
      ((Pi.single (1 : Fin 112) (1 : ZMod 2) : Fin 112 → ZMod 2) i) * matrixA 0 j := by
    by_cases hi : i = 1
    · subst i
      simp only [ite_true, Pi.single_eq_same, one_mul]
      rfl
    · simp [hi, bit]
  rw [h0, h1]
  simp only [rowProjection, Matrix.add_apply, Matrix.vecMulVec_apply, add_assoc]

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.CommutantCertificate
