module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.NormalFour.PackedNumerics

/-!
# The cyclic rows and annihilator projection

The cyclic matrix consists of the zeroth rows of the certified group words.
Bitwise addition identifies the annihilator with their prescribed sum. Its
checked right multiple is a sparse projection with a two-dimensional left
kernel. Source matrices and bit convention: `Janko4/Model/Data.lean`.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
open GeneratorCertificates Matrix

private theorem bit_sum_rows (L : List (Vector ℕ 112)) (i j : Fin 112) :
    bit (xorList (L.map (fun v => v.get i))) j.val =
      ((L.map decodeRows).sum) i j := by
  induction L with
  | nil => simp [xorList, bit]
  | cons v L ih =>
    simpa only [List.map_cons, List.sum_cons, xorList, bit_xor,
      Matrix.add_apply, decodeRows, bit] using congrArg (decodeRows v i j + ·) ih

private theorem decode_sum_rows (L : List (Vector ℕ 112)) (r : Vector ℕ 112)
    (h : ∀ i : Fin 112, xorList (L.map (fun v => v.get i)) = r.get i) :
    (L.map decodeRows).sum = decodeRows r := by
  funext i j
  exact (bit_sum_rows L i j).symm.trans (congrArg (fun n => bit n j.val) (h i))


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


theorem projection_matrix : pMatrix = 1 + vecMulVec (Pi.single 0 1) ((1 : BinaryMatrix) 0) +
      vecMulVec (Pi.single 1 1) kernelRow := by
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
  have h1 : bit (if i = 1 then 2937915053987813481625123188289954 else 0) j.val =
      ((Pi.single (1 : Fin 112) (1 : ZMod 2) : Fin 112 → ZMod 2) i) * kernelRow j := by
    by_cases hi : i = 1
    · subst i
      simp only [ite_true, Pi.single_eq_same, one_mul]
      rfl
    · simp [hi, bit]
  rw [h0, h1]
  simp only [Matrix.add_apply, Matrix.vecMulVec_apply, add_assoc]

end Janko4.LocalStructure.SymmetricLinear.NormalFour.Certificate
