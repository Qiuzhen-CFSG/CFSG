module
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.Seed
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion.Checks

/-!
# The paired kernels and invertible completion in degree 1242

The packed certificates identify D with precisely I+A+B+BAB in the original
ATLAS row convention. They check D*u=0, v*D=0 and v*u=1, and exhibit a left
inverse of D+u*v. Square matrices over the field are Dedekind finite, so the
last certificate proves the completion is a unit. No nullity assertion or
external computation is used as a proof.

These are the four kernel/completion inputs of `density1242_of_certificates`.
The independent orbit-basis certificates are not used here.
Source: James, J. Algebra 27 (1973), 57–111; ATLAS M24G1-f2r1242B0.m1/.m2.
Provenance, generation and resource measurements: `KernelCompletion/source/README.md`.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion
open Thompson.BinaryMatrix

theorem element_eq_decode : algebraElement = decode 1242 Data.elementRows := by
  have hba' : Data1242.second * Data1242.first = decode 1242 Data.baRows := by
    apply product_of_rows Data1242.secondRows Data1242.firstRows Data.baRows Checks.first_size
    intro i
    exact of_decide_eq_true (checkRange_sound Checks.ba_check (Nat.zero_le _) i.isLt)
  have hbab' : decode 1242 Data.baRows * Data1242.second = decode 1242 Data.babRows := by
    apply product_of_rows Data.baRows Data1242.secondRows Data.babRows Checks.second_size
    intro i
    exact of_decide_eq_true (checkRange_sound Checks.bab_check (Nat.zero_le _) i.isLt)
  unfold algebraElement
  rw [hba', hbab']
  ext i j
  have hi : (2 ^ i.val ^^^ Data1242.firstRows[i.val]! ^^^ Data1242.secondRows[i.val]! ^^^
      Data.babRows[i.val]!) = Data.elementRows[i.val]! :=
    of_decide_eq_true (checkRange_sound Checks.element_check (Nat.zero_le _) i.isLt)
  have hone : (1 : Mat) i j = bit (2 ^ i.val) j.val := by
    simp [bit, Nat.testBit_two_pow, Matrix.one_apply, Fin.ext_iff]
  change (1 : Mat) i j + bit Data1242.firstRows[i.val]! j.val +
    bit Data1242.secondRows[i.val]! j.val + bit Data.babRows[i.val]! j.val = _
  rw [hone, ← bit_xor, ← bit_xor, ← bit_xor, hi]
  rfl

theorem completion_eq_decode :
    algebraElement + Matrix.vecMulVec column Density1242.row = decode 1242 Data.completedRows := by
  rw [element_eq_decode]
  ext i j
  have hi : (Data.elementRows[i.val]! ^^^ (if columnPacked.testBit i.val then rowPacked else 0)) =
      Data.completedRows[i.val]! :=
    of_decide_eq_true (checkRange_sound Checks.completion_check (Nat.zero_le _) i.isLt)
  change bit Data.elementRows[i.val]! j.val + bit columnPacked i.val * bit rowPacked j.val =
    bit Data.completedRows[i.val]! j.val
  rw [← hi, bit_xor]
  apply congrArg (fun x : ZMod 2 => bit Data.elementRows[i.val]! j.val + x)
  cases hu : columnPacked.testBit i.val <;> simp [bit, hu]

theorem kernel_column : algebraElement.mulVec column = 0 := by
  rw [element_eq_decode]
  funext i
  change (∑ k : Fin 1242, bit Data.elementRows[i.val]! k.val * bit columnPacked k.val) = 0
  rw [← bit_packedDot]
  have hi : packedDot Data.elementRows[i.val]! columnPacked 1242 = 0 :=
    of_decide_eq_true (checkRange_sound Checks.column_check (Nat.zero_le _) i.isLt)
  rw [hi]
  rfl

theorem kernel_row : Matrix.vecMul Density1242.row algebraElement = 0 := by
  rw [element_eq_decode]
  funext j
  change (∑ k : Fin 1242, bit rowPacked k.val * bit Data.elementRows[k.val]! j.val) = 0
  rw [← bit_packedMul 1242 Data.elementRows Checks.element_size]
  change bit (packedMul rowPacked Data.elementRows.toList 0) j.val = 0
  rw [Checks.row_check]
  simp [bit]

theorem pairing : dotProduct Density1242.row column = 1 := by
  change (∑ i : Fin 1242, bit rowPacked i.val * bit columnPacked i.val) = 1
  rw [← bit_packedDot, Checks.pairing_check]
  rfl

theorem completion_isUnit : IsUnit (algebraElement + Matrix.vecMulVec column Density1242.row) := by
  rw [completion_eq_decode]
  apply isUnit_iff_exists_inv'.mpr
  refine ⟨decode 1242 Data.inverseRows, ?_⟩
  apply inverse_of_rows Data.inverseRows Data.completedRows Checks.completed_size
  intro i
  exact of_decide_eq_true (checkRange_sound Checks.inverse_check (Nat.zero_le _) i.isLt)

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degrees12421792.Density1242.KernelCompletion
