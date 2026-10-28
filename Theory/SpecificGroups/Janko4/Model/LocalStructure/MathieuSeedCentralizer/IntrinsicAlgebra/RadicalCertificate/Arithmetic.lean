module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra.Data
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.KernelBound.OrbitCover.KernelEquations.ExteriorInvariance.Arithmetic

/-!
# Decoding binary exterior combinations

XOR of the original upper-triangle words represents the corresponding sum of
alternating matrices. This bridge checks the saved radical coefficients against
the original exterior family without changing its definition. The packed matrix
arithmetic imported here is proved by bitwise interpretation in `ZMod 2`.
-/

@[expose] public section
open scoped Matrix
namespace Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
open OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.Generation.KernelBound.OrbitCoverCoordinates

/-- Untrusted computation of an upper-triangle linear combination. -/
def radicalExteriorCombination (c : ℕ) : ℕ :=
  GeneratorCertificates.xorList (List.ofFn (fun j : Fin 1221 =>
    if c.testBit j.val then exteriorFormRows.get j else 0))

private theorem bit_radicalExteriorCombination (c k : ℕ) :
    bit (radicalExteriorCombination c) k =
      ∑ j : Fin 1221, bit c j.val * bit (exteriorFormRows.get j) k := by
  change GeneratorCertificates.bit _ _ = _
  rw [radicalExteriorCombination, GeneratorCertificates.bit_xorList,
    List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro j _
  cases h : c.testBit j.val <;> simp [h, bit, GeneratorCertificates.bit]

theorem decode_radicalExteriorCombination (c : ℕ) :
    decodeExteriorForm (radicalExteriorCombination c) =
      ∑ j : Fin 1221, bit c j.val • exteriorBasisForm j := by
  ext a b
  simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
    exteriorBasisForm, decodeExteriorForm]
  by_cases hab : a < b
  · simp only [hab, if_true]
    exact bit_radicalExteriorCombination c _
  · by_cases hba : b < a
    · simp only [hab, hba, if_false, if_true]
      exact bit_radicalExteriorCombination c _
    · simp [hab, hba]

/-- Bridge from checked XOR data to the prescribed literal radical form. -/
theorem ambientRadicalForm_eq_decode (i : Fin 10) (r : ℕ)
    (h : radicalExteriorCombination (radicalCoefficients.get i) = r) :
    ambientRadicalForm i = decodeExteriorForm r := by
  rw [← h, decode_radicalExteriorCombination]
  rfl

/-- Row-major packed matrices of arbitrary square size. -/
def radicalPackedMatrix (n r : ℕ) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  fun i j => bit r (n * i.val + j.val)

def radicalPackedRow (n r i : ℕ) : ℕ := (r >>> (n * i)) % 2^n

def radicalPackedMulRow (n x y : ℕ) : ℕ :=
  GeneratorCertificates.xorList (List.ofFn (fun k : Fin n =>
    if x.testBit k.val then radicalPackedRow n y k.val else 0))

private theorem radicalPackedRow_bit (n r : ℕ) (i j : Fin n) :
    bit (radicalPackedRow n r i.val) j.val = radicalPackedMatrix n r i j := by
  simp only [bit, radicalPackedRow, Nat.testBit_mod_two_pow, j.isLt, decide_true,
    Bool.true_and, Nat.testBit_shiftRight, radicalPackedMatrix]

private theorem radicalPackedMulRow_bit (n x y : ℕ) (i j : Fin n) :
    bit (radicalPackedMulRow n (radicalPackedRow n x i.val) y) j.val =
      (radicalPackedMatrix n x * radicalPackedMatrix n y) i j := by
  change GeneratorCertificates.bit _ _ = _
  rw [radicalPackedMulRow, GeneratorCertificates.bit_xorList,
    List.map_ofFn, List.sum_ofFn, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [← radicalPackedRow_bit n x i k, ← radicalPackedRow_bit n y k j]
  cases h : (radicalPackedRow n x i.val).testBit k.val <;>
    simp [h, bit, GeneratorCertificates.bit]

theorem radicalPackedMatrix_mul (n x y z : ℕ)
    (h : ∀ i : Fin n, radicalPackedMulRow n (radicalPackedRow n x i.val) y =
      radicalPackedRow n z i.val) :
    radicalPackedMatrix n x * radicalPackedMatrix n y = radicalPackedMatrix n z := by
  ext i j
  rw [← radicalPackedMulRow_bit, h, radicalPackedRow_bit]

/-- Embed a descended form as the lower-right adapted block, with all other
blocks zero. This is the full pullback identity, not a restriction alone. -/
def radicalAdaptedBlock (R : SmallMatrix) : BinaryMatrix := fun i j =>
  if hi : 56 ≤ i.val then
    if hj : 56 ≤ j.val then R ⟨i.val - 56, by omega⟩ ⟨j.val - 56, by omega⟩
    else 0
  else 0

theorem radicalAdaptedBlock_first_first (R : SmallMatrix) :
    (radicalAdaptedBlock R).submatrix firstIndex firstIndex = 0 := by
  ext i j
  simp [radicalAdaptedBlock, Matrix.submatrix, firstIndex, Nat.not_le.mpr i.isLt]

theorem radicalAdaptedBlock_first_second (R : SmallMatrix) :
    (radicalAdaptedBlock R).submatrix firstIndex secondIndex = 0 := by
  ext i j
  simp [radicalAdaptedBlock, Matrix.submatrix, firstIndex, Nat.not_le.mpr i.isLt]

theorem radicalAdaptedBlock_second_first (R : SmallMatrix) :
    (radicalAdaptedBlock R).submatrix secondIndex firstIndex = 0 := by
  ext i j
  simp [radicalAdaptedBlock, Matrix.submatrix, firstIndex, secondIndex, Nat.not_le.mpr j.isLt]

theorem radicalAdaptedBlock_second_second (R : SmallMatrix) :
    (radicalAdaptedBlock R).submatrix secondIndex secondIndex = R := by
  ext i j
  simp [radicalAdaptedBlock, Matrix.submatrix, secondIndex]

end Janko4.LocalStructure.MathieuSeedCentralizer.IntrinsicAlgebra
