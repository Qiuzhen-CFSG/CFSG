module
public import Theory.Representation.Mathieu.M22James.Uniqueness.PointExtension.MatrixRigidity

/-!
# Words for the point-stabilizer extension argument

The two words S and T fix points 1 and 17; the involution B swaps these
points. The word H fixes point 1 and satisfies BHB = HBH. Finally a word
L fixing point 1 sends 17 to A(1), so A belongs to H₁ B H₁, where H₁ is
the actual point stabilizer. All matrix and permutation identities are
checked in the original ATLAS coordinates.

This supplies finite data for the extension step in James (1973), Lemma 8.3,
as used in Aschbacher–Smith H.12.1(1), printed pp.393–394. The ATLAS source
attribution remains in the LinearModel/source directory imported by Reduction.
-/

@[expose] public section
namespace Sporadic.Mathieu.M22TripleCover.Uniqueness.PointExtension
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel

def wordS : M22TripleCover := coreGeneratorA⁻¹ * coreGeneratorB * coreGeneratorA * coreGeneratorB

def wordT : M22TripleCover := coreGeneratorA⁻¹ ^ 4 * coreGeneratorB * coreGeneratorA⁻¹ ^ 3

def wordH : M22TripleCover := coreGeneratorB * coreGeneratorA * coreGeneratorB * coreGeneratorA⁻¹ * coreGeneratorB

def wordL : M22TripleCover := coreGeneratorA⁻¹ ^ 2 * coreGeneratorB * coreGeneratorA ^ 2

theorem generatorB_sq : coreGeneratorB * coreGeneratorB = 1 := by
  apply Subtype.ext
  change coreB * coreB = 1
  simpa only [pow_two] using coreB_pow_two

theorem wordS_mem : wordS ∈ pointStabilizer := by
  rw [mem_pointStabilizer]
  simp only [wordS, map_mul, map_inv,
    corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
  decide +kernel

theorem wordT_mem : wordT ∈ pointStabilizer := by
  rw [mem_pointStabilizer]
  simp only [wordT, map_mul, map_inv, map_pow,
    corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
  decide +kernel

theorem wordH_mem : wordH ∈ pointStabilizer := by
  rw [mem_pointStabilizer]
  simp only [wordH, map_mul, map_inv,
    corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
  decide +kernel

theorem wordL_mem : wordL ∈ pointStabilizer := by
  rw [mem_pointStabilizer]
  simp only [wordL, map_mul, map_inv, map_pow,
    corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
  decide +kernel

theorem conjugate_wordS_mem :
    coreGeneratorB * wordS * coreGeneratorB ∈ pointStabilizer := by
  rw [mem_pointStabilizer]
  simp only [wordS, map_mul, map_inv,
    corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
  decide +kernel

theorem conjugate_wordT_mem :
    coreGeneratorB * wordT * coreGeneratorB ∈ pointStabilizer := by
  rw [mem_pointStabilizer]
  simp only [wordT, map_mul, map_inv, map_pow,
    corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
  decide +kernel

theorem generatorA_bridge_mem :
    coreGeneratorB * wordL⁻¹ * coreGeneratorA ∈ pointStabilizer := by
  rw [mem_pointStabilizer]
  simp only [wordL, map_mul, map_inv, map_pow,
    corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
  decide +kernel

private def inverseA : Matrix12 := fromRows ![100, 32, 2, 1, 7, 1705, 3524, 8, 16, 561, 2074, 1024]

private theorem coe_inverseA : ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val =
    inverseA := by
  change (↑(coreA⁻¹) : Matrix12) = inverseA
  have h : inverseA * matrixA = 1 := by decide +kernel
  have hh : inverseA * (coreA : Matrix12) = 1 := by rw [coe_coreA]; exact h
  have hx := congrArg (fun M : Matrix12 => M * (↑(coreA⁻¹) : Matrix12)) hh
  simpa only [mul_assoc, Units.val_mul, Units.mul_inv, Units.val_one, mul_one,
    one_mul] using hx.symm

private theorem coe_generatorA : ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val =
    matrixA := coe_coreA

private theorem coe_generatorB : ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val =
    matrixB := coe_coreB

private def inverseA2 : Matrix12 := fromRows ![2927, 1705, 32, 100, 70, 3311, 452, 1, 7, 1275, 1062, 2074]

private theorem inverseA_pow2 : inverseA ^ 2 = inverseA2 := by
  rw [pow_succ]
  decide +kernel

private def inverseA3 : Matrix12 := fromRows ![3339, 3311, 1705, 2927, 3558, 1848, 3550, 100, 70, 829, 3729, 1062]

private theorem inverseA_pow3 : inverseA ^ 3 = inverseA3 := by
  rw [pow_succ, inverseA_pow2]
  decide +kernel

private def inverseA4 : Matrix12 := fromRows ![3151, 1848, 3311, 3339, 1869, 3220, 482, 2927, 3558, 1256, 3648, 3729]

private theorem inverseA_pow4 : inverseA ^ 4 = inverseA4 := by
  rw [pow_succ, inverseA_pow3]
  decide +kernel

private def partialS0 : Matrix12 := fromRows ![2837, 778, 2, 16, 13, 1699, 3524, 8, 1, 2395, 75, 3163]

private theorem stepS0 : inverseA * matrixB = partialS0 := by decide +kernel

private def partialS1 : Matrix12 := fromRows ![509, 1513, 4, 256, 148, 164, 64, 128, 8, 624, 147, 3095]

private theorem stepS1 : partialS0 * matrixA = partialS1 := by decide +kernel

private theorem stepS2 : partialS1 * matrixB = matrixS := by decide +kernel

theorem coe_wordS : ((wordS : M22TripleCover) : Matrix12ˣ).val = matrixS := by
  simp only [wordS, Subgroup.coe_mul, Units.val_mul]
  rw [coe_inverseA, coe_generatorB, coe_generatorA]
  rw [stepS0, stepS1, stepS2]

private def partialT0 : Matrix12 := fromRows ![1054, 3954, 1214, 1643, 1142, 4015, 712, 2917, 3788, 1267, 3675, 1504]

private theorem stepT0 : inverseA4 * matrixB = partialT0 := by decide +kernel

private theorem stepT1 : partialT0 * inverseA3 = matrixT := by decide +kernel

theorem coe_wordT : ((wordT : M22TripleCover) : Matrix12ˣ).val = matrixT := by
  simp only [wordT, Subgroup.coe_mul, Subgroup.coe_pow, Units.val_mul,
    Units.val_pow_eq_pow_val]
  rw [coe_inverseA, coe_generatorB, inverseA_pow4, inverseA_pow3]
  rw [stepT0, stepT1]

private def partialH0 : Matrix12 := fromRows ![256, 4, 400, 128, 8, 1513, 1412, 3659, 1559, 1681, 3095, 31]

private theorem stepH0 : matrixB * matrixA = partialH0 := by decide +kernel

private def partialH1 : Matrix12 := fromRows ![2666, 31, 2497, 938, 8, 3721, 1412, 3649, 1559, 1440, 3095, 4]

private theorem stepH1 : partialH0 * matrixB = partialH1 := by decide +kernel

private def partialH2 : Matrix12 := fromRows ![3453, 64, 2488, 1185, 1, 3654, 2048, 907, 2666, 3755, 3163, 2]

private theorem stepH2 : partialH1 * inverseA = partialH2 := by decide +kernel

private theorem stepH3 : partialH2 * matrixB = matrixH := by decide +kernel

theorem coe_wordH : ((wordH : M22TripleCover) : Matrix12ˣ).val = matrixH := by
  simp only [wordH, Subgroup.coe_mul, Units.val_mul]
  rw [coe_inverseA, coe_generatorB, coe_generatorA]
  rw [stepH0, stepH1, stepH2, stepH3]

/-- The relation that distinguishes the four involutory extension candidates. -/
theorem generatorB_wordH_braid :
    coreGeneratorB * wordH * coreGeneratorB = wordH * coreGeneratorB * wordH := by
  apply Subtype.ext
  apply Units.ext
  change (↑(coreGeneratorB : Matrix12ˣ) : Matrix12) * ↑(wordH : Matrix12ˣ) *
      ↑(coreGeneratorB : Matrix12ˣ) =
    (↑(wordH : Matrix12ˣ) : Matrix12) * ↑(coreGeneratorB : Matrix12ˣ) * ↑(wordH : Matrix12ˣ)
  rw [coe_generatorB, coe_wordH]
  decide +kernel

end Sporadic.Mathieu.M22TripleCover.Uniqueness.PointExtension
