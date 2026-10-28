module

public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.Factors
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.TableChecks
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products00
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products01
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products02
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products03
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products04
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products05
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products06
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products07
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products08
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products09
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products10
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products11
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products12
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products13
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products14
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products15
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products16
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SymmetricLinear.Quotient.OrderBound.DiagonalImage.LinearOrder.Products17

/-!
# The complete right-transition certificate

The first generator is an involution. Four direct products along the base
cycle prove that the second generator has fourth power one. These identities
recover reverse edges and the closing edge of each remaining four-cycle; all
other products were checked on the full 112-dimensional matrices.

Source: ATLAS J4G1-f2r112B0 and J4G1-max4W1; see source/README.md.
-/

@[expose] public section
namespace Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.LinearEnumeration

private theorem reverse_transition {a b g : BinaryMatrix}
    (hg : g * g = 1) (h : a * g = b) : b * g = a := by
  rw [← h, mul_assoc, hg, mul_one]

private theorem fourth_transition {a b c e g : BinaryMatrix}
    (hg : g ^ 4 = 1) (hab : a * g = b) (hbc : b * g = c)
    (hce : c * g = e) : e * g = a := by
  rw [← hce, ← hbc, ← hab]
  calc
    a * g * g * g * g = a * g ^ 4 := by
      simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = a := by rw [hg, mul_one]

theorem second_four : (decodeRows linearSecondRows) ^ 4 = 1 := by
  have hzero : decodeRows rows000 = 1 := zero_matrix
  calc
    (decodeRows linearSecondRows) ^ 4 =
        decodeRows rows000 * decodeRows linearSecondRows * decodeRows linearSecondRows *
          decodeRows linearSecondRows * decodeRows linearSecondRows := by
      rw [hzero]
      simp only [pow_succ, pow_zero, one_mul]
    _ = decodeRows rows000 := by
      rw [product_000_1, product_002_1, product_005_1, product_010_1]
    _ = 1 := hzero

theorem matrix_transition (i : Fin 168) (j : Fin 2) :
    decodeRows (rows i) * decodeRows (generatorRows j) = decodeRows (rows (next i j)) := by
  fin_cases j
  · fin_cases i
    · exact product_000_0
    · exact reverse_transition linearFirst_square product_000_0
    · exact product_002_0
    · exact product_003_0
    · exact reverse_transition linearFirst_square product_002_0
    · exact product_005_0
    · exact reverse_transition linearFirst_square product_003_0
    · exact product_007_0
    · exact product_008_0
    · exact reverse_transition linearFirst_square product_005_0
    · exact product_010_0
    · exact product_011_0
    · exact reverse_transition linearFirst_square product_007_0
    · exact product_013_0
    · exact reverse_transition linearFirst_square product_008_0
    · exact product_015_0
    · exact product_016_0
    · exact reverse_transition linearFirst_square product_010_0
    · exact reverse_transition linearFirst_square product_011_0
    · exact product_019_0
    · exact product_020_0
    · exact reverse_transition linearFirst_square product_013_0
    · exact product_022_0
    · exact reverse_transition linearFirst_square product_015_0
    · exact product_024_0
    · exact reverse_transition linearFirst_square product_016_0
    · exact product_026_0
    · exact product_027_0
    · exact reverse_transition linearFirst_square product_019_0
    · exact product_029_0
    · exact reverse_transition linearFirst_square product_020_0
    · exact product_031_0
    · exact reverse_transition linearFirst_square product_022_0
    · exact product_033_0
    · exact product_034_0
    · exact reverse_transition linearFirst_square product_024_0
    · exact product_036_0
    · exact reverse_transition linearFirst_square product_026_0
    · exact reverse_transition linearFirst_square product_027_0
    · exact product_039_0
    · exact product_040_0
    · exact reverse_transition linearFirst_square product_029_0
    · exact product_042_0
    · exact reverse_transition linearFirst_square product_031_0
    · exact product_044_0
    · exact reverse_transition linearFirst_square product_033_0
    · exact product_046_0
    · exact reverse_transition linearFirst_square product_034_0
    · exact product_048_0
    · exact reverse_transition linearFirst_square product_036_0
    · exact product_050_0
    · exact product_051_0
    · exact product_052_0
    · exact reverse_transition linearFirst_square product_039_0
    · exact product_054_0
    · exact reverse_transition linearFirst_square product_040_0
    · exact product_056_0
    · exact reverse_transition linearFirst_square product_042_0
    · exact reverse_transition linearFirst_square product_050_0
    · exact product_059_0
    · exact reverse_transition linearFirst_square product_044_0
    · exact product_061_0
    · exact product_062_0
    · exact reverse_transition linearFirst_square product_046_0
    · exact product_064_0
    · exact reverse_transition linearFirst_square product_048_0
    · exact product_066_0
    · exact product_067_0
    · exact reverse_transition linearFirst_square product_051_0
    · exact product_069_0
    · exact reverse_transition linearFirst_square product_052_0
    · exact product_071_0
    · exact product_072_0
    · exact reverse_transition linearFirst_square product_054_0
    · exact product_074_0
    · exact reverse_transition linearFirst_square product_056_0
    · exact product_076_0
    · exact product_077_0
    · exact reverse_transition linearFirst_square product_059_0
    · exact product_079_0
    · exact reverse_transition linearFirst_square product_061_0
    · exact product_081_0
    · exact reverse_transition linearFirst_square product_062_0
    · exact product_083_0
    · exact reverse_transition linearFirst_square product_064_0
    · exact reverse_transition linearFirst_square product_069_0
    · exact product_086_0
    · exact reverse_transition linearFirst_square product_066_0
    · exact product_088_0
    · exact reverse_transition linearFirst_square product_067_0
    · exact product_090_0
    · exact product_091_0
    · exact reverse_transition linearFirst_square product_071_0
    · exact product_093_0
    · exact reverse_transition linearFirst_square product_072_0
    · exact product_095_0
    · exact reverse_transition linearFirst_square product_074_0
    · exact reverse_transition linearFirst_square product_079_0
    · exact product_098_0
    · exact reverse_transition linearFirst_square product_076_0
    · exact product_100_0
    · exact reverse_transition linearFirst_square product_077_0
    · exact product_102_0
    · exact product_103_0
    · exact product_104_0
    · exact reverse_transition linearFirst_square product_081_0
    · exact product_106_0
    · exact reverse_transition linearFirst_square product_083_0
    · exact product_108_0
    · exact reverse_transition linearFirst_square product_086_0
    · exact product_110_0
    · exact reverse_transition linearFirst_square product_088_0
    · exact product_112_0
    · exact product_113_0
    · exact reverse_transition linearFirst_square product_090_0
    · exact product_115_0
    · exact reverse_transition linearFirst_square product_091_0
    · exact product_117_0
    · exact reverse_transition linearFirst_square product_093_0
    · exact product_119_0
    · exact reverse_transition linearFirst_square product_095_0
    · exact product_121_0
    · exact reverse_transition linearFirst_square product_098_0
    · exact product_123_0
    · exact reverse_transition linearFirst_square product_100_0
    · exact product_125_0
    · exact product_126_0
    · exact reverse_transition linearFirst_square product_102_0
    · exact product_128_0
    · exact reverse_transition linearFirst_square product_103_0
    · exact reverse_transition linearFirst_square product_104_0
    · exact product_131_0
    · exact reverse_transition linearFirst_square product_106_0
    · exact reverse_transition linearFirst_square product_110_0
    · exact reverse_transition linearFirst_square product_119_0
    · exact reverse_transition linearFirst_square product_108_0
    · exact product_136_0
    · exact product_137_0
    · exact reverse_transition linearFirst_square product_112_0
    · exact reverse_transition linearFirst_square product_113_0
    · exact reverse_transition linearFirst_square product_115_0
    · exact product_141_0
    · exact product_142_0
    · exact reverse_transition linearFirst_square product_117_0
    · exact product_144_0
    · exact reverse_transition linearFirst_square product_123_0
    · exact reverse_transition linearFirst_square product_121_0
    · exact product_147_0
    · exact reverse_transition linearFirst_square product_137_0
    · exact reverse_transition linearFirst_square product_125_0
    · exact reverse_transition linearFirst_square product_126_0
    · exact reverse_transition linearFirst_square product_128_0
    · exact product_152_0
    · exact reverse_transition linearFirst_square product_142_0
    · exact product_154_0
    · exact reverse_transition linearFirst_square product_131_0
    · exact product_156_0
    · exact product_157_0
    · exact reverse_transition linearFirst_square product_136_0
    · exact reverse_transition linearFirst_square product_154_0
    · exact reverse_transition linearFirst_square product_141_0
    · exact product_161_0
    · exact reverse_transition linearFirst_square product_144_0
    · exact reverse_transition linearFirst_square product_147_0
    · exact reverse_transition linearFirst_square product_161_0
    · exact reverse_transition linearFirst_square product_152_0
    · exact reverse_transition linearFirst_square product_157_0
    · exact reverse_transition linearFirst_square product_156_0
  · fin_cases i
    · exact product_000_1
    · exact product_001_1
    · exact product_002_1
    · exact product_003_1
    · exact product_004_1
    · exact product_005_1
    · exact product_006_1
    · exact product_007_1
    · exact product_008_1
    · exact product_009_1
    · exact product_010_1
    · exact product_011_1
    · exact product_012_1
    · exact fourth_transition second_four product_001_1 product_003_1 product_007_1
    · exact product_014_1
    · exact product_015_1
    · exact product_016_1
    · exact product_017_1
    · exact product_018_1
    · exact product_019_1
    · exact fourth_transition second_four product_009_1 product_016_1 product_012_1
    · exact product_021_1
    · exact product_022_1
    · exact product_023_1
    · exact fourth_transition second_four product_004_1 product_008_1 product_015_1
    · exact product_025_1
    · exact product_026_1
    · exact product_027_1
    · exact product_028_1
    · exact fourth_transition second_four product_006_1 product_011_1 product_019_1
    · exact product_030_1
    · exact product_031_1
    · exact product_032_1
    · exact product_033_1
    · exact fourth_transition second_four product_017_1 product_026_1 product_023_1
    · exact product_035_1
    · exact product_036_1
    · exact product_037_1
    · exact product_038_1
    · exact product_039_1
    · exact fourth_transition second_four product_021_1 product_031_1 product_028_1
    · exact product_041_1
    · exact product_042_1
    · exact product_043_1
    · exact product_044_1
    · exact product_045_1
    · exact fourth_transition second_four product_014_1 product_022_1 product_033_1
    · exact product_047_1
    · exact product_048_1
    · exact product_049_1
    · exact product_050_1
    · exact product_051_1
    · exact product_052_1
    · exact product_053_1
    · exact fourth_transition second_four product_018_1 product_027_1 product_039_1
    · exact product_055_1
    · exact product_056_1
    · exact product_057_1
    · exact product_058_1
    · exact product_059_1
    · exact fourth_transition second_four product_055_1 product_074_1 product_097_1
    · exact product_061_1
    · exact fourth_transition second_four product_035_1 product_048_1 product_045_1
    · exact product_063_1
    · exact product_064_1
    · exact product_065_1
    · exact product_066_1
    · exact fourth_transition second_four product_025_1 product_036_1 product_050_1
    · exact product_068_1
    · exact product_069_1
    · exact fourth_transition second_four product_047_1 product_064_1 product_085_1
    · exact product_071_1
    · exact fourth_transition second_four product_041_1 product_056_1 product_053_1
    · exact product_073_1
    · exact product_074_1
    · exact product_075_1
    · exact product_076_1
    · exact fourth_transition second_four product_030_1 product_042_1 product_058_1
    · exact product_078_1
    · exact product_079_1
    · exact product_080_1
    · exact fourth_transition second_four product_032_1 product_044_1 product_061_1
    · exact product_082_1
    · exact product_083_1
    · exact product_084_1
    · exact product_085_1
    · exact product_086_1
    · exact fourth_transition second_four product_082_1 product_106_1 product_133_1
    · exact product_088_1
    · exact product_089_1
    · exact product_090_1
    · exact fourth_transition second_four product_037_1 product_051_1 product_069_1
    · exact product_092_1
    · exact fourth_transition second_four product_038_1 product_052_1 product_071_1
    · exact product_094_1
    · exact product_095_1
    · exact product_096_1
    · exact product_097_1
    · exact product_098_1
    · exact fourth_transition second_four product_094_1 product_119_1 product_145_1
    · exact product_100_1
    · exact product_101_1
    · exact product_102_1
    · exact fourth_transition second_four product_043_1 product_059_1 product_079_1
    · exact fourth_transition second_four product_063_1 product_083_1 product_080_1
    · exact product_105_1
    · exact product_106_1
    · exact product_107_1
    · exact product_108_1
    · exact product_109_1
    · exact product_110_1
    · exact product_111_1
    · exact fourth_transition second_four product_049_1 product_066_1 product_088_1
    · exact product_113_1
    · exact fourth_transition second_four product_101_1 product_126_1 product_124_1
    · exact product_115_1
    · exact product_116_1
    · exact fourth_transition second_four product_073_1 product_095_1 product_092_1
    · exact product_118_1
    · exact product_119_1
    · exact product_120_1
    · exact product_121_1
    · exact product_122_1
    · exact product_123_1
    · exact product_124_1
    · exact fourth_transition second_four product_057_1 product_076_1 product_100_1
    · exact product_126_1
    · exact fourth_transition second_four product_089_1 product_113_1 product_111_1
    · exact product_128_1
    · exact product_129_1
    · exact product_130_1
    · exact fourth_transition second_four product_096_1 product_121_1 product_105_1
    · exact product_132_1
    · exact product_133_1
    · exact product_134_1
    · exact fourth_transition second_four product_130_1 product_154_1 product_166_1
    · exact product_136_1
    · exact fourth_transition second_four product_065_1 product_086_1 product_110_1
    · exact fourth_transition second_four product_120_1 product_132_1 product_156_1
    · exact product_139_1
    · exact product_140_1
    · exact fourth_transition second_four product_068_1 product_090_1 product_115_1
    · exact product_142_1
    · exact product_143_1
    · exact fourth_transition second_four product_084_1 product_108_1 product_118_1
    · exact product_145_1
    · exact fourth_transition second_four product_143_1 product_161_1 product_167_1
    · exact fourth_transition second_four product_109_1 product_136_1 product_122_1
    · exact fourth_transition second_four product_075_1 product_098_1 product_123_1
    · exact fourth_transition second_four product_107_1 product_134_1 product_157_1
    · exact product_150_1
    · exact product_151_1
    · exact fourth_transition second_four product_078_1 product_102_1 product_128_1
    · exact product_153_1
    · exact product_154_1
    · exact fourth_transition second_four product_150_1 product_164_1 product_160_1
    · exact product_156_1
    · exact product_157_1
    · exact fourth_transition second_four product_116_1 product_142_1 product_140_1
    · exact product_159_1
    · exact product_160_1
    · exact product_161_1
    · exact fourth_transition second_four product_139_1 product_159_1 product_165_1
    · exact fourth_transition second_four product_129_1 product_153_1 product_151_1
    · exact product_164_1
    · exact product_165_1
    · exact product_166_1
    · exact product_167_1

end Janko4.LocalStructure.SymmetricLinear.OrderBound.DiagonalFactors.LinearEnumeration
