module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Sylow
import Mathlib.Tactic.FinCases

/-!
# Membership in the closure of the three actual second-candidate words

These are certificates for the published words in FiniteIncidence/Words.lean.
Literal binary rows and word decompositions are untrusted witnesses. Each
product is checked by kernel reduction through packedRow_spec, and all group
claims are transferred to the actual matrix subgroup. Source context:
Aschbacher–Smith, Proposition 1.3.4, printed p.511/PDF p.528; Aschbacher (1986).
See Obstructions/source/README.md for the certificate construction.
-/

set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
@[expose] public section
open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound LowerBound.QuotientOrderCertificate
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate

theorem e0_value : value (involutionMatrixSecondGenerator 0) = wordMatrix494 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix494_expansion.symm

theorem e0_inverse_value :
    value ((involutionMatrixSecondGenerator 0)⁻¹) = quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] := by
  apply inverse_value _ _ _ e0_value
  intro i
  fin_cases i <;> rfl

theorem e1_value : value (involutionMatrixSecondGenerator 1) = wordMatrix042 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix042_expansion.symm

theorem e1_inverse_value :
    value ((involutionMatrixSecondGenerator 1)⁻¹) = quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] := by
  apply inverse_value _ _ _ e1_value
  intro i
  fin_cases i <;> rfl

theorem e2_value : value (involutionMatrixSecondGenerator 2) = wordMatrix035 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix035_expansion.symm

theorem e2_inverse_value :
    value ((involutionMatrixSecondGenerator 2)⁻¹) = quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] := by
  apply inverse_value _ _ _ e2_value
  intro i
  fin_cases i <;> rfl

private def s0SecondWord : quotientSubgroup := (involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 1) * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 1) * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2)⁻¹ * ((involutionMatrixSecondGenerator 1)))))))))))

private def s0SecondM9 : QuotientMatrix := quotientDecode #v[1145, 3389, 1722, 675, 4073, 965, 2784, 1323, 2229, 2978, 1047, 2028]

private theorem s0Second_mul9 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] = s0SecondM9 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s0SecondM8 : QuotientMatrix := quotientDecode #v[3369, 2992, 910, 729, 4073, 73, 2735, 3981, 616, 382, 666, 1942]

private theorem s0Second_mul8 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * s0SecondM9 = s0SecondM8 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s0SecondM7 : QuotientMatrix := quotientDecode #v[2792, 498, 3419, 1444, 3263, 1362, 3999, 526, 1410, 3178, 2148, 2408]

private theorem s0Second_mul7 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * s0SecondM8 = s0SecondM7 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s0SecondM6 : QuotientMatrix := quotientDecode #v[1, 1334, 1724, 71, 2421, 4093, 899, 3231, 3428, 1164, 2148, 3778]

private theorem s0Second_mul6 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * s0SecondM7 = s0SecondM6 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s0SecondM5 : QuotientMatrix := quotientDecode #v[2631, 1313, 158, 1875, 2421, 1375, 2048, 2927, 563, 1128, 2163, 2518]

private theorem s0Second_mul5 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * s0SecondM6 = s0SecondM5 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s0SecondM4 : QuotientMatrix := quotientDecode #v[960, 3548, 3344, 164, 1409, 3588, 2754, 2581, 557, 763, 3838, 3521]

private theorem s0Second_mul4 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * s0SecondM5 = s0SecondM4 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s0SecondM3 : QuotientMatrix := quotientDecode #v[4019, 3102, 2144, 3008, 3392, 1540, 2958, 2516, 3064, 2862, 3838, 1904]

private theorem s0Second_mul3 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * s0SecondM4 = s0SecondM3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s0SecondM2 : QuotientMatrix := quotientDecode #v[942, 1760, 2073, 1341, 3392, 1300, 3300, 2084, 1729, 1059, 1024, 2445]

private theorem s0Second_mul2 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * s0SecondM3 = s0SecondM2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s0SecondM1 : QuotientMatrix := quotientDecode #v[3399, 2586, 3992, 1604, 2258, 254, 897, 3496, 3403, 4009, 1024, 1172]

private theorem s0Second_mul1 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * s0SecondM2 = s0SecondM1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s0SecondM0 : QuotientMatrix := quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960]

private theorem s0Second_mul0 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * s0SecondM1 = s0SecondM0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem s0Second_value : value (s0SecondWord) = s0SecondM0 := by
  simp only [s0SecondWord, e2_value, e0_value, e1_value, e2_inverse_value, map_mul]
  change quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100])))))))))) = _
  rw [s0Second_mul9, s0Second_mul8, s0Second_mul7, s0Second_mul6, s0Second_mul5, s0Second_mul4, s0Second_mul3, s0Second_mul2, s0Second_mul1, s0Second_mul0]

theorem s0_second : sylowGenerator 0 ∈ involutionMatrixSecondSubgroup := by
  have heq : sylowGenerator 0 = s0SecondWord := by
    apply value_injective
    rw [s0_value, s0Second_value]
    rfl
  rw [heq]
  exact (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 1) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 1) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (involutionMatrixSecondSubgroup.mul_mem (involutionMatrixSecondSubgroup.inv_mem (secondGenerator_mem 2)) (secondGenerator_mem 1)))))))))))

private def s1SecondWord : quotientSubgroup := (involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 1) * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2)⁻¹ * ((involutionMatrixSecondGenerator 1) * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 1) * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 1)))))))))))

private def s1SecondM9 : QuotientMatrix := quotientDecode #v[110, 2621, 2181, 1716, 705, 2797, 2784, 316, 669, 394, 1047, 251]

private theorem s1Second_mul9 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] = s1SecondM9 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s1SecondM8 : QuotientMatrix := quotientDecode #v[2345, 3248, 3494, 473, 705, 73, 1159, 1458, 1407, 617, 666, 1942]

private theorem s1Second_mul8 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * s1SecondM9 = s1SecondM8 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s1SecondM7 : QuotientMatrix := quotientDecode #v[3816, 3021, 2636, 2971, 1431, 1362, 2184, 1294, 2986, 1602, 2148, 2408]

private theorem s1Second_mul7 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * s1SecondM8 = s1SecondM7 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s1SecondM6 : QuotientMatrix := quotientDecode #v[1025, 545, 1707, 2671, 2677, 469, 1155, 2952, 76, 3492, 2148, 2045]

private theorem s1Second_mul6 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * s1SecondM7 = s1SecondM6 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s1SecondM5 : QuotientMatrix := quotientDecode #v[2640, 566, 1182, 3707, 2677, 3191, 3863, 3183, 2060, 3671, 2163, 1001]

private theorem s1Second_mul5 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * s1SecondM6 = s1SecondM5 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s1SecondM4 : QuotientMatrix := quotientDecode #v[1984, 1251, 3335, 947, 2217, 3347, 1021, 1834, 2066, 2244, 3838, 2046]

private theorem s1Second_mul4 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * s1SecondM5 = s1SecondM4 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s1SecondM3 : QuotientMatrix := quotientDecode #v[1357, 1313, 4, 1577, 1765, 3053, 689, 2581, 1866, 1948, 3838, 3010]

private theorem s1Second_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * s1SecondM4 = s1SecondM3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s1SecondM2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem s1Second_mul2 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * s1SecondM3 = s1SecondM2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s1SecondM1 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem s1Second_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * s1SecondM2 = s1SecondM1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def s1SecondM0 : QuotientMatrix := quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155]

private theorem s1Second_mul0 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * s1SecondM1 = s1SecondM0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem s1Second_value : value (s1SecondWord) = s1SecondM0 := by
  simp only [s1SecondWord, e2_value, e1_value, e0_value, e2_inverse_value, map_mul]
  change quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100])))))))))) = _
  rw [s1Second_mul9, s1Second_mul8, s1Second_mul7, s1Second_mul6, s1Second_mul5, s1Second_mul4, s1Second_mul3, s1Second_mul2, s1Second_mul1, s1Second_mul0]

theorem s1_second : sylowGenerator 1 ∈ involutionMatrixSecondSubgroup := by
  have heq : sylowGenerator 1 = s1SecondWord := by
    apply value_injective
    rw [s1_value, s1Second_value]
    rfl
  rw [heq]
  exact (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 1) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (involutionMatrixSecondSubgroup.mul_mem (involutionMatrixSecondSubgroup.inv_mem (secondGenerator_mem 2)) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 1) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 1) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (secondGenerator_mem 1)))))))))))

private def s2SecondWord : quotientSubgroup := (involutionMatrixSecondGenerator 2)

private theorem s2Second_value : value (s2SecondWord) = quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] := by
  simp only [s2SecondWord, e2_value, map_mul]
  change quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] = _
  rfl

theorem s2_second : sylowGenerator 2 ∈ involutionMatrixSecondSubgroup := by
  have heq : sylowGenerator 2 = s2SecondWord := by
    apply value_injective
    rw [s2_value, s2Second_value]
    rfl
  rw [heq]
  exact (secondGenerator_mem 2)

private def s3SecondWord : quotientSubgroup := (involutionMatrixSecondGenerator 1)

private theorem s3Second_value : value (s3SecondWord) = quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] := by
  simp only [s3SecondWord, e1_value, map_mul]
  change quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] = _
  rfl

theorem s3_second : sylowGenerator 3 ∈ involutionMatrixSecondSubgroup := by
  have heq : sylowGenerator 3 = s3SecondWord := by
    apply value_injective
    rw [s3_value, s3Second_value]
    rfl
  rw [heq]
  exact (secondGenerator_mem 1)

private theorem r65_value : value (representative 65) = wordMatrix323 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix323_expansion.symm

private def r65SecondWord : quotientSubgroup := (involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2)⁻¹ * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2)⁻¹ * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2)))))))))

private def r65SecondM7 : QuotientMatrix := quotientDecode #v[2251, 2104, 1852, 59, 1365, 3898, 742, 2626, 3716, 3943, 2814, 3181]

private theorem r65Second_mul7 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] = r65SecondM7 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r65SecondM6 : QuotientMatrix := quotientDecode #v[3665, 569, 716, 2096, 3134, 4033, 3854, 3022, 3085, 3566, 2814, 1556]

private theorem r65Second_mul6 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * r65SecondM7 = r65SecondM6 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r65SecondM5 : QuotientMatrix := quotientDecode #v[1025, 1593, 1653, 2727, 3134, 1308, 2045, 2516, 1162, 3427, 3838, 1155]

private theorem r65Second_mul5 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * r65SecondM6 = r65SecondM5 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r65SecondM4 : QuotientMatrix := quotientDecode #v[2162, 2799, 3958, 2300, 1432, 1993, 2127, 1259, 2067, 506, 3838, 2196]

private theorem r65Second_mul4 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * r65SecondM5 = r65SecondM4 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r65SecondM3 : QuotientMatrix := quotientDecode #v[1208, 17, 1318, 39, 1432, 1576, 475, 283, 2011, 3281, 1024, 79]

private theorem r65Second_mul3 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * r65SecondM4 = r65SecondM3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r65SecondM2 : QuotientMatrix := quotientDecode #v[2641, 556, 253, 72, 3223, 3166, 64, 2665, 2019, 3305, 1024, 2670]

private theorem r65Second_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * r65SecondM3 = r65SecondM2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r65SecondM1 : QuotientMatrix := quotientDecode #v[1046, 3282, 3127, 2083, 3223, 3267, 2690, 3288, 1982, 563, 2814, 517]

private theorem r65Second_mul1 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * r65SecondM2 = r65SecondM1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r65SecondM0 : QuotientMatrix := quotientDecode #v[2162, 3698, 3344, 2293, 884, 32, 3033, 2841, 3952, 2813, 2814, 1790]

private theorem r65Second_mul0 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * r65SecondM1 = r65SecondM0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem r65Second_value : value (r65SecondWord) = r65SecondM0 := by
  simp only [r65SecondWord, e2_value, e0_value, e2_inverse_value, map_mul]
  change quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184])))))))) = _
  rw [r65Second_mul7, r65Second_mul6, r65Second_mul5, r65Second_mul4, r65Second_mul3, r65Second_mul2, r65Second_mul1, r65Second_mul0]

theorem r65_second : representative 65 ∈ involutionMatrixSecondSubgroup := by
  have heq : representative 65 = r65SecondWord := by
    apply value_injective
    rw [r65_value, r65Second_value]
    rfl
  rw [heq]
  exact (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (involutionMatrixSecondSubgroup.mul_mem (involutionMatrixSecondSubgroup.inv_mem (secondGenerator_mem 2)) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (involutionMatrixSecondSubgroup.mul_mem (involutionMatrixSecondSubgroup.inv_mem (secondGenerator_mem 2)) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (secondGenerator_mem 2)))))))))

private theorem r104_value : value (representative 104) = wordMatrix472 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix472_expansion.symm

private def r104SecondWord : quotientSubgroup := (involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 0) * ((involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 2) * ((involutionMatrixSecondGenerator 0))))))))

private def r104SecondM6 : QuotientMatrix := quotientDecode #v[2251, 34, 1306, 2594, 2942, 3166, 3523, 2026, 1517, 1667, 3838, 144]

private theorem r104Second_mul6 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] = r104SecondM6 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r104SecondM5 : QuotientMatrix := quotientDecode #v[1208, 1900, 1318, 179, 127, 1062, 3778, 1638, 2764, 2466, 3838, 3416]

private theorem r104Second_mul5 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * r104SecondM6 = r104SecondM5 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r104SecondM4 : QuotientMatrix := quotientDecode #v[2162, 3474, 1416, 1515, 127, 32, 1484, 3058, 2589, 366, 1024, 2048]

private theorem r104Second_mul4 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * r104SecondM5 = r104SecondM4 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r104SecondM3 : QuotientMatrix := quotientDecode #v[1691, 842, 914, 1968, 1620, 4066, 538, 1741, 2461, 750, 1024, 1561]

private theorem r104Second_mul3 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * r104SecondM4 = r104SecondM3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r104SecondM2 : QuotientMatrix := quotientDecode #v[3186, 737, 606, 491, 3290, 2194, 1484, 4082, 2507, 696, 1024, 1892]

private theorem r104Second_mul2 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * r104SecondM3 = r104SecondM2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r104SecondM1 : QuotientMatrix := quotientDecode #v[175, 2079, 743, 3031, 3290, 1062, 2307, 1447, 1448, 721, 3838, 3416]

private theorem r104Second_mul1 : quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * r104SecondM2 = r104SecondM1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def r104SecondM0 : QuotientMatrix := quotientDecode #v[546, 2675, 539, 4015, 3271, 2854, 3586, 3797, 160, 2009, 3838, 808]

private theorem r104Second_mul0 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * r104SecondM1 = r104SecondM0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem r104Second_value : value (r104SecondWord) = r104SecondM0 := by
  simp only [r104SecondWord, e2_value, e0_value, map_mul]
  change quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[2630, 2812, 1575, 3661, 16, 3130, 3778, 2200, 1843, 1117, 3838, 1605]))))))) = _
  rw [r104Second_mul6, r104Second_mul5, r104Second_mul4, r104Second_mul3, r104Second_mul2, r104Second_mul1, r104Second_mul0]

theorem r104_second : representative 104 ∈ involutionMatrixSecondSubgroup := by
  have heq : representative 104 = r104SecondWord := by
    apply value_injective
    rw [r104_value, r104Second_value]
    rfl
  rw [heq]
  exact (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 0) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (involutionMatrixSecondSubgroup.mul_mem (secondGenerator_mem 2) (secondGenerator_mem 0))))))))


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
