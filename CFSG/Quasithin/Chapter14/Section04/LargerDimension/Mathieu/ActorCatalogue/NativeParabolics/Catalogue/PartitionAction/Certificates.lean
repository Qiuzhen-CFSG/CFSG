module
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.LinearNormalizer.CoreRecognition.ProjectiveAction
public import Theory.Mathieu.M22.ValueBoundParabolics.Concrete.Geometry

/-!
# Four involutions in the literal hexad-partition preimage

Four explicit even words in the original ATLAS binary matrices have square one.
Their images under the published degree-22 homomorphism preserve exactly
`{{1,2},{3,10},{18,20}}`. Twelve independent rows of their fixed-vector equations
have a checked inverse, so their common fixed space in the column module is zero.

This is the finite calculation used for the partition branch of
Aschbacher--Smith 14.4.12, printed pp.1011--1012, with H.12.1, pp.393--394.
All finite equalities are kernel checked. Matrix attribution is inherited from
`TwoCoreNormalizer/LinearModel/source/`; the small certificate generator and
conventions are documented in `source/README.md` next to this module.
-/
public section
open Matrix Subgroup Sporadic.Mathieu
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix Pointwise
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue.PartitionAction.Certificates

private def matrixOf : derivedGroup →* Matrix12 := (Units.coeHom Matrix12).comp derivedGroup.subtype

private lemma generatorA_matrix : matrixOf coreGeneratorA = fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412] := coe_coreA

private lemma generatorB_matrix : matrixOf coreGeneratorB = fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64] := coe_coreB

private lemma inverseA_matrix : matrixOf (coreGeneratorA⁻¹) = fromRows ![100, 32, 2, 1, 7, 1705, 3524, 8, 16, 561, 2074, 1024] := by
  change ((coreA⁻¹ : Matrix12ˣ) : Matrix12) = _
  apply Units.inv_eq_of_mul_eq_one_right
  change (coreA : Matrix12) * _ = 1
  rw [coe_coreA]
  decide +kernel

private def a2 : derivedGroup := coreGeneratorA * coreGeneratorA

private lemma a2_matrix : matrixOf (a2) = fromRows ![128, 28, 412, 2976, 1639, 4, 400, 2891, 2823, 1513, 1412, 1499] := by
  simp only [a2, map_mul, generatorA_matrix]
  change (fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412]) * (fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412]) = _
  decide +kernel

private def a3 : derivedGroup := a2 * coreGeneratorA

private lemma a3_matrix : matrixOf (a3) = fromRows ![2976, 412, 3163, 2891, 2823, 28, 3271, 122, 249, 1362, 1499, 1108] := by
  simp only [a3, map_mul, a2_matrix, generatorA_matrix]
  change (fromRows ![128, 28, 412, 2976, 1639, 4, 400, 2891, 2823, 1513, 1412, 1499]) * (fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412]) = _
  decide +kernel

private def ai2 : derivedGroup := coreGeneratorA⁻¹ * coreGeneratorA⁻¹

private lemma ai2_matrix : matrixOf (ai2) = fromRows ![2927, 1705, 32, 100, 70, 3311, 452, 1, 7, 1275, 1062, 2074] := by
  simp only [ai2, map_mul, inverseA_matrix]
  change (fromRows ![100, 32, 2, 1, 7, 1705, 3524, 8, 16, 561, 2074, 1024]) * (fromRows ![100, 32, 2, 1, 7, 1705, 3524, 8, 16, 561, 2074, 1024]) = _
  decide +kernel

private def ai3 : derivedGroup := ai2 * coreGeneratorA⁻¹

private lemma ai3_matrix : matrixOf (ai3) = fromRows ![3339, 3311, 1705, 2927, 3558, 1848, 3550, 100, 70, 829, 3729, 1062] := by
  simp only [ai3, map_mul, ai2_matrix, inverseA_matrix]
  change (fromRows ![2927, 1705, 32, 100, 70, 3311, 452, 1, 7, 1275, 1062, 2074]) * (fromRows ![100, 32, 2, 1, 7, 1705, 3524, 8, 16, 561, 2074, 1024]) = _
  decide +kernel

private def ai5 : derivedGroup := ai3 * ai2

private lemma ai5_matrix : matrixOf (ai5) = fromRows ![409, 3220, 1848, 3151, 1944, 3095, 2901, 3339, 1869, 894, 1007, 3648] := by
  simp only [ai5, map_mul, ai3_matrix, ai2_matrix]
  change (fromRows ![3339, 3311, 1705, 2927, 3558, 1848, 3550, 100, 70, 829, 3729, 1062]) * (fromRows ![2927, 1705, 32, 100, 70, 3311, 452, 1, 7, 1275, 1062, 2074]) = _
  decide +kernel

private def raw0 : derivedGroup := ai2 * coreGeneratorB * a2

private lemma raw0_matrix : matrixOf (raw0) = fromRows ![3005, 3006, 1362, 3150, 2304, 652, 3355, 1639, 2748, 3931, 1309, 2732] := by
  simp only [raw0, map_mul, ai2_matrix, generatorB_matrix, a2_matrix]
  change (fromRows ![2927, 1705, 32, 100, 70, 3311, 452, 1, 7, 1275, 1062, 2074]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) * (fromRows ![128, 28, 412, 2976, 1639, 4, 400, 2891, 2823, 1513, 1412, 1499]) = _
  rw [show (fromRows ![2927, 1705, 32, 100, 70, 3311, 452, 1, 7, 1275, 1062, 2074]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) = fromRows ![2917, 1699, 778, 2837, 2077, 1214, 479, 16, 13, 1248, 3916, 75] by decide +kernel]
  decide +kernel

private def actor0 : derivedGroup := raw0

private lemma actor0_matrix : matrixOf (actor0) = fromRows ![3005, 3006, 1362, 3150, 2304, 652, 3355, 1639, 2748, 3931, 1309, 2732] := raw0_matrix

private def raw1 : derivedGroup := coreGeneratorA * coreGeneratorB * a3 * coreGeneratorB * a2 * coreGeneratorB * coreGeneratorA⁻¹ * coreGeneratorB * coreGeneratorA⁻¹

private lemma raw1_matrix : matrixOf (raw1) = fromRows ![572, 529, 2852, 2048, 2375, 922, 3524, 592, 3092, 3076, 531, 1102] := by
  simp only [raw1, map_mul, generatorA_matrix, generatorB_matrix, a3_matrix, a2_matrix, inverseA_matrix]
  change (fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) * (fromRows ![2976, 412, 3163, 2891, 2823, 28, 3271, 122, 249, 1362, 1499, 1108]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) * (fromRows ![128, 28, 412, 2976, 1639, 4, 400, 2891, 2823, 1513, 1412, 1499]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) * (fromRows ![100, 32, 2, 1, 7, 1705, 3524, 8, 16, 561, 2074, 1024]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) * (fromRows ![100, 32, 2, 1, 7, 1705, 3524, 8, 16, 561, 2074, 1024]) = _
  rw [show (fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) = fromRows ![8, 31, 22, 938, 2666, 2, 4, 202, 3356, 32, 64, 1412] by decide +kernel]
  rw [show (fromRows ![8, 31, 22, 938, 2666, 2, 4, 202, 3356, 32, 64, 1412]) * (fromRows ![2976, 412, 3163, 2891, 2823, 28, 3271, 122, 249, 1362, 1499, 1108]) = fromRows ![2891, 1579, 1728, 3866, 1802, 412, 3163, 1642, 3425, 28, 3271, 2307] by decide +kernel]
  rw [show (fromRows ![2891, 1579, 1728, 3866, 1802, 412, 3163, 1642, 3425, 28, 3271, 2307]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) = fromRows ![2160, 1291, 3505, 3130, 3195, 2518, 1024, 3355, 3435, 22, 1980, 2616] by decide +kernel]
  rw [show (fromRows ![2160, 1291, 3505, 3130, 3195, 2518, 1024, 3355, 3435, 22, 1980, 2616]) * (fromRows ![128, 28, 412, 2976, 1639, 4, 400, 2891, 2823, 1513, 1412, 1499]) = fromRows ![552, 1471, 1776, 3456, 3216, 992, 1412, 1539, 496, 2023, 3198, 3569] by decide +kernel]
  rw [show (fromRows ![552, 1471, 1776, 3456, 3216, 992, 1412, 1539, 496, 2023, 3198, 3569]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) = fromRows ![2370, 1685, 3770, 1499, 4016, 2186, 1412, 1545, 715, 1244, 1797, 3776] by decide +kernel]
  rw [show (fromRows ![2370, 1685, 3770, 1499, 4016, 2186, 1412, 1545, 715, 1244, 1797, 3776]) * (fromRows ![100, 32, 2, 1, 7, 1705, 3524, 8, 16, 561, 2074, 1024]) = fromRows ![2548, 2626, 2220, 1412, 2205, 1065, 2048, 2638, 4024, 1490, 2653, 999] by decide +kernel]
  rw [show (fromRows ![2548, 2626, 2220, 1412, 2205, 1065, 2048, 2638, 4024, 1490, 2653, 999]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) = fromRows ![660, 514, 247, 1412, 1004, 3913, 64, 533, 3224, 3480, 518, 2183] by decide +kernel]
  decide +kernel

private def actor1 : derivedGroup := raw1 * raw1 * raw1

private lemma actor1_matrix : matrixOf (actor1) = fromRows ![2646, 1555, 2643, 3810, 2631, 3174, 1324, 3351, 2555, 1900, 364, 1094] := by
  simp only [actor1, map_mul, raw1_matrix]
  change (fromRows ![572, 529, 2852, 2048, 2375, 922, 3524, 592, 3092, 3076, 531, 1102]) * (fromRows ![572, 529, 2852, 2048, 2375, 922, 3524, 592, 3092, 3076, 531, 1102]) * (fromRows ![572, 529, 2852, 2048, 2375, 922, 3524, 592, 3092, 3076, 531, 1102]) = _
  rw [show (fromRows ![572, 529, 2852, 2048, 2375, 922, 3524, 592, 3092, 3076, 531, 1102]) * (fromRows ![572, 529, 2852, 2048, 2375, 922, 3524, 592, 3092, 3076, 531, 1102]) = fromRows ![1533, 1919, 3296, 1102, 3735, 278, 3833, 2183, 1086, 3449, 1390, 3810] by decide +kernel]
  decide +kernel

private def raw2 : derivedGroup := ai5 * coreGeneratorB * ai2 * coreGeneratorB * a3

private lemma raw2_matrix : matrixOf (raw2) = fromRows ![1111, 1739, 3296, 1212, 4049, 3792, 149, 2527, 3046, 3283, 1220, 4026] := by
  simp only [raw2, map_mul, ai5_matrix, generatorB_matrix, ai2_matrix, a3_matrix]
  change (fromRows ![409, 3220, 1848, 3151, 1944, 3095, 2901, 3339, 1869, 894, 1007, 3648]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) * (fromRows ![2927, 1705, 32, 100, 70, 3311, 452, 1, 7, 1275, 1062, 2074]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) * (fromRows ![2976, 412, 3163, 2891, 2823, 28, 3271, 122, 249, 1362, 1499, 1108]) = _
  rw [show (fromRows ![409, 3220, 1848, 3151, 1944, 3095, 2901, 3339, 1869, 894, 1007, 3648]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) = fromRows ![2521, 4015, 3954, 1054, 4050, 3095, 2148, 1643, 1142, 2868, 2191, 3675] by decide +kernel]
  rw [show (fromRows ![2521, 4015, 3954, 1054, 4050, 3095, 2148, 1643, 1142, 2868, 2191, 3675]) * (fromRows ![2927, 1705, 32, 100, 70, 3311, 452, 1, 7, 1275, 1062, 2074]) = fromRows ![661, 2476, 772, 653, 4074, 412, 1297, 84, 4034, 111, 1433, 1255] by decide +kernel]
  rw [show (fromRows ![661, 2476, 772, 653, 4074, 412, 1297, 84, 4034, 111, 1433, 1255]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) = fromRows ![2532, 2717, 53, 2541, 1179, 2518, 1568, 2078, 1945, 2831, 1410, 1270] by decide +kernel]
  decide +kernel

private def actor2 : derivedGroup := raw2 * raw2 * raw2

private lemma actor2_matrix : matrixOf (actor2) = fromRows ![3893, 3694, 4, 3706, 14, 204, 3992, 454, 180, 3380, 2868, 2374] := by
  simp only [actor2, map_mul, raw2_matrix]
  change (fromRows ![1111, 1739, 3296, 1212, 4049, 3792, 149, 2527, 3046, 3283, 1220, 4026]) * (fromRows ![1111, 1739, 3296, 1212, 4049, 3792, 149, 2527, 3046, 3283, 1220, 4026]) * (fromRows ![1111, 1739, 3296, 1212, 4049, 3792, 149, 2527, 3046, 3283, 1220, 4026]) = _
  rw [show (fromRows ![1111, 1739, 3296, 1212, 4049, 3792, 149, 2527, 3046, 3283, 1220, 4026]) * (fromRows ![1111, 1739, 3296, 1212, 4049, 3792, 149, 2527, 3046, 3283, 1220, 4026]) = fromRows ![1532, 1917, 3300, 1094, 3719, 310, 3769, 2055, 1342, 3961, 366, 1762] by decide +kernel]
  decide +kernel

private def raw3 : derivedGroup := ai3 * coreGeneratorB * coreGeneratorA * coreGeneratorB * ai2 * coreGeneratorB * coreGeneratorA * coreGeneratorB * coreGeneratorA

private lemma raw3_matrix : matrixOf (raw3) = fromRows ![3030, 1982, 103, 2724, 3670, 278, 509, 2472, 2233, 3643, 2666, 676] := by
  simp only [raw3, map_mul, ai3_matrix, generatorB_matrix, generatorA_matrix, ai2_matrix]
  change (fromRows ![3339, 3311, 1705, 2927, 3558, 1848, 3550, 100, 70, 829, 3729, 1062]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) * (fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) * (fromRows ![2927, 1705, 32, 100, 70, 3311, 452, 1, 7, 1275, 1062, 2074]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) * (fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) * (fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412]) = _
  rw [show (fromRows ![3339, 3311, 1705, 2927, 3558, 1848, 3550, 100, 70, 829, 3729, 1062]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) = fromRows ![1643, 1214, 1699, 2917, 3788, 3954, 3535, 2837, 2077, 806, 1504, 3916] by decide +kernel]
  rw [show (fromRows ![1643, 1214, 1699, 2917, 3788, 3954, 3535, 2837, 2077, 806, 1504, 3916]) * (fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412]) = fromRows ![2971, 570, 164, 224, 1453, 2544, 204, 509, 1040, 1399, 1498, 2154] by decide +kernel]
  rw [show (fromRows ![2971, 570, 164, 224, 1453, 2544, 204, 509, 1040, 1399, 1498, 2154]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) = fromRows ![987, 2369, 191, 2208, 1686, 651, 3005, 716, 3162, 3383, 3472, 2880] by decide +kernel]
  rw [show (fromRows ![987, 2369, 191, 2208, 1686, 651, 3005, 716, 3162, 3383, 3472, 2880]) * (fromRows ![2927, 1705, 32, 100, 70, 3311, 452, 1, 7, 1275, 1062, 2074]) = fromRows ![2269, 694, 298, 1268, 1555, 2392, 2917, 1402, 2931, 3444, 3196, 3362] by decide +kernel]
  rw [show (fromRows ![2269, 694, 298, 1268, 1555, 2392, 2917, 1402, 2931, 3444, 3196, 3362]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) = fromRows ![3052, 2812, 2410, 1253, 1544, 547, 2927, 3376, 2931, 3429, 1799, 1401] by decide +kernel]
  rw [show (fromRows ![3052, 2812, 2410, 1253, 1544, 547, 2927, 3376, 2931, 3429, 1799, 1401]) * (fromRows ![8, 4, 28, 128, 256, 2, 31, 2976, 1639, 778, 2048, 1412]) = fromRows ![3016, 3247, 890, 937, 2954, 772, 100, 2785, 504, 3050, 3453, 4082] by decide +kernel]
  rw [show (fromRows ![3016, 3247, 890, 937, 2954, 772, 100, 2785, 504, 3050, 3453, 4082]) * (fromRows ![16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) = fromRows ![3016, 3262, 2859, 146, 970, 53, 2837, 688, 707, 2240, 3453, 1170] by decide +kernel]
  decide +kernel

private def actor3 : derivedGroup := raw3 * raw3 * raw3

private lemma actor3_matrix : matrixOf (actor3) = fromRows ![3845, 832, 490, 3150, 850, 32, 367, 3755, 238, 387, 1327, 2732] := by
  simp only [actor3, map_mul, raw3_matrix]
  change (fromRows ![3030, 1982, 103, 2724, 3670, 278, 509, 2472, 2233, 3643, 2666, 676]) * (fromRows ![3030, 1982, 103, 2724, 3670, 278, 509, 2472, 2233, 3643, 2666, 676]) * (fromRows ![3030, 1982, 103, 2724, 3670, 278, 509, 2472, 2233, 3643, 2666, 676]) = _
  rw [show (fromRows ![3030, 1982, 103, 2724, 3670, 278, 509, 2472, 2233, 3643, 2666, 676]) * (fromRows ![3030, 1982, 103, 2724, 3670, 278, 509, 2472, 2233, 3643, 2666, 676]) = fromRows ![1532, 1917, 3300, 1094, 3719, 310, 3769, 2055, 1342, 3961, 366, 1762] by decide +kernel]
  decide +kernel

def involution : Fin 4 → derivedGroup := ![actor0, actor1, actor2, actor3]

def involutionMatrix : Fin 4 → Matrix12 := ![(fromRows ![3005, 3006, 1362, 3150, 2304, 652, 3355, 1639, 2748, 3931, 1309, 2732]), (fromRows ![2646, 1555, 2643, 3810, 2631, 3174, 1324, 3351, 2555, 1900, 364, 1094]), (fromRows ![3893, 3694, 4, 3706, 14, 204, 3992, 454, 180, 3380, 2868, 2374]), (fromRows ![3845, 832, 490, 3150, 850, 32, 367, 3755, 238, 387, 1327, 2732])]

lemma involution_matrix (i : Fin 4) : ((involution i : Matrix12ˣ) : Matrix12) = involutionMatrix i := by
  fin_cases i
  · exact actor0_matrix
  · exact actor1_matrix
  · exact actor2_matrix
  · exact actor3_matrix

lemma involution_square (i : Fin 4) : involution i ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change ((involution i : Matrix12ˣ) : Matrix12) ^ 2 = 1
  rw [involution_matrix, pow_two]
  revert i
  decide +kernel

lemma involution_partition (i : Fin 4) :
    corePermutationAction (involution i) • M22ValueBound.Concrete.hexadPartition =
      M22ValueBound.Concrete.hexadPartition := by
  fin_cases i
  · change corePermutationAction actor0 • _ = _
    simp only [actor0, raw0, a2, ai2, map_mul, map_inv, corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
    decide +kernel
  · change corePermutationAction actor1 • _ = _
    simp only [actor1, raw1, a2, a3, map_mul, map_inv, corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
    decide +kernel
  · change corePermutationAction actor2 • _ = _
    simp only [actor2, raw2, a2, a3, ai2, ai3, ai5, map_mul, map_inv, corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
    decide +kernel
  · change corePermutationAction actor3 • _ = _
    simp only [actor3, raw3, ai2, ai3, map_mul, map_inv, corePermutationAction_coreGeneratorA, corePermutationAction_coreGeneratorB]
    decide +kernel

private def equationActor : Fin 12 → Fin 4 := ![0, 0, 0, 0, 1, 1, 2, 2, 2, 2, 3, 3]

private def equationRow : Fin 12 → Fin 12 := ![0, 2, 3, 6, 0, 6, 0, 1, 3, 5, 0, 6]

private def equations : Matrix12 := fromRows ![3004, 1366, 3142, 3419, 2647, 1388, 3892, 3692, 3698, 236, 3844, 303]

private def elimination : Matrix12 := fromRows ![1935, 3148, 925, 2094, 1663, 575, 1246, 3922, 2639, 1753, 1853, 3126]

private def equationRelation (i j : Fin 12) : Prop := equations i j =
  (involutionMatrix (equationActor i) - 1) (equationRow i) j
private instance : DecidableRel equationRelation := fun i j =>
  inferInstanceAs (Decidable (equations i j =
    (involutionMatrix (equationActor i) - 1) (equationRow i) j))
private lemma equation_rows : ∀ i j,
    equations i j = (involutionMatrix (equationActor i) - 1) (equationRow i) j := by
  change ∀ i j, equationRelation i j
  decide +kernel
private lemma elimination_equations : elimination * equations = 1 := by decide +kernel

/-- The literal column action of the four partition involutions has no
nonzero common fixed vector. -/
lemma eq_zero_of_fixed (v : Fin 12 → ZMod 2)
    (h : ∀ i, involutionMatrix i *ᵥ v = v) : v = 0 := by
  have heq : equations *ᵥ v = 0 := by
    ext i
    have hh : (involutionMatrix (equationActor i) - 1) *ᵥ v = 0 := by
      rw [Matrix.sub_mulVec, h, one_mulVec, sub_self]
    have hrow := congrFun hh (equationRow i)
    simpa only [Matrix.mulVec, dotProduct, equation_rows, Pi.zero_apply] using hrow
  have he := congrArg (fun w => elimination *ᵥ w) heq
  simpa only [mulVec_mulVec, elimination_equations, one_mulVec, mulVec_zero] using he


end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.NativeParabolics.Catalogue.PartitionAction.Certificates
