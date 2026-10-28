module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.LineOverlap.Words
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientOrder.Packed
import Mathlib.Tactic.FinCases

/-!
# Matrix certificates for the line words and a row stabilizer

Every multiplication and inverse in these word evaluations is checked by
packed binary arithmetic. The first two words preserve the specified line;
three further words fix row 895 and supply a small stabilizer for the lower
order bound. Source and witness provenance: `LineOverlap/source/README.md`.
-/

set_option maxRecDepth 100000
@[expose] public section
open Subgroup
open scoped Pointwise
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData
open LowerBound
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.QuotientOrderCertificate
namespace CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.LineOverlapCertificate

def caMatrix : QuotientMatrix := quotientDecode #v[546, 1214, 1213, 426, 1590, 989, 538, 3108, 3826, 1890, 1024, 2016]

def caInverse : QuotientMatrix := quotientDecode #v[546, 548, 3651, 445, 2642, 2990, 1562, 2084, 27, 2443, 1024, 365]

def ca : U where
  val := caMatrix
  inv := caInverse
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def cbMatrix : QuotientMatrix := quotientDecode #v[2050, 301, 1139, 2776, 2379, 264, 1780, 618, 1189, 2982, 23, 3615]

def cbInverse : QuotientMatrix := quotientDecode #v[3774, 414, 2181, 2908, 933, 1561, 3727, 1333, 2940, 724, 1047, 415]

def cb : U where
  val := cbMatrix
  inv := cbInverse
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def c0Matrix : QuotientMatrix := quotientDecode #v[2641, 567, 3587, 2558, 1650, 1372, 2133, 2793, 3022, 3153, 1024, 1655]

def c0Inverse : QuotientMatrix := quotientDecode #v[3664, 2330, 1600, 2529, 285, 1556, 3074, 3689, 1694, 1537, 1024, 1359]

def c0 : U where
  val := c0Matrix
  inv := c0Inverse
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def c1Matrix : QuotientMatrix := quotientDecode #v[2964, 1851, 2491, 2107, 1283, 522, 3782, 2227, 2239, 3872, 1024, 917]

def c1Inverse : QuotientMatrix := quotientDecode #v[2964, 1851, 2491, 2107, 1283, 522, 3782, 2227, 2239, 3872, 1024, 917]

def c1 : U where
  val := c1Matrix
  inv := c1Inverse
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def c2Matrix : QuotientMatrix := quotientDecode #v[2032, 3120, 3587, 1119, 1492, 3299, 2473, 2227, 4048, 3501, 1024, 1069]

def c2Inverse : QuotientMatrix := quotientDecode #v[525, 345, 1600, 1468, 1283, 3569, 419, 2006, 294, 2976, 1024, 3312]

def c2 : U where
  val := c2Matrix
  inv := c2Inverse
  val_inv := by decide +kernel
  inv_val := by decide +kernel

private def caPrefix1 : QuotientMatrix := quotientDecode #v[1977, 940, 2835, 693, 1772, 1021, 1719, 685, 506, 3663, 2609, 2138]

private theorem ca_step1 : matrixX * matrixYInv = caPrefix1 := by
  apply mul_eq_of_packed
  decide +kernel

private def caPrefix2 : QuotientMatrix := quotientDecode #v[1088, 829, 3134, 1113, 1772, 2528, 611, 2224, 2092, 3871, 695, 1082]

private theorem ca_step2 : caPrefix1 * matrixX = caPrefix2 := by
  apply mul_eq_of_packed
  decide +kernel

private def caPrefix3 : QuotientMatrix := quotientDecode #v[2571, 1847, 2235, 3305, 3283, 3742, 3751, 2480, 3410, 2934, 70, 203]

private theorem ca_step3 : caPrefix2 * matrixY = caPrefix3 := by
  apply mul_eq_of_packed
  decide +kernel

private def caPrefix4 : QuotientMatrix := quotientDecode #v[703, 1452, 1306, 24, 16, 101, 2016, 197, 3642, 672, 2970, 3579]

private theorem ca_step4 : caPrefix3 * matrixX = caPrefix4 := by
  apply mul_eq_of_packed
  decide +kernel

private def caPrefix5 : QuotientMatrix := quotientDecode #v[4067, 832, 764, 1437, 2616, 3385, 2721, 1958, 2905, 2074, 1755, 1965]

private theorem ca_step5 : caPrefix4 * matrixY = caPrefix5 := by
  apply mul_eq_of_packed
  decide +kernel

private def caPrefix6 : QuotientMatrix := quotientDecode #v[122, 475, 621, 136, 2920, 1263, 3011, 1341, 3463, 3025, 1314, 650]

private theorem ca_step6 : caPrefix5 * matrixX = caPrefix6 := by
  apply mul_eq_of_packed
  decide +kernel

private def caPrefix7 : QuotientMatrix := quotientDecode #v[2752, 2960, 25, 4029, 934, 3413, 1439, 2591, 3190, 4059, 3558, 3396]

private theorem ca_step7 : caPrefix6 * matrixY = caPrefix7 := by
  apply mul_eq_of_packed
  decide +kernel

private def caPrefix8 : QuotientMatrix := quotientDecode #v[3908, 3604, 1292, 1801, 3439, 942, 3808, 1141, 1218, 3610, 4062, 1688]

private theorem ca_step8 : caPrefix7 * matrixX = caPrefix8 := by
  apply mul_eq_of_packed
  decide +kernel

private def caPrefix9 : QuotientMatrix := quotientDecode #v[527, 942, 992, 1149, 1626, 3936, 569, 3402, 2418, 2440, 3273, 3637]

private theorem ca_step9 : caPrefix8 * matrixYInv = caPrefix9 := by
  apply mul_eq_of_packed
  decide +kernel

private def caPrefix10 : QuotientMatrix := quotientDecode #v[502, 3413, 1781, 2597, 2400, 592, 3037, 723, 1249, 3749, 657, 252]

private theorem ca_step10 : caPrefix9 * matrixX = caPrefix10 := by
  apply mul_eq_of_packed
  decide +kernel

private def caPrefix11 : QuotientMatrix := quotientDecode #v[3242, 908, 2609, 781, 3718, 3355, 281, 3584, 1003, 3256, 3034, 3011]

private theorem ca_step11 : caPrefix10 * matrixY = caPrefix11 := by
  apply mul_eq_of_packed
  decide +kernel

private def caPrefix12 : QuotientMatrix := quotientDecode #v[2174, 436, 695, 3574, 3212, 2062, 1892, 3418, 322, 2757, 4013, 2721]

private theorem ca_step12 : caPrefix11 * matrixX = caPrefix12 := by
  apply mul_eq_of_packed
  decide +kernel

private theorem ca_step13 : caPrefix12 * matrixYInv = caMatrix := by
  apply mul_eq_of_packed
  decide +kernel

theorem ca_eq_word : ca = involutionLineWord quotientX quotientY 0 := by
  apply Units.ext
  change caMatrix = matrixX * matrixYInv * matrixX * matrixY * matrixX * matrixY * matrixX * matrixY * matrixX * matrixYInv * matrixX * matrixY * matrixX * matrixYInv
  symm
  rw [ca_step1, ca_step2, ca_step3, ca_step4, ca_step5, ca_step6, ca_step7, ca_step8, ca_step9, ca_step10, ca_step11, ca_step12, ca_step13]

private def cbPrefix1 : QuotientMatrix := quotientDecode #v[1977, 940, 2835, 693, 1772, 1021, 1719, 685, 506, 3663, 2609, 2138]

private theorem cb_step1 : matrixX * matrixYInv = cbPrefix1 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix2 : QuotientMatrix := quotientDecode #v[1088, 829, 3134, 1113, 1772, 2528, 611, 2224, 2092, 3871, 695, 1082]

private theorem cb_step2 : cbPrefix1 * matrixX = cbPrefix2 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix3 : QuotientMatrix := quotientDecode #v[2571, 1847, 2235, 3305, 3283, 3742, 3751, 2480, 3410, 2934, 70, 203]

private theorem cb_step3 : cbPrefix2 * matrixY = cbPrefix3 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix4 : QuotientMatrix := quotientDecode #v[703, 1452, 1306, 24, 16, 101, 2016, 197, 3642, 672, 2970, 3579]

private theorem cb_step4 : cbPrefix3 * matrixX = cbPrefix4 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix5 : QuotientMatrix := quotientDecode #v[181, 3987, 2374, 128, 1160, 623, 626, 3612, 102, 3318, 3592, 698]

private theorem cb_step5 : cbPrefix4 * matrixYInv = cbPrefix5 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix6 : QuotientMatrix := quotientDecode #v[2049, 459, 162, 1447, 3535, 3220, 897, 2986, 2323, 357, 3424, 2551]

private theorem cb_step6 : cbPrefix5 * matrixX = cbPrefix6 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix7 : QuotientMatrix := quotientDecode #v[2838, 3466, 1960, 685, 2601, 1718, 3653, 878, 3573, 3039, 3729, 2282]

private theorem cb_step7 : cbPrefix6 * matrixYInv = cbPrefix7 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix8 : QuotientMatrix := quotientDecode #v[4034, 2207, 374, 2224, 3678, 2950, 333, 1817, 1152, 3153, 3531, 4039]

private theorem cb_step8 : cbPrefix7 * matrixX = cbPrefix8 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix9 : QuotientMatrix := quotientDecode #v[2381, 3830, 3250, 2480, 1311, 545, 171, 890, 4021, 2651, 1810, 2901]

private theorem cb_step9 : cbPrefix8 * matrixY = cbPrefix9 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix10 : QuotientMatrix := quotientDecode #v[1813, 3389, 1175, 197, 2887, 1844, 153, 467, 1843, 391, 1241, 1956]

private theorem cb_step10 : cbPrefix9 * matrixX = cbPrefix10 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix11 : QuotientMatrix := quotientDecode #v[264, 1424, 1659, 3612, 148, 2571, 2032, 3338, 1736, 238, 196, 2846]

private theorem cb_step11 : cbPrefix10 * matrixYInv = cbPrefix11 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix12 : QuotientMatrix := quotientDecode #v[594, 846, 524, 2986, 877, 703, 628, 3384, 3708, 3214, 85, 4088]

private theorem cb_step12 : cbPrefix11 * matrixX = cbPrefix12 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix13 : QuotientMatrix := quotientDecode #v[847, 3978, 376, 878, 3922, 181, 1167, 648, 721, 3565, 3849, 2825]

private theorem cb_step13 : cbPrefix12 * matrixYInv = cbPrefix13 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix14 : QuotientMatrix := quotientDecode #v[3189, 1223, 995, 1817, 610, 2049, 91, 2501, 802, 2153, 1773, 3775]

private theorem cb_step14 : cbPrefix13 * matrixX = cbPrefix14 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix15 : QuotientMatrix := quotientDecode #v[1201, 3690, 233, 245, 3625, 2838, 1327, 3671, 2816, 2665, 2258, 739]

private theorem cb_step15 : cbPrefix14 * matrixYInv = cbPrefix15 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix16 : QuotientMatrix := quotientDecode #v[2634, 3690, 282, 2026, 1548, 4034, 1309, 1014, 1888, 437, 423, 784]

private theorem cb_step16 : cbPrefix15 * matrixX = cbPrefix16 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix17 : QuotientMatrix := quotientDecode #v[493, 1223, 3409, 1400, 1002, 2381, 152, 3631, 2745, 2575, 75, 13]

private theorem cb_step17 : cbPrefix16 * matrixY = cbPrefix17 := by
  apply mul_eq_of_packed
  decide +kernel

private def cbPrefix18 : QuotientMatrix := quotientDecode #v[2411, 3978, 2487, 2993, 2215, 1813, 2382, 637, 1834, 2214, 2140, 966]

private theorem cb_step18 : cbPrefix17 * matrixX = cbPrefix18 := by
  apply mul_eq_of_packed
  decide +kernel

private theorem cb_step19 : cbPrefix18 * matrixYInv = cbMatrix := by
  apply mul_eq_of_packed
  decide +kernel

theorem cb_eq_word : cb = involutionLineWord quotientX quotientY 1 := by
  apply Units.ext
  change cbMatrix = matrixX * matrixYInv * matrixX * matrixY * matrixX * matrixYInv * matrixX * matrixYInv * matrixX * matrixY * matrixX * matrixYInv * matrixX * matrixYInv * matrixX * matrixYInv * matrixX * matrixY * matrixX * matrixYInv
  symm
  rw [cb_step1, cb_step2, cb_step3, cb_step4, cb_step5, cb_step6, cb_step7, cb_step8, cb_step9, cb_step10, cb_step11, cb_step12, cb_step13, cb_step14, cb_step15, cb_step16, cb_step17, cb_step18, cb_step19]

private def c0Prefix1 : QuotientMatrix := quotientDecode #v[2947, 3805, 2677, 2085, 2859, 3576, 2319, 2916, 2748, 2855, 23, 1520]

private theorem c0_step1 : caInverse * cbMatrix = c0Prefix1 := by
  apply mul_eq_of_packed
  decide +kernel

private def c0Prefix2 : QuotientMatrix := quotientDecode #v[223, 1366, 865, 1698, 744, 2825, 3726, 2826, 3776, 3350, 1047, 3033]

private theorem c0_step2 : c0Prefix1 * caInverse = c0Prefix2 := by
  apply mul_eq_of_packed
  decide +kernel

private def c0Prefix3 : QuotientMatrix := quotientDecode #v[2641, 3667, 253, 2558, 1256, 966, 2114, 2793, 304, 1720, 1024, 3603]

private theorem c0_step3 : c0Prefix2 * cbMatrix = c0Prefix3 := by
  apply mul_eq_of_packed
  decide +kernel

private def c0Prefix4 : QuotientMatrix := quotientDecode #v[1676, 168, 542, 878, 45, 3017, 1363, 3817, 487, 1518, 1024, 1714]

private theorem c0_step4 : c0Prefix3 * caInverse = c0Prefix4 := by
  apply mul_eq_of_packed
  decide +kernel

private theorem c0_step5 : c0Prefix4 * caInverse = c0Matrix := by
  apply mul_eq_of_packed
  decide +kernel

theorem c0_eq_word : c0 = ca⁻¹ * cb * ca⁻¹ * cb * ca⁻¹ * ca⁻¹ := by
  apply Units.ext
  change c0Matrix = caInverse * cbMatrix * caInverse * cbMatrix * caInverse * caInverse
  symm
  rw [c0_step1, c0_step2, c0_step3, c0_step4, c0_step5]

private def c1Prefix1 : QuotientMatrix := quotientDecode #v[862, 2586, 1389, 2336, 3134, 3928, 3082, 945, 3430, 394, 1047, 319]

private theorem c1_step1 : cbMatrix * caMatrix = c1Prefix1 := by
  apply mul_eq_of_packed
  decide +kernel

private def c1Prefix2 : QuotientMatrix := quotientDecode #v[3898, 1799, 1511, 2994, 2509, 1132, 1533, 3368, 2063, 3386, 1024, 2914]

private theorem c1_step2 : c1Prefix1 * cbMatrix = c1Prefix2 := by
  apply mul_eq_of_packed
  decide +kernel

private def c1Prefix3 : QuotientMatrix := quotientDecode #v[701, 584, 3192, 2584, 2189, 2368, 3782, 381, 2459, 2331, 23, 1997]

private theorem c1_step3 : c1Prefix2 * cbMatrix = c1Prefix3 := by
  apply mul_eq_of_packed
  decide +kernel

private def c1Prefix4 : QuotientMatrix := quotientDecode #v[1830, 1930, 2663, 1578, 2780, 3150, 1134, 3259, 620, 6, 1047, 3363]

private theorem c1_step4 : c1Prefix3 * cbMatrix = c1Prefix4 := by
  apply mul_eq_of_packed
  decide +kernel

private def c1Prefix5 : QuotientMatrix := quotientDecode #v[3662, 1184, 868, 1451, 3485, 83, 1134, 3353, 946, 3, 23, 2131]

private theorem c1_step5 : c1Prefix4 * caMatrix = c1Prefix5 := by
  apply mul_eq_of_packed
  decide +kernel

private theorem c1_step6 : c1Prefix5 * cbInverse = c1Matrix := by
  apply mul_eq_of_packed
  decide +kernel

theorem c1_eq_word : c1 = cb * ca * cb * cb * cb * ca * cb⁻¹ := by
  apply Units.ext
  change c1Matrix = cbMatrix * caMatrix * cbMatrix * cbMatrix * cbMatrix * caMatrix * cbInverse
  symm
  rw [c1_step1, c1_step2, c1_step3, c1_step4, c1_step5, c1_step6]

private def c2Prefix1 : QuotientMatrix := quotientDecode #v[1363, 1753, 2553, 658, 2660, 3280, 2995, 2836, 2244, 1207, 1047, 28]

private theorem c2_step1 : caMatrix * cbInverse = c2Prefix1 := by
  apply mul_eq_of_packed
  decide +kernel

private def c2Prefix2 : QuotientMatrix := quotientDecode #v[2114, 2274, 335, 2510, 1528, 3048, 291, 3323, 3427, 4078, 23, 801]

private theorem c2_step2 : c2Prefix1 * caMatrix = c2Prefix2 := by
  apply mul_eq_of_packed
  decide +kernel

private def c2Prefix3 : QuotientMatrix := quotientDecode #v[3726, 3490, 2314, 798, 2609, 3784, 581, 4082, 2370, 964, 1024, 271]

private theorem c2_step3 : c2Prefix2 * cbInverse = c2Prefix3 := by
  apply mul_eq_of_packed
  decide +kernel

private def c2Prefix4 : QuotientMatrix := quotientDecode #v[2328, 1240, 751, 3608, 2872, 869, 1008, 283, 1352, 2541, 1024, 4067]

private theorem c2_step4 : c2Prefix3 * caInverse = c2Prefix4 := by
  apply mul_eq_of_packed
  decide +kernel

private def c2Prefix5 : QuotientMatrix := quotientDecode #v[2345, 1818, 2484, 1597, 903, 1166, 990, 3609, 2206, 2437, 23, 3506]

private theorem c2_step5 : c2Prefix4 * cbMatrix = c2Prefix5 := by
  apply mul_eq_of_packed
  decide +kernel

private def c2Prefix6 : QuotientMatrix := quotientDecode #v[2375, 3762, 1120, 444, 1941, 2445, 49, 316, 3163, 937, 1047, 99]

private theorem c2_step6 : c2Prefix5 * caMatrix = c2Prefix6 := by
  apply mul_eq_of_packed
  decide +kernel

private def c2Prefix7 : QuotientMatrix := quotientDecode #v[969, 1611, 3201, 2092, 3348, 689, 2818, 3353, 3294, 3942, 23, 1974]

private theorem c2_step7 : c2Prefix6 * cbInverse = c2Prefix7 := by
  apply mul_eq_of_packed
  decide +kernel

private theorem c2_step8 : c2Prefix7 * cbInverse = c2Matrix := by
  apply mul_eq_of_packed
  decide +kernel

theorem c2_eq_word : c2 = ca * cb⁻¹ * ca * cb⁻¹ * ca⁻¹ * cb * ca * cb⁻¹ * cb⁻¹ := by
  apply Units.ext
  change c2Matrix = caMatrix * cbInverse * caMatrix * cbInverse * caInverse * cbMatrix * caMatrix * cbInverse * cbInverse
  symm
  rw [c2_step1, c2_step2, c2_step3, c2_step4, c2_step5, c2_step6, c2_step7, c2_step8]

/-- The generated subgroup inside the ambient matrix units. -/
def generatedUnits : Subgroup U :=
  involutionMatrixLineGenerated.map quotientSubgroup.subtype

theorem generator_coe (i : Fin 2) :
    (involutionMatrixLineGenerator i : U) = ![ca, cb] i := by
  fin_cases i
  · exact ca_eq_word.symm
  · exact cb_eq_word.symm

theorem ca_mem : ca ∈ generatedUnits :=
  ⟨involutionMatrixLineGenerator 0, subset_closure ⟨0, rfl⟩, generator_coe 0⟩

theorem cb_mem : cb ∈ generatedUnits :=
  ⟨involutionMatrixLineGenerator 1, subset_closure ⟨1, rfl⟩, generator_coe 1⟩

def gen0 : Fin 4 → U := ![ca, cb, ca⁻¹, cb⁻¹]
def rowStabilizer : Subgroup U := generatedUnits ⊓ stabilizer (row 895)

theorem gen0_mem : ∀ i, gen0 i ∈ generatedUnits := by
  intro i
  fin_cases i
  · exact ca_mem
  · exact cb_mem
  · exact generatedUnits.inv_mem ca_mem
  · exact generatedUnits.inv_mem cb_mem

theorem c0_mem : c0 ∈ rowStabilizer := by
  constructor
  · rw [c0_eq_word]
    exact (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.inv_mem ca_mem) cb_mem) (generatedUnits.inv_mem ca_mem)) cb_mem) (generatedUnits.inv_mem ca_mem)) (generatedUnits.inv_mem ca_mem))
  · show right (row 895) c0 = row 895
    decide +kernel

theorem c1_mem : c1 ∈ rowStabilizer := by
  constructor
  · rw [c1_eq_word]
    exact (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem cb_mem ca_mem) cb_mem) cb_mem) cb_mem) ca_mem) (generatedUnits.inv_mem cb_mem))
  · show right (row 895) c1 = row 895
    decide +kernel

theorem c2_mem : c2 ∈ rowStabilizer := by
  constructor
  · rw [c2_eq_word]
    exact (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem (generatedUnits.mul_mem ca_mem (generatedUnits.inv_mem cb_mem)) ca_mem) (generatedUnits.inv_mem cb_mem)) (generatedUnits.inv_mem ca_mem)) cb_mem) ca_mem) (generatedUnits.inv_mem cb_mem)) (generatedUnits.inv_mem cb_mem))
  · show right (row 895) c2 = row 895
    decide +kernel

def gen1 : Fin 6 → U := ![c0, c1, c2, c0⁻¹, c1⁻¹, c2⁻¹]

theorem gen1_mem : ∀ i, gen1 i ∈ rowStabilizer := by
  intro i
  fin_cases i
  · exact c0_mem
  · exact c1_mem
  · exact c2_mem
  · exact rowStabilizer.inv_mem c0_mem
  · exact rowStabilizer.inv_mem c1_mem
  · exact rowStabilizer.inv_mem c2_mem

def genRows0 : Fin 4 → Vector ℕ 12 :=
  ![#v[546, 1214, 1213, 426, 1590, 989, 538, 3108, 3826, 1890, 1024, 2016],
    #v[2050, 301, 1139, 2776, 2379, 264, 1780, 618, 1189, 2982, 23, 3615],
    #v[546, 548, 3651, 445, 2642, 2990, 1562, 2084, 27, 2443, 1024, 365],
    #v[3774, 414, 2181, 2908, 933, 1561, 3727, 1333, 2940, 724, 1047, 415]]

theorem gen0_val : ∀ i, (gen0 i).val = quotientDecode (genRows0 i) := by
  intro i
  fin_cases i <;> rfl

def genRows1 : Fin 6 → Vector ℕ 12 :=
  ![#v[2641, 567, 3587, 2558, 1650, 1372, 2133, 2793, 3022, 3153, 1024, 1655],
    #v[2964, 1851, 2491, 2107, 1283, 522, 3782, 2227, 2239, 3872, 1024, 917],
    #v[2032, 3120, 3587, 1119, 1492, 3299, 2473, 2227, 4048, 3501, 1024, 1069],
    #v[3664, 2330, 1600, 2529, 285, 1556, 3074, 3689, 1694, 1537, 1024, 1359],
    #v[2964, 1851, 2491, 2107, 1283, 522, 3782, 2227, 2239, 3872, 1024, 917],
    #v[525, 345, 1600, 1468, 1283, 3569, 419, 2006, 294, 2976, 1024, 3312]]

theorem gen1_val : ∀ i, (gen1 i).val = quotientDecode (genRows1 i) := by
  intro i
  fin_cases i <;> rfl

private theorem ca_row23 :
    OuterImageComparison.rowAction ca (involutionMatrixVector 23) =
      involutionMatrixVector 1047 := by
  change Matrix.vecMul (row 23) caInverse = row 1047
  exact vecMul_eq_of_packed _ _ _ (by decide +kernel)

private theorem ca_row1024 :
    OuterImageComparison.rowAction ca (involutionMatrixVector 1024) =
      involutionMatrixVector 1024 := by
  change Matrix.vecMul (row 1024) caInverse = row 1024
  exact vecMul_eq_of_packed _ _ _ (by decide +kernel)

private theorem ca_row1047 :
    OuterImageComparison.rowAction ca (involutionMatrixVector 1047) =
      involutionMatrixVector 23 := by
  change Matrix.vecMul (row 1047) caInverse = row 23
  exact vecMul_eq_of_packed _ _ _ (by decide +kernel)

theorem ca_fixes_line :
    OuterImageComparison.rowAction ca • involutionMatrixLine = involutionMatrixLine := by
  rw [involutionMatrixLine, Set.smul_set_insert, Set.smul_set_insert, Set.smul_set_singleton]
  change {OuterImageComparison.rowAction ca (involutionMatrixVector 23),
    OuterImageComparison.rowAction ca (involutionMatrixVector 1024),
    OuterImageComparison.rowAction ca (involutionMatrixVector 1047)} = _
  rw [ca_row23, ca_row1024, ca_row1047]
  ext v
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private theorem cb_row23 :
    OuterImageComparison.rowAction cb (involutionMatrixVector 23) =
      involutionMatrixVector 1024 := by
  change Matrix.vecMul (row 23) cbInverse = row 1024
  exact vecMul_eq_of_packed _ _ _ (by decide +kernel)

private theorem cb_row1024 :
    OuterImageComparison.rowAction cb (involutionMatrixVector 1024) =
      involutionMatrixVector 1047 := by
  change Matrix.vecMul (row 1024) cbInverse = row 1047
  exact vecMul_eq_of_packed _ _ _ (by decide +kernel)

private theorem cb_row1047 :
    OuterImageComparison.rowAction cb (involutionMatrixVector 1047) =
      involutionMatrixVector 23 := by
  change Matrix.vecMul (row 1047) cbInverse = row 23
  exact vecMul_eq_of_packed _ _ _ (by decide +kernel)

theorem cb_fixes_line :
    OuterImageComparison.rowAction cb • involutionMatrixLine = involutionMatrixLine := by
  rw [involutionMatrixLine, Set.smul_set_insert, Set.smul_set_insert, Set.smul_set_singleton]
  change {OuterImageComparison.rowAction cb (involutionMatrixVector 23),
    OuterImageComparison.rowAction cb (involutionMatrixVector 1024),
    OuterImageComparison.rowAction cb (involutionMatrixVector 1047)} = _
  rw [cb_row23, cb_row1024, cb_row1047]
  ext v
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem lineGenerator_mem (i : Fin 2) :
    involutionMatrixLineGenerator i ∈ involutionMatrixLineStabilizer := by
  change OuterImageComparison.rowAction (involutionMatrixLineGenerator i : U) •
    involutionMatrixLine = involutionMatrixLine
  rw [generator_coe]
  fin_cases i
  · exact ca_fixes_line
  · exact cb_fixes_line

theorem generated_le_stabilizer :
    involutionMatrixLineGenerated ≤ involutionMatrixLineStabilizer := by
  rw [involutionMatrixLineGenerated, closure_le, Set.range_subset_iff]
  exact lineGenerator_mem

end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.LineOverlapCertificate
