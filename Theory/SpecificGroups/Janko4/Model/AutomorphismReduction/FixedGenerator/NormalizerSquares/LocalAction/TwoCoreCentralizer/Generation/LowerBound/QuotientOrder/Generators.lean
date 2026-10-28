module

import Mathlib.Tactic.FinCases
public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreCentralizer.Generation.LowerBound.QuotientOrder.Packed

/-!
# Word certificates for two right-row stabilizers

Three explicit units are certified as words in the preceding generators.
Each matrix product, inverse and fixed-vector identity is kernel checked.
The first two units fix row 1; the third also fixes row 2533. These facts
place the orbit-tree generators in the successive actual stabilizers.
See `source/README.md` for the witness provenance and conventions.
-/

set_option maxRecDepth 100000

@[expose] public section
namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.QuotientOrderCertificate

def aMatrix : QuotientMatrix := quotientDecode #v[1, 1159, 4060, 3530, 1427, 2654, 662, 204, 1694, 803, 1906, 168]

def aInverse : QuotientMatrix := quotientDecode #v[1, 3300, 1976, 2643, 53, 543, 3367, 76, 1951, 2917, 2835, 1880]

def a : U where
  val := aMatrix
  inv := aInverse
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def bMatrix : QuotientMatrix := quotientDecode #v[1, 2061, 810, 2009, 2833, 3559, 3906, 2945, 1962, 2658, 456, 1088]

def bInverse : QuotientMatrix := quotientDecode #v[1, 1402, 1440, 3612, 3371, 3559, 1215, 3515, 792, 1437, 3263, 3007]

def b : U where
  val := bMatrix
  inv := bInverse
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def cMatrix : QuotientMatrix := quotientDecode #v[1, 1904, 4, 198, 1620, 4063, 440, 1732, 4041, 512, 1528, 3722]

def cInverse : QuotientMatrix := quotientDecode #v[1, 1904, 4, 198, 1620, 4063, 440, 1732, 4041, 512, 1528, 3722]

def c : U where
  val := cMatrix
  inv := cInverse
  val_inv := by decide +kernel
  inv_val := by decide +kernel

def gen0 : Fin 3 → U := ![quotientX, quotientY, quotientY⁻¹]
def gen1 : Fin 4 → U := ![a, b, a⁻¹, b⁻¹]
def gen2 : Fin 4 → U := ![b, c, b⁻¹, c⁻¹]

def firstStabilizer : Subgroup U := quotientSubgroup ⊓ stabilizer (row 1)
def secondStabilizer : Subgroup U := firstStabilizer ⊓ stabilizer (row 2533)

theorem gen0_mem : ∀ i, gen0 i ∈ quotientSubgroup := by
  intro i
  fin_cases i
  · exact quotientX_mem
  · exact quotientY_mem
  · exact quotientSubgroup.inv_mem quotientY_mem

private def aPrefix1 : QuotientMatrix := quotientDecode #v[3206, 1211, 3440, 3942, 2623, 3655, 3856, 4070, 513, 1665, 1781, 3641]

private theorem a_step1 : matrixX * matrixY = aPrefix1 := by
  apply mul_eq_of_packed
  decide +kernel

private def aPrefix2 : QuotientMatrix := quotientDecode #v[212, 1048, 731, 1569, 1788, 3877, 993, 902, 1469, 2120, 992, 2783]

private theorem a_step2 : aPrefix1 * matrixX = aPrefix2 := by
  apply mul_eq_of_packed
  decide +kernel

private def aPrefix3 : QuotientMatrix := quotientDecode #v[3809, 2608, 421, 1232, 1771, 1040, 1651, 2870, 2567, 788, 1292, 2517]

private theorem a_step3 : aPrefix2 * matrixY = aPrefix3 := by
  apply mul_eq_of_packed
  decide +kernel

private def aPrefix4 : QuotientMatrix := quotientDecode #v[3194, 2898, 1722, 3789, 2936, 1153, 566, 3403, 2204, 2298, 25, 3675]

private theorem a_step4 : aPrefix3 * matrixX = aPrefix4 := by
  apply mul_eq_of_packed
  decide +kernel

private def aPrefix5 : QuotientMatrix := quotientDecode #v[3194, 3264, 598, 3132, 2462, 3274, 801, 1802, 3573, 975, 1762, 1799]

private theorem a_step5 : aPrefix4 * matrixY = aPrefix5 := by
  apply mul_eq_of_packed
  decide +kernel

private def aPrefix6 : QuotientMatrix := quotientDecode #v[3809, 2894, 2833, 1403, 1543, 1308, 1372, 2096, 1152, 2514, 679, 3062]

private theorem a_step6 : aPrefix5 * matrixX = aPrefix6 := by
  apply mul_eq_of_packed
  decide +kernel

private def aPrefix7 : QuotientMatrix := quotientDecode #v[212, 1649, 1707, 3804, 2027, 1896, 3057, 1181, 3632, 1564, 53, 2690]

private theorem a_step7 : aPrefix6 * matrixYInv = aPrefix7 := by
  apply mul_eq_of_packed
  decide +kernel

private def aPrefix8 : QuotientMatrix := quotientDecode #v[3206, 3166, 1171, 486, 2320, 2874, 2707, 736, 768, 762, 3494, 3783]

private theorem a_step8 : aPrefix7 * matrixX = aPrefix8 := by
  apply mul_eq_of_packed
  decide +kernel

private def aPrefix9 : QuotientMatrix := quotientDecode #v[2533, 97, 910, 1908, 1219, 635, 349, 111, 2357, 2868, 2491, 1812]

private theorem a_step9 : aPrefix8 * matrixYInv = aPrefix9 := by
  apply mul_eq_of_packed
  decide +kernel

private theorem a_step10 : aPrefix9 * matrixX = aMatrix := by
  apply mul_eq_of_packed
  decide +kernel

theorem a_eq_word : a = quotientX * quotientY * quotientX * quotientY * quotientX * quotientY * quotientX * quotientY⁻¹ * quotientX * quotientY⁻¹ * quotientX := by
  apply Units.ext
  change aMatrix = matrixX * matrixY * matrixX * matrixY * matrixX * matrixY * matrixX * matrixYInv * matrixX * matrixYInv * matrixX
  symm
  rw [a_step1, a_step2, a_step3, a_step4, a_step5, a_step6, a_step7, a_step8, a_step9, a_step10]

private def bPrefix1 : QuotientMatrix := quotientDecode #v[559, 2962, 670, 3040, 2920, 3387, 2405, 3305, 685, 2563, 3034, 2687]

private theorem b_step1 : matrixY * matrixX = bPrefix1 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix2 : QuotientMatrix := quotientDecode #v[416, 2560, 2998, 36, 433, 3006, 548, 1113, 4070, 72, 657, 74]

private theorem b_step2 : bPrefix1 * matrixYInv = bPrefix2 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix3 : QuotientMatrix := quotientDecode #v[1350, 1288, 2284, 2192, 112, 2262, 1224, 693, 902, 4049, 3273, 441]

private theorem b_step3 : bPrefix2 * matrixX = bPrefix3 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix4 : QuotientMatrix := quotientDecode #v[928, 2232, 2284, 823, 1305, 1930, 1462, 58, 2870, 118, 4062, 1229]

private theorem b_step4 : bPrefix3 * matrixY = bPrefix4 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix5 : QuotientMatrix := quotientDecode #v[2334, 663, 2998, 3582, 3894, 3479, 1462, 8, 3403, 1472, 3558, 472]

private theorem b_step5 : bPrefix4 * matrixX = bPrefix5 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix6 : QuotientMatrix := quotientDecode #v[1313, 2753, 670, 1461, 3371, 1614, 1697, 4005, 1802, 675, 40, 2195]

private theorem b_step6 : bPrefix5 * matrixY = bPrefix6 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix7 : QuotientMatrix := quotientDecode #v[342, 1697, 359, 571, 1620, 4010, 2753, 3040, 2096, 3323, 691, 1961]

private theorem b_step7 : bPrefix6 * matrixX = bPrefix7 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix8 : QuotientMatrix := quotientDecode #v[3983, 1462, 4, 221, 1740, 2243, 663, 36, 1181, 2826, 328, 2062]

private theorem b_step8 : bPrefix7 * matrixYInv = bPrefix8 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix9 : QuotientMatrix := quotientDecode #v[1851, 1462, 2585, 1369, 1125, 1169, 2232, 2192, 736, 2354, 3513, 3355]

private theorem b_step9 : bPrefix8 * matrixX = bPrefix9 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix10 : QuotientMatrix := quotientDecode #v[704, 1224, 2835, 3305, 2498, 2133, 1288, 2286, 111, 1782, 1528, 592]

private theorem b_step10 : bPrefix9 * matrixYInv = bPrefix10 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix11 : QuotientMatrix := quotientDecode #v[1556, 548, 3134, 24, 3868, 2452, 2560, 1502, 204, 1133, 3606, 3936]

private theorem b_step11 : bPrefix10 * matrixX = bPrefix11 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix12 : QuotientMatrix := quotientDecode #v[1655, 2405, 2235, 1437, 2165, 2784, 2962, 1573, 2940, 3377, 3868, 942]

private theorem b_step12 : bPrefix11 * matrixY = bPrefix12 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix13 : QuotientMatrix := quotientDecode #v[2095, 1446, 1306, 136, 2845, 3533, 124, 1407, 3314, 1237, 2498, 3413]

private theorem b_step13 : bPrefix12 * matrixX = bPrefix13 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix14 : QuotientMatrix := quotientDecode #v[2270, 64, 2374, 405, 1878, 498, 2, 2857, 3567, 313, 660, 1263]

private theorem b_step14 : bPrefix13 * matrixYInv = bPrefix14 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix15 : QuotientMatrix := quotientDecode #v[2948, 4075, 162, 2272, 299, 2070, 3688, 3126, 1537, 1517, 3893, 3385]

private theorem b_step15 : bPrefix14 * matrixX = bPrefix15 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix16 : QuotientMatrix := quotientDecode #v[605, 3856, 2787, 1582, 3729, 564, 1211, 1822, 3671, 1433, 3624, 623]

private theorem b_step16 : bPrefix15 * matrixY = bPrefix16 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix17 : QuotientMatrix := quotientDecode #v[3238, 993, 2624, 712, 3531, 2075, 1048, 3834, 1014, 2705, 4073, 3220]

private theorem b_step17 : bPrefix16 * matrixX = bPrefix17 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix18 : QuotientMatrix := quotientDecode #v[11, 2866, 1511, 3465, 4060, 77, 2861, 2402, 889, 2694, 3436, 1718]

private theorem b_step18 : bPrefix17 * matrixYInv = bPrefix18 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix19 : QuotientMatrix := quotientDecode #v[1975, 1874, 3947, 3858, 910, 3117, 1583, 2098, 1630, 1246, 1067, 2950]

private theorem b_step19 : bPrefix18 * matrixX = bPrefix19 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix20 : QuotientMatrix := quotientDecode #v[1883, 2682, 3848, 1739, 1171, 384, 2670, 2516, 3080, 3733, 2444, 545]

private theorem b_step20 : bPrefix19 * matrixY = bPrefix20 := by
  apply mul_eq_of_packed
  decide +kernel

private def bPrefix21 : QuotientMatrix := quotientDecode #v[749, 2795, 3848, 2545, 1707, 1999, 3105, 1982, 312, 2002, 1212, 1844]

private theorem b_step21 : bPrefix20 * matrixX = bPrefix21 := by
  apply mul_eq_of_packed
  decide +kernel

private theorem b_step22 : bPrefix21 * matrixY = bMatrix := by
  apply mul_eq_of_packed
  decide +kernel

theorem b_eq_word : b = quotientY * quotientX * quotientY⁻¹ * quotientX * quotientY * quotientX * quotientY * quotientX * quotientY⁻¹ * quotientX * quotientY⁻¹ * quotientX * quotientY * quotientX * quotientY⁻¹ * quotientX * quotientY * quotientX * quotientY⁻¹ * quotientX * quotientY * quotientX * quotientY := by
  apply Units.ext
  change bMatrix = matrixY * matrixX * matrixYInv * matrixX * matrixY * matrixX * matrixY * matrixX * matrixYInv * matrixX * matrixYInv * matrixX * matrixY * matrixX * matrixYInv * matrixX * matrixY * matrixX * matrixYInv * matrixX * matrixY * matrixX * matrixY
  symm
  rw [b_step1, b_step2, b_step3, b_step4, b_step5, b_step6, b_step7, b_step8, b_step9, b_step10, b_step11, b_step12, b_step13, b_step14, b_step15, b_step16, b_step17, b_step18, b_step19, b_step20, b_step21, b_step22]

private def cPrefix1 : QuotientMatrix := quotientDecode #v[1, 367, 865, 2357, 3838, 1679, 469, 48, 1988, 2083, 3513, 447]

private theorem c_step1 : aMatrix * bMatrix = cPrefix1 := by
  apply mul_eq_of_packed
  decide +kernel

private def cPrefix2 : QuotientMatrix := quotientDecode #v[1, 2473, 963, 1364, 2400, 308, 3448, 554, 3386, 2466, 992, 1271]

private theorem c_step2 : cPrefix1 * aInverse = cPrefix2 := by
  apply mul_eq_of_packed
  decide +kernel

private def cPrefix3 : QuotientMatrix := quotientDecode #v[1, 1766, 2810, 915, 511, 1652, 3703, 796, 4018, 3457, 614, 1452]

private theorem c_step3 : cPrefix2 * bInverse = cPrefix3 := by
  apply mul_eq_of_packed
  decide +kernel

private def cPrefix4 : QuotientMatrix := quotientDecode #v[1, 1806, 1873, 1124, 3481, 1750, 760, 568, 2529, 393, 176, 2408]

private theorem c_step4 : cPrefix3 * aMatrix = cPrefix4 := by
  apply mul_eq_of_packed
  decide +kernel

private def cPrefix5 : QuotientMatrix := quotientDecode #v[1, 254, 2130, 71, 1386, 3935, 3982, 2893, 2767, 3059, 3447, 1686]

private theorem c_step5 : cPrefix4 * bMatrix = cPrefix5 := by
  apply mul_eq_of_packed
  decide +kernel

private def cPrefix6 : QuotientMatrix := quotientDecode #v[1, 3662, 1710, 1658, 1283, 3245, 498, 2927, 88, 2054, 3972, 2899]

private theorem c_step6 : cPrefix5 * aInverse = cPrefix6 := by
  apply mul_eq_of_packed
  decide +kernel

private def cPrefix7 : QuotientMatrix := quotientDecode #v[1, 2276, 1976, 1591, 2780, 3297, 4010, 2725, 1928, 2917, 2462, 469]

private theorem c_step7 : cPrefix6 * bInverse = cPrefix7 := by
  apply mul_eq_of_packed
  decide +kernel

private theorem c_step8 : cPrefix7 * aMatrix = cMatrix := by
  apply mul_eq_of_packed
  decide +kernel

theorem c_eq_word : c = a * b * a⁻¹ * b⁻¹ * a * b * a⁻¹ * b⁻¹ * a := by
  apply Units.ext
  change cMatrix = aMatrix * bMatrix * aInverse * bInverse * aMatrix * bMatrix * aInverse * bInverse * aMatrix
  symm
  rw [c_step1, c_step2, c_step3, c_step4, c_step5, c_step6, c_step7, c_step8]

theorem a_mem : a ∈ quotientSubgroup := by
  let H := quotientSubgroup
  rw [a_eq_word]
  exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem quotientX_mem quotientY_mem) quotientX_mem) quotientY_mem) quotientX_mem) quotientY_mem) quotientX_mem) (H.inv_mem quotientY_mem)) quotientX_mem) (H.inv_mem quotientY_mem)) quotientX_mem)

theorem b_mem : b ∈ quotientSubgroup := by
  let H := quotientSubgroup
  rw [b_eq_word]
  exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem quotientY_mem quotientX_mem) (H.inv_mem quotientY_mem)) quotientX_mem) quotientY_mem) quotientX_mem) quotientY_mem) quotientX_mem) (H.inv_mem quotientY_mem)) quotientX_mem) (H.inv_mem quotientY_mem)) quotientX_mem) quotientY_mem) quotientX_mem) (H.inv_mem quotientY_mem)) quotientX_mem) quotientY_mem) quotientX_mem) (H.inv_mem quotientY_mem)) quotientX_mem) quotientY_mem) quotientX_mem) quotientY_mem)

theorem gen1_mem : ∀ i, gen1 i ∈ firstStabilizer := by
  have hfix : ∀ i, right (row 1) (gen1 i) = row 1 := by decide +kernel
  intro i
  refine ⟨?_, hfix i⟩
  fin_cases i
  · exact a_mem
  · exact b_mem
  · exact quotientSubgroup.inv_mem a_mem
  · exact quotientSubgroup.inv_mem b_mem

theorem c_mem : c ∈ firstStabilizer := by
  let H := firstStabilizer
  rw [c_eq_word]
  exact (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (H.mul_mem (gen1_mem 0) (gen1_mem 1)) (gen1_mem 2)) (gen1_mem 3)) (gen1_mem 0)) (gen1_mem 1)) (gen1_mem 2)) (gen1_mem 3)) (gen1_mem 0))

theorem gen2_mem : ∀ i, gen2 i ∈ secondStabilizer := by
  have hfix : ∀ i, right (row 2533) (gen2 i) = row 2533 := by decide +kernel
  intro i
  refine ⟨?_, hfix i⟩
  fin_cases i
  · exact gen1_mem 1
  · exact c_mem
  · exact gen1_mem 3
  · exact firstStabilizer.inv_mem c_mem

def genRows0 : Fin 3 → Vector ℕ 12 :=
  ![#v[2533, 3688, 2585, 58, 3283, 649, 4075, 1447, 616, 3160, 2130, 2384],
    #v[895, 124, 359, 4005, 2616, 2695, 1446, 24, 2224, 645, 4013, 2327],
    #v[749, 3035, 1525, 1032, 1160, 2542, 3225, 1437, 2480, 133, 2989, 2555]]

theorem gen0_val : ∀ i, (gen0 i).val = quotientDecode (genRows0 i) := by
  intro i
  fin_cases i <;> rfl

def genRows1 : Fin 4 → Vector ℕ 12 :=
  ![#v[1, 1159, 4060, 3530, 1427, 2654, 662, 204, 1694, 803, 1906, 168],
    #v[1, 2061, 810, 2009, 2833, 3559, 3906, 2945, 1962, 2658, 456, 1088],
    #v[1, 3300, 1976, 2643, 53, 543, 3367, 76, 1951, 2917, 2835, 1880],
    #v[1, 1402, 1440, 3612, 3371, 3559, 1215, 3515, 792, 1437, 3263, 3007]]

theorem gen1_val : ∀ i, (gen1 i).val = quotientDecode (genRows1 i) := by
  intro i
  fin_cases i <;> rfl

def genRows2 : Fin 4 → Vector ℕ 12 :=
  ![#v[1, 2061, 810, 2009, 2833, 3559, 3906, 2945, 1962, 2658, 456, 1088],
    #v[1, 1904, 4, 198, 1620, 4063, 440, 1732, 4041, 512, 1528, 3722],
    #v[1, 1402, 1440, 3612, 3371, 3559, 1215, 3515, 792, 1437, 3263, 3007],
    #v[1, 1904, 4, 198, 1620, 4063, 440, 1732, 4041, 512, 1528, 3722]]

theorem gen2_val : ∀ i, (gen2 i).val = quotientDecode (genRows2 i) := by
  intro i
  fin_cases i <;> rfl

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreCentralizerData.LowerBound.QuotientOrderCertificate
