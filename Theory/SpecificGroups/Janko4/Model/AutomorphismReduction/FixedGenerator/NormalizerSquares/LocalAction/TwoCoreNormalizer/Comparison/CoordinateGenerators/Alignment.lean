module

public import Theory.SpecificGroups.Janko4.Model.AutomorphismReduction.FixedGenerator.NormalizerSquares.LocalAction.TwoCoreNormalizer.Comparison.CoordinateGenerators.RawAction
public import Theory.SpecificGroups.Thompson.Model.GeneratorCertificates.BinaryMatrix

/-!
# Certified change of generators and basis for the twelve-dimensional action

These are finite matrix identities, independent of the unproved realization
of the raw action on the actual two-core quotient. The first new generator is
(xy)^7. The second is the conjugate by xyx of ((xy)^3 y (xy)^2 y (xy)^2)^3.
The explicit matrix P sends their column actions to the unchanged ATLAS C,D.
Conversely, certified words in C,D contain the P-conjugates of the raw x,y;
this reverse inclusion is needed for generation modulo the two-core.

The witnesses were found by binary linear algebra and GAP word factorization.
Every product, inverse, and membership identity below is checked by Lean's
kernel. No group order or recognition output from those programs is used.
Source matrices and attribution: `TwoCoreNormalizer.LinearModel`, online
ATLAS of Finite Group Representations, Wilson, Nickerson and Bray.
-/

@[expose] public section

namespace Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.CoordinateGenerators
open TwoCoreLinearModel
open Thompson.BinaryMatrix (decode rowProduct)

set_option maxRecDepth 10000


private theorem mul_rows {g h : Matrix12ˣ} {r s t : Array ℕ}
    (hg : (g : Matrix12) = decode 12 r) (hh : (h : Matrix12) = decode 12 s)
    (hc : ∀ i : Fin 12, rowProduct r[i.val]! s 12 = t[i.val]!) :
    ((g * h : Matrix12ˣ) : Matrix12) = decode 12 t := by
  rw [Units.val_mul, hg, hh]
  exact Thompson.BinaryMatrix.decode_mul 12 r s t hc

private theorem pow_rows {g : Matrix12ˣ} {m n : ℕ} {r s t : Array ℕ}
    (hg : ((g ^ m : Matrix12ˣ) : Matrix12) = decode 12 r)
    (hh : ((g ^ n : Matrix12ˣ) : Matrix12) = decode 12 s)
    (hc : ∀ i : Fin 12, rowProduct r[i.val]! s 12 = t[i.val]!) :
    ((g ^ (m + n) : Matrix12ˣ) : Matrix12) = decode 12 t := by
  rw [pow_add]
  exact mul_rows hg hh hc

private theorem inv_rows {g : Matrix12ˣ} {r s : Array ℕ}
    (hg : (g : Matrix12) = decode 12 r)
    (hc : ∀ i : Fin 12, rowProduct r[i.val]! s 12 = 2 ^ i.val) :
    ((g⁻¹ : Matrix12ˣ) : Matrix12) = decode 12 s := by
  have h : (g : Matrix12) * decode 12 s = 1 := by
    rw [hg]
    exact Thompson.BinaryMatrix.decode_mul_one 12 r s hc
  calc
    ((g⁻¹ : Matrix12ˣ) : Matrix12) = ((g⁻¹ : Matrix12ˣ) : Matrix12) * 1 :=
      (mul_one _).symm
    _ = ((g⁻¹ : Matrix12ˣ) : Matrix12) * ((g : Matrix12) * decode 12 s) := by rw [h]
    _ = decode 12 s := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]


/-- A certified matrix unit used in the coordinate alignment. -/
def rawUnitX : Matrix12ˣ where
  val := rawMatrixX
  inv := rawMatrixX
  val_inv := by decide +kernel
  inv_val := by decide +kernel

/-- A certified matrix unit used in the coordinate alignment. -/
def rawUnitY : Matrix12ˣ where
  val := rawMatrixY
  inv := fromRows (![4, 2561, 514, 64, 8, 1536, 16, 2592, 512, 2560, 2176, 2816])
  val_inv := by decide +kernel
  inv_val := by decide +kernel

/-- A certified matrix unit used in the coordinate alignment. -/
def basisUnit : Matrix12ˣ where
  val := fromRows (![871, 2540, 1781, 3968, 2970, 761, 2468, 2311, 1894, 3166, 2360, 141])
  inv := fromRows (![976, 2098, 1950, 1387, 3984, 519, 1321, 2341, 3155, 1792, 721, 175])
  val_inv := by decide +kernel
  inv_val := by decide +kernel

private theorem eval_x : (rawUnitX : Matrix12) = decode 12 (#[3073, 2050, 3080, 3076, 1056, 1040, 2304, 2560, 2112, 2176, 1024, 2048]) := by decide +kernel

private theorem eval_y : (rawUnitY : Matrix12) = decode 12 (#[514, 260, 1, 16, 64, 640, 8, 1792, 2560, 256, 288, 768]) := by decide +kernel

private theorem eval_p : (basisUnit : Matrix12) = decode 12 (#[871, 2540, 1781, 3968, 2970, 761, 2468, 2311, 1894, 3166, 2360, 141]) := by decide +kernel

private theorem eval_c : (unitC : Matrix12) = decode 12 (#[2, 1, 7, 32, 64, 8, 16, 512, 1024, 128, 256, 3453]) := by decide +kernel

private theorem eval_d : (unitD : Matrix12) = decode 12 (#[4, 8, 16, 2, 31, 128, 256, 778, 2048, 2976, 1639, 2666]) := by decide +kernel

private def xy : Matrix12ˣ := rawUnitX * rawUnitY

private theorem eval_xy : (xy : Matrix12) = decode 12 (#[34, 516, 560, 545, 928, 352, 2304, 512, 776, 1024, 288, 768]) := by
  exact mul_rows eval_x eval_y (by decide +kernel)

private def firstlr : Matrix12ˣ := xy ^ 2

private theorem eval_firstlr : (firstlr : Matrix12) = decode 12 (#[868, 1584, 1728, 1346, 1128, 2920, 8, 1024, 1321, 288, 616, 1800]) := by
  exact pow_rows (g := xy) (m := 1) (n := 1) (by simpa only [pow_one] using eval_xy) (by simpa only [pow_one] using eval_xy) (by decide +kernel)

private def firstl : Matrix12ˣ := xy ^ 3

private theorem eval_firstl : (firstl : Matrix12) = decode 12 (#[3416, 2016, 3616, 2348, 2913, 3657, 545, 288, 331, 616, 3649, 1033]) := by
  exact pow_rows (g := xy) (m := 1) (n := 2) (by simpa only [pow_one] using eval_xy) eval_firstlr (by decide +kernel)

private def firstrl : Matrix12ˣ := xy ^ 2

private theorem eval_firstrl : (firstrl : Matrix12) = decode 12 (#[868, 1584, 1728, 1346, 1128, 2920, 8, 1024, 1321, 288, 616, 1800]) := by
  exact pow_rows (g := xy) (m := 1) (n := 1) (by simpa only [pow_one] using eval_xy) (by simpa only [pow_one] using eval_xy) (by decide +kernel)

private def firstr : Matrix12ˣ := xy ^ 4

private theorem eval_firstr : (firstr : Matrix12) = decode 12 (#[2473, 3144, 1856, 377, 3146, 3363, 1346, 616, 2575, 3649, 3842, 803]) := by
  exact pow_rows (g := xy) (m := 2) (n := 2) eval_firstrl eval_firstrl (by decide +kernel)

private def first : Matrix12ˣ := xy ^ 7

private theorem eval_first : (first : Matrix12) = decode 12 (#[3679, 325, 3907, 566, 1701, 4082, 2763, 1836, 3029, 1881, 3723, 2002]) := by
  exact pow_rows (g := xy) (m := 3) (n := 4) eval_firstl eval_firstr (by decide +kernel)

private def xy2 : Matrix12ˣ := xy ^ 2

private theorem eval_xy2 : (xy2 : Matrix12) = decode 12 (#[868, 1584, 1728, 1346, 1128, 2920, 8, 1024, 1321, 288, 616, 1800]) := by
  exact pow_rows (g := xy) (m := 1) (n := 1) (by simpa only [pow_one] using eval_xy) (by simpa only [pow_one] using eval_xy) (by decide +kernel)

private def xy3r : Matrix12ˣ := xy ^ 2

private theorem eval_xy3r : (xy3r : Matrix12) = decode 12 (#[868, 1584, 1728, 1346, 1128, 2920, 8, 1024, 1321, 288, 616, 1800]) := by
  exact pow_rows (g := xy) (m := 1) (n := 1) (by simpa only [pow_one] using eval_xy) (by simpa only [pow_one] using eval_xy) (by decide +kernel)

private def xy3 : Matrix12ˣ := xy ^ 3

private theorem eval_xy3 : (xy3 : Matrix12) = decode 12 (#[3416, 2016, 3616, 2348, 2913, 3657, 545, 288, 331, 616, 3649, 1033]) := by
  exact pow_rows (g := xy) (m := 1) (n := 2) (by simpa only [pow_one] using eval_xy) eval_xy3r (by decide +kernel)

private def z1 : Matrix12ˣ := xy3 * rawUnitY

private theorem eval_z1 : (z1 : Matrix12) = decode 12 (#[2168, 4008, 416, 2961, 2186, 314, 386, 2176, 2334, 920, 298, 818]) := by
  exact mul_rows eval_xy3 eval_y (by decide +kernel)

private def z2 : Matrix12ˣ := z1 * xy2

private theorem eval_z2 : (z2 : Matrix12) = decode 12 (#[3394, 2883, 2625, 13, 122, 2395, 1817, 776, 1019, 291, 3379, 3385]) := by
  exact mul_rows eval_z1 eval_xy2 (by decide +kernel)

private def z3 : Matrix12ˣ := z2 * rawUnitY

private theorem eval_z3 : (z3 : Matrix12) = decode 12 (#[2348, 2830, 10, 531, 988, 2654, 2162, 2832, 3550, 2950, 2534, 2290]) := by
  exact mul_rows eval_z2 eval_y (by decide +kernel)

private def z4 : Matrix12ˣ := z3 * xy2

private theorem eval_z4 : (z4 : Matrix12) = decode 12 (#[2763, 1715, 882, 28, 2027, 2042, 3632, 1897, 1435, 2033, 3505, 2608]) := by
  exact mul_rows eval_z3 eval_xy2 (by decide +kernel)

private def zCuber : Matrix12ˣ := z4 ^ 2

private theorem eval_zCuber : (zCuber : Matrix12) = decode 12 (#[2300, 320, 2808, 1157, 3356, 60, 97, 3270, 1228, 3160, 4009, 3536]) := by
  exact pow_rows (g := z4) (m := 1) (n := 1) (by simpa only [pow_one] using eval_z4) (by simpa only [pow_one] using eval_z4) (by decide +kernel)

private def zCube : Matrix12ˣ := z4 ^ 3

private theorem eval_zCube : (zCube : Matrix12) = decode 12 (#[22, 2987, 1173, 865, 1695, 895, 769, 2841, 1926, 3654, 4015, 3240]) := by
  exact pow_rows (g := z4) (m := 1) (n := 2) (by simpa only [pow_one] using eval_z4) eval_zCuber (by decide +kernel)

private def g : Matrix12ˣ := xy * rawUnitX

private theorem eval_g : (g : Matrix12) = decode 12 (#[3090, 1160, 2224, 145, 3792, 1360, 64, 2176, 3268, 1024, 3152, 192]) := by
  exact mul_rows eval_xy eval_x (by decide +kernel)

private def gi : Matrix12ˣ := g⁻¹

private theorem eval_gi : (gi : Matrix12) = decode 12 (#[1736, 1089, 960, 2626, 3712, 3588, 64, 2112, 3296, 3152, 512, 2240]) := by
  exact inv_rows eval_g (by decide +kernel)

private def sec0 : Matrix12ˣ := gi * zCube

private theorem eval_sec0 : (sec0 : Matrix12) = decode 12 (#[2704, 3256, 472, 2628, 1624, 2516, 769, 4009, 2144, 1689, 3654, 1200]) := by
  exact mul_rows eval_gi eval_zCube (by decide +kernel)

private def second : Matrix12ˣ := sec0 * g

private theorem eval_second : (second : Matrix12) = decode 12 (#[656, 3841, 2629, 3120, 1617, 676, 1238, 1287, 1488, 643, 1256, 3920]) := by
  exact mul_rows eval_sec0 eval_g (by decide +kernel)

private def pi : Matrix12ˣ := basisUnit⁻¹

private theorem eval_pi : (pi : Matrix12) = decode 12 (#[976, 2098, 1950, 1387, 3984, 519, 1321, 2341, 3155, 1792, 721, 175]) := by
  exact inv_rows eval_p (by decide +kernel)

private def p_first : Matrix12ˣ := basisUnit * first

private theorem eval_p_first : (p_first : Matrix12) = decode 12 (#[2540, 871, 3198, 761, 2468, 3968, 2970, 3166, 2360, 2311, 1894, 1030]) := by
  exact mul_rows eval_p eval_first (by decide +kernel)

private def conj_first : Matrix12ˣ := p_first * pi

private theorem eval_conj_first : (conj_first : Matrix12) = decode 12 (#[2, 1, 7, 32, 64, 8, 16, 512, 1024, 128, 256, 3453]) := by
  exact mul_rows eval_p_first eval_pi (by decide +kernel)

private def p_second : Matrix12ˣ := basisUnit * second

private theorem eval_p_second : (p_second : Matrix12) = decode 12 (#[1781, 3968, 2970, 2540, 2148, 2311, 1894, 3412, 141, 75, 581, 482]) := by
  exact mul_rows eval_p eval_second (by decide +kernel)

private def conj_second : Matrix12ˣ := p_second * pi

private theorem eval_conj_second : (conj_second : Matrix12) = decode 12 (#[4, 8, 16, 2, 31, 128, 256, 778, 2048, 2976, 1639, 2666]) := by
  exact mul_rows eval_p_second eval_pi (by decide +kernel)

private def p_x : Matrix12ˣ := basisUnit * rawUnitX

private theorem eval_p_x : (p_x : Matrix12) = decode 12 (#[1499, 1884, 4025, 1728, 742, 2997, 600, 2123, 3546, 2350, 3188, 1549]) := by
  exact mul_rows eval_p eval_x (by decide +kernel)

private def conj_x : Matrix12ˣ := p_x * pi

private theorem eval_conj_x : (conj_x : Matrix12) = decode 12 (#[919, 462, 2852, 2525, 1703, 2816, 2258, 2831, 232, 1084, 3422, 1268]) := by
  exact mul_rows eval_p_x eval_pi (by decide +kernel)

private def p_y : Matrix12ˣ := basisUnit * rawUnitY

private theorem eval_p_y : (p_y : Matrix12) = decode 12 (#[2703, 3225, 2027, 3616, 3668, 1754, 3201, 2567, 2477, 893, 3024, 1299]) := by
  exact mul_rows eval_p eval_y (by decide +kernel)

private def conj_y : Matrix12ˣ := p_y * pi

private theorem eval_conj_y : (conj_y : Matrix12) = decode 12 (#[1949, 624, 2304, 1913, 2137, 2836, 2187, 3027, 1787, 712, 2144, 2800]) := by
  exact mul_rows eval_p_y eval_pi (by decide +kernel)

/-- Both the change of generators and the column basis change are certified. -/
theorem align_first : MulAut.conj basisUnit (firstWord rawUnitX rawUnitY) = unitC := by
  apply Units.ext
  exact eval_conj_first.trans eval_c.symm

theorem align_second : MulAut.conj basisUnit (secondWord rawUnitX rawUnitY) = unitD := by
  apply Units.ext
  exact eval_conj_second.trans eval_d.symm

private theorem mem_c : unitC ∈ actionGroup := unitC_mem_actionGroup

private theorem mem_d : unitD ∈ actionGroup := unitD_mem_actionGroup

private def di : Matrix12ˣ := unitD⁻¹

private theorem eval_di : (di : Matrix12) = decode 12 (#[31, 8, 1, 2, 4, 938, 2666, 32, 64, 202, 3356, 256]) := by
  exact inv_rows eval_d (by decide +kernel)

private theorem mem_di : di ∈ actionGroup := actionGroup.inv_mem mem_d

private def wx0 : Matrix12ˣ := di * di

private theorem eval_wx0 : (wx0 : Matrix12) = decode 12 (#[16, 2, 31, 8, 1, 778, 2048, 938, 2666, 2624, 3163, 64]) := by
  exact mul_rows eval_di eval_di (by decide +kernel)

private theorem mem_wx0 : wx0 ∈ actionGroup := actionGroup.mul_mem mem_di mem_di

private def wx1 : Matrix12ˣ := wx0 * unitC

private theorem eval_wx1 : (wx1 : Matrix12) = decode 12 (#[64, 1, 100, 32, 2, 1185, 3453, 1705, 3524, 3565, 3086, 16]) := by
  exact mul_rows eval_wx0 eval_c (by decide +kernel)

private theorem mem_wx1 : wx1 ∈ actionGroup := actionGroup.mul_mem mem_wx0 mem_c

private def wx2 : Matrix12ˣ := wx1 * di

private theorem eval_wx2 : (wx2 : Matrix12) = decode 12 (#[2666, 31, 2497, 938, 8, 3721, 1412, 3649, 1559, 1440, 3095, 4]) := by
  exact mul_rows eval_wx1 eval_di (by decide +kernel)

private theorem mem_wx2 : wx2 ∈ actionGroup := actionGroup.mul_mem mem_wx1 mem_di

private def wx3 : Matrix12ˣ := wx2 * unitC

private theorem eval_wx3 : (wx3 : Matrix12) = decode 12 (#[3524, 100, 2927, 1705, 32, 3807, 1799, 3311, 452, 1800, 3129, 7]) := by
  exact mul_rows eval_wx2 eval_c (by decide +kernel)

private theorem mem_wx3 : wx3 ∈ actionGroup := actionGroup.mul_mem mem_wx2 mem_c

private def wx4 : Matrix12ˣ := wx3 * unitD

private theorem eval_wx4 : (wx4 : Matrix12) = decode 12 (#[1559, 400, 2132, 3659, 128, 1446, 1499, 3737, 2586, 1477, 3220, 28]) := by
  exact mul_rows eval_wx3 eval_d (by decide +kernel)

private theorem mem_wx4 : wx4 ∈ actionGroup := actionGroup.mul_mem mem_wx3 mem_d

private def wx5 : Matrix12ˣ := wx4 * unitC

private theorem eval_wx5 : (wx5 : Matrix12) = decode 12 (#[452, 1600, 3370, 3278, 512, 1806, 1907, 3743, 3484, 1813, 3642, 103]) := by
  exact mul_rows eval_wx4 eval_c (by decide +kernel)

private theorem mem_wx5 : wx5 ∈ actionGroup := actionGroup.mul_mem mem_wx4 mem_c

private def wx6 : Matrix12ˣ := wx5 * unitD

private theorem eval_wx6 : (wx6 : Matrix12) = decode 12 (#[2586, 3271, 1159, 3613, 2976, 1501, 1108, 1190, 1802, 1484, 1848, 412]) := by
  exact mul_rows eval_wx5 eval_d (by decide +kernel)

private theorem mem_wx6 : wx6 ∈ actionGroup := actionGroup.mul_mem mem_wx5 mem_d

private def wx7 : Matrix12ˣ := wx6 * unitC

private theorem eval_wx7 : (wx7 : Matrix12) = decode 12 (#[3484, 3689, 772, 3224, 3061, 1909, 343, 782, 1441, 1847, 1512, 1639]) := by
  exact mul_rows eval_wx6 eval_c (by decide +kernel)

private theorem mem_wx7 : wx7 ∈ actionGroup := actionGroup.mul_mem mem_wx6 mem_c

private def wx8 : Matrix12ˣ := wx7 * unitD

private theorem eval_wx8 : (wx8 : Matrix12) = decode 12 (#[1802, 1579, 944, 3866, 2891, 1100, 2307, 954, 3561, 1348, 3311, 3163]) := by
  exact mul_rows eval_wx7 eval_d (by decide +kernel)

private theorem mem_wx8 : wx8 ∈ actionGroup := actionGroup.mul_mem mem_wx7 mem_d

private def wx9 : Matrix12ˣ := wx8 * unitC

private theorem eval_wx9 : (wx9 : Matrix12) = decode 12 (#[1441, 427, 1736, 2204, 2510, 311, 2430, 1769, 2631, 1303, 3649, 3086]) := by
  exact mul_rows eval_wx8 eval_c (by decide +kernel)

private theorem mem_wx9 : wx9 ∈ actionGroup := actionGroup.mul_mem mem_wx8 mem_c

private def wx10 : Matrix12ˣ := wx9 * di

private theorem eval_wx10 : (wx10 : Matrix12) = decode 12 (#[3785, 991, 1950, 295, 2817, 1016, 2191, 1067, 2998, 3406, 1699, 3095]) := by
  exact mul_rows eval_wx9 eval_di (by decide +kernel)

private theorem mem_wx10 : wx10 ∈ actionGroup := actionGroup.mul_mem mem_wx9 mem_di

private def wx11 : Matrix12ˣ := wx10 * unitC

private theorem eval_wx11 : (wx11 : Matrix12) = decode 12 (#[3791, 1780, 2022, 1036, 2559, 1784, 3929, 299, 2995, 2123, 907, 3129]) := by
  exact mul_rows eval_wx10 eval_c (by decide +kernel)

private theorem mem_wx11 : wx11 ∈ actionGroup := actionGroup.mul_mem mem_wx10 mem_c

private def wx12 : Matrix12ˣ := wx11 * unitD

private theorem eval_wx12 : (wx12 : Matrix12) = decode 12 (#[1465, 3906, 1877, 1653, 225, 3920, 3764, 2190, 2643, 2916, 164, 3220]) := by
  exact mul_rows eval_wx11 eval_d (by decide +kernel)

private theorem mem_wx12 : wx12 ∈ actionGroup := actionGroup.mul_mem mem_wx11 mem_d

private def wx13 : Matrix12ˣ := wx12 * unitC

private theorem eval_wx13 : (wx13 : Matrix12) = decode 12 (#[1898, 2284, 1493, 477, 538, 2221, 3762, 3931, 3502, 2530, 527, 3642]) := by
  exact mul_rows eval_wx12 eval_c (by decide +kernel)

private theorem mem_wx13 : wx13 ∈ actionGroup := actionGroup.mul_mem mem_wx12 mem_c

private def wx14 : Matrix12ˣ := wx13 * unitD

private theorem eval_wx14 : (wx14 : Matrix12) = decode 12 (#[1101, 2290, 3174, 2563, 2997, 2550, 1072, 3772, 1949, 232, 3006, 1848]) := by
  exact mul_rows eval_wx13 eval_d (by decide +kernel)

private theorem mem_wx14 : wx14 ∈ actionGroup := actionGroup.mul_mem mem_wx13 mem_d

private def wx15 : Matrix12ˣ := wx14 * unitC

private theorem eval_wx15 : (wx15 : Matrix12) = decode 12 (#[309, 3876, 3171, 3582, 2992, 2851, 328, 3730, 2021, 568, 2963, 1512]) := by
  exact mul_rows eval_wx14 eval_c (by decide +kernel)

private theorem mem_wx15 : wx15 ∈ actionGroup := actionGroup.mul_mem mem_wx14 mem_c

private def wx16 : Matrix12ˣ := wx15 * unitD

private theorem eval_wx16 : (wx16 : Matrix12) = decode 12 (#[2187, 3901, 3457, 1666, 2655, 2374, 2306, 1200, 1881, 2877, 2771, 3311]) := by
  exact mul_rows eval_wx15 eval_d (by decide +kernel)

private theorem mem_wx16 : wx16 ∈ actionGroup := actionGroup.mul_mem mem_wx15 mem_d

private def wx17 : Matrix12ˣ := wx16 * unitC

private theorem eval_wx17 : (wx17 : Matrix12) = decode 12 (#[3934, 2192, 2687, 897, 3465, 2411, 2428, 840, 1522, 2448, 4014, 3649]) := by
  exact mul_rows eval_wx16 eval_c (by decide +kernel)

private theorem mem_wx17 : wx17 ∈ actionGroup := actionGroup.mul_mem mem_wx16 mem_c

private def wx18 : Matrix12ˣ := wx17 * unitD

private theorem eval_wx18 : (wx18 : Matrix12) = decode 12 (#[3752, 2431, 75, 174, 1793, 996, 999, 674, 3322, 383, 3133, 1705]) := by
  exact mul_rows eval_wx17 eval_d (by decide +kernel)

private theorem mem_wx18 : wx18 ∈ actionGroup := actionGroup.mul_mem mem_wx17 mem_d

private def wx19 : Matrix12ˣ := wx18 * unitC

private theorem eval_wx19 : (wx19 : Matrix12) = decode 12 (#[3797, 2305, 51, 558, 1410, 1695, 1692, 649, 3588, 1148, 3088, 938]) := by
  exact mul_rows eval_wx18 eval_c (by decide +kernel)

private theorem mem_wx19 : wx19 ∈ actionGroup := actionGroup.mul_mem mem_wx18 mem_c

private def wx20 : Matrix12ˣ := wx19 * unitD

private theorem eval_wx20 : (wx20 : Matrix12) = decode 12 (#[1452, 622, 147, 2874, 3429, 3788, 3776, 2220, 1981, 2026, 3090, 32]) := by
  exact mul_rows eval_wx19 eval_d (by decide +kernel)

private theorem mem_wx20 : wx20 ∈ actionGroup := actionGroup.mul_mem mem_wx19 mem_d

private def wx21 : Matrix12ˣ := wx20 * unitC

private theorem eval_wx21 : (wx21 : Matrix12) = decode 12 (#[1839, 190, 579, 2452, 2144, 3786, 3821, 3922, 2029, 1977, 3132, 8]) := by
  exact mul_rows eval_wx20 eval_c (by decide +kernel)

private theorem mem_wx21 : wx21 ∈ actionGroup := actionGroup.mul_mem mem_wx20 mem_c

private def wx22 : Matrix12ˣ := wx21 * di

private theorem eval_wx22 : (wx22 : Matrix12) = decode 12 (#[3624, 901, 2743, 357, 2240, 1686, 1322, 1776, 1130, 3589, 4017, 2]) := by
  exact mul_rows eval_wx21 eval_di (by decide +kernel)

private theorem mem_wx22 : wx22 ∈ actionGroup := actionGroup.mul_mem mem_wx21 mem_di

private def wx23 : Matrix12ˣ := wx22 * unitC

private theorem eval_wx23 : (wx23 : Matrix12) = decode 12 (#[3285, 1669, 4017, 1053, 3949, 966, 1321, 984, 313, 3320, 2743, 1]) := by
  exact mul_rows eval_wx22 eval_c (by decide +kernel)

private theorem mem_wx23 : wx23 ∈ actionGroup := actionGroup.mul_mem mem_wx22 mem_c

private def wx24 : Matrix12ˣ := wx23 * unitD

private theorem eval_wx24 : (wx24 : Matrix12) = decode 12 (#[3596, 3801, 3132, 1646, 3643, 434, 3809, 439, 2201, 3738, 579, 4]) := by
  exact mul_rows eval_wx23 eval_d (by decide +kernel)

private theorem mem_wx24 : wx24 ∈ actionGroup := actionGroup.mul_mem mem_wx23 mem_d

private def wx25 : Matrix12ˣ := wx24 * unitC

private theorem eval_wx25 : (wx25 : Matrix12) = decode 12 (#[3290, 3727, 3090, 446, 3222, 1609, 3815, 1612, 3871, 3740, 147, 7]) := by
  exact mul_rows eval_wx24 eval_c (by decide +kernel)

private theorem mem_wx25 : wx25 ∈ actionGroup := actionGroup.mul_mem mem_wx24 mem_c

private def wx26 : Matrix12ˣ := wx25 * unitD

private theorem eval_wx26 : (wx26 : Matrix12) = decode 12 (#[3602, 1209, 3098, 2959, 3840, 3265, 1339, 3285, 4012, 1194, 793, 28]) := by
  exact mul_rows eval_wx25 eval_d (by decide +kernel)

private theorem mem_wx26 : wx26 ∈ actionGroup := actionGroup.mul_mem mem_wx25 mem_d

private def wx27 : Matrix12ˣ := wx26 * unitD

private theorem eval_wx27 : (wx27 : Matrix12) = decode 12 (#[1978, 1524, 3096, 2782, 4013, 3587, 3830, 3596, 3125, 1511, 953, 13]) := by
  exact mul_rows eval_wx26 eval_d (by decide +kernel)

private theorem mem_wx27 : wx27 ∈ actionGroup := actionGroup.mul_mem mem_wx26 mem_d

private def wx28 : Matrix12ˣ := wx27 * unitC

private theorem eval_wx28 : (wx28 : Matrix12) = decode 12 (#[2025, 1887, 3101, 3979, 2768, 3326, 3747, 3290, 3120, 1820, 1770, 37]) := by
  exact mul_rows eval_wx27 eval_c (by decide +kernel)

private theorem mem_wx28 : wx28 ∈ actionGroup := actionGroup.mul_mem mem_wx27 mem_c

private def wx29 : Matrix12ˣ := wx28 * di

private theorem eval_wx29 : (wx29 : Matrix12) = decode 12 (#[1131, 2028, 3076, 3235, 2948, 1523, 3915, 1624, 4018, 3473, 1084, 948]) := by
  exact mul_rows eval_wx28 eval_di (by decide +kernel)

private theorem mem_wx29 : wx29 ∈ actionGroup := actionGroup.mul_mem mem_wx28 mem_di

private def wx30 : Matrix12ˣ := wx29 * unitC

private theorem eval_wx30 : (wx30 : Matrix12) = decode 12 (#[315, 1983, 3194, 3702, 3066, 1883, 2254, 496, 2740, 2623, 367, 1743]) := by
  exact mul_rows eval_wx29 eval_c (by decide +kernel)

private theorem mem_wx30 : wx30 ∈ actionGroup := actionGroup.mul_mem mem_wx29 mem_c

private def wx31 : Matrix12ˣ := wx30 * unitD

private theorem eval_wx31 : (wx31 : Matrix12) = decode 12 (#[2193, 1612, 3480, 1578, 2901, 1238, 2170, 2709, 591, 331, 2462, 4051]) := by
  exact mul_rows eval_wx30 eval_d (by decide +kernel)

private theorem mem_wx31 : wx31 ∈ actionGroup := actionGroup.mul_mem mem_wx30 mem_d

private def wx32 : Matrix12ˣ := wx31 * unitC

private theorem eval_wx32 : (wx32 : Matrix12) = decode 12 (#[3903, 439, 2589, 425, 2472, 854, 3332, 4024, 180, 1075, 2843, 2734]) := by
  exact mul_rows eval_wx31 eval_c (by decide +kernel)

private theorem mem_wx32 : wx32 ∈ actionGroup := actionGroup.mul_mem mem_wx31 mem_c

private def wx33 : Matrix12ˣ := wx32 * unitD

private theorem eval_wx33 : (wx33 : Matrix12) = decode 12 (#[3884, 2953, 451, 2956, 482, 679, 1053, 3130, 901, 1780, 2523, 602]) := by
  exact mul_rows eval_wx32 eval_d (by decide +kernel)

private theorem mem_wx33 : wx33 ∈ actionGroup := actionGroup.mul_mem mem_wx32 mem_d

private def wx34 : Matrix12ˣ := wx33 * unitD

private theorem eval_wx34 : (wx34 : Matrix12) = decode 12 (#[3903, 2758, 2566, 2770, 2690, 2102, 1646, 3224, 190, 3906, 113, 2741]) := by
  exact mul_rows eval_wx33 eval_d (by decide +kernel)

private theorem mem_wx34 : wx34 ∈ actionGroup := actionGroup.mul_mem mem_wx33 mem_d

private def wx35 : Matrix12ˣ := wx34 * unitC

private theorem eval_wx35 : (wx35 : Matrix12) = decode 12 (#[2193, 4075, 3579, 4012, 4092, 3379, 446, 3613, 622, 2284, 90, 4016]) := by
  exact mul_rows eval_wx34 eval_c (by decide +kernel)

private theorem mem_wx35 : wx35 ∈ actionGroup := actionGroup.mul_mem mem_wx34 mem_c

private def wx36 : Matrix12ˣ := wx35 * unitD

private theorem eval_wx36 : (wx36 : Matrix12) = decode 12 (#[2427, 3369, 1686, 3125, 3370, 1182, 2959, 1956, 2618, 2290, 277, 3128]) := by
  exact mul_rows eval_wx35 eval_d (by decide +kernel)

private theorem mem_wx36 : wx36 ∈ actionGroup := actionGroup.mul_mem mem_wx35 mem_d

private def wx37 : Matrix12ˣ := wx36 * unitC

private theorem eval_wx37 : (wx37 : Matrix12) = decode 12 (#[2310, 2135, 966, 3120, 2132, 870, 3033, 1935, 3476, 3876, 1093, 3093]) := by
  exact mul_rows eval_wx36 eval_c (by decide +kernel)

private theorem mem_wx37 : wx37 ∈ actionGroup := actionGroup.mul_mem mem_wx36 mem_c

private def wx38 : Matrix12ˣ := wx37 * unitD

private theorem eval_wx38 : (wx38 : Matrix12) = decode 12 (#[626, 2921, 434, 3218, 2917, 568, 3033, 1747, 1800, 3901, 1907, 3078]) := by
  exact mul_rows eval_wx37 eval_d (by decide +kernel)

private theorem mem_wx38 : wx38 ∈ actionGroup := actionGroup.mul_mem mem_wx37 mem_d

private def wx39 : Matrix12ˣ := wx38 * unitD

private theorem eval_wx39 : (wx39 : Matrix12) = decode 12 (#[2615, 2124, 2973, 3856, 2142, 2877, 3033, 4062, 1477, 3876, 1108, 3093]) := by
  exact mul_rows eval_wx38 eval_d (by decide +kernel)

private theorem mem_wx39 : wx39 ∈ actionGroup := actionGroup.mul_mem mem_wx38 mem_d

private def wx40 : Matrix12ˣ := wx39 * unitC

private theorem eval_wx40 : (wx40 : Matrix12) = decode 12 (#[3505, 3402, 2968, 2237, 3339, 2448, 2959, 2699, 1813, 2290, 343, 3128]) := by
  exact mul_rows eval_wx39 eval_c (by decide +kernel)

private theorem mem_wx40 : wx40 ∈ actionGroup := actionGroup.mul_mem mem_wx39 mem_c

private def wx41 : Matrix12ˣ := wx40 * di

private theorem eval_wx41 : (wx41 : Matrix12) = decode 12 (#[4045, 1596, 428, 658, 3145, 356, 446, 511, 3468, 2284, 2616, 4016]) := by
  exact mul_rows eval_wx40 eval_di (by decide +kernel)

private theorem mem_wx41 : wx41 ∈ actionGroup := actionGroup.mul_mem mem_wx40 mem_di

private def wx42 : Matrix12ˣ := wx41 * unitC

private theorem eval_wx42 : (wx42 : Matrix12) = decode 12 (#[2760, 495, 1583, 705, 3151, 1055, 1646, 1660, 2650, 3906, 3477, 2741]) := by
  exact mul_rows eval_wx41 eval_c (by decide +kernel)

private theorem mem_wx42 : wx42 ∈ actionGroup := actionGroup.mul_mem mem_wx41 mem_c

private def wx43 : Matrix12ˣ := wx42 * di

private theorem eval_wx43 : (wx43 : Matrix12) = decode 12 (#[2946, 2484, 3688, 2719, 1634, 3340, 1053, 1041, 2990, 1780, 3174, 602]) := by
  exact mul_rows eval_wx42 eval_di (by decide +kernel)

private theorem mem_wx43 : wx43 ∈ actionGroup := actionGroup.mul_mem mem_wx42 mem_di

private def wx44 : Matrix12ˣ := wx43 * unitC

private theorem eval_wx44 : (wx44 : Matrix12) = decode 12 (#[3068, 2866, 3269, 3993, 409, 2138, 357, 322, 3027, 991, 3171, 241]) := by
  exact mul_rows eval_wx43 eval_c (by decide +kernel)

private theorem mem_wx44 : wx44 ∈ actionGroup := actionGroup.mul_mem mem_wx43 mem_c

private def wx45 : Matrix12ˣ := wx44 * unitD

private theorem eval_wx45 : (wx45 : Matrix12) = decode 12 (#[2893, 2397, 3603, 3262, 2835, 2943, 2452, 2312, 3027, 427, 3457, 657]) := by
  exact mul_rows eval_wx44 eval_d (by decide +kernel)

private theorem mem_wx45 : wx45 ∈ actionGroup := actionGroup.mul_mem mem_wx44 mem_d

private def wx46 : Matrix12ˣ := wx45 * unitC

private theorem eval_wx46 : (wx46 : Matrix12) = decode 12 (#[2504, 2312, 3262, 3603, 2494, 2433, 2874, 2397, 2990, 1579, 2687, 706]) := by
  exact mul_rows eval_wx45 eval_c (by decide +kernel)

private theorem mem_wx46 : wx46 ∈ actionGroup := actionGroup.mul_mem mem_wx45 mem_c

private def wx47 : Matrix12ˣ := wx46 * di

private theorem eval_wx47 : (wx47 : Matrix12) = decode 12 (#[2824, 322, 3993, 3269, 709, 383, 558, 2866, 523, 3689, 2074, 2696]) := by
  exact mul_rows eval_wx46 eval_di (by decide +kernel)

private theorem mem_wx47 : wx47 ∈ actionGroup := actionGroup.mul_mem mem_wx46 mem_di

private def wx48 : Matrix12ˣ := wx47 * di

private theorem eval_wx48 : (wx48 : Matrix12) = decode 12 (#[392, 2594, 3247, 1608, 2718, 2448, 875, 556, 223, 1291, 270, 488]) := by
  exact mul_rows eval_wx47 eval_di (by decide +kernel)

private theorem mem_wx48 : wx48 ∈ actionGroup := actionGroup.mul_mem mem_wx47 mem_di

private def wx49 : Matrix12ˣ := wx48 * unitC

private theorem eval_wx49 : (wx49 : Matrix12) = decode 12 (#[1568, 3572, 3665, 432, 3995, 2877, 1211, 175, 628, 1315, 1062, 1592]) := by
  exact mul_rows eval_wx48 eval_c (by decide +kernel)

private theorem mem_wx49 : wx49 ∈ actionGroup := actionGroup.mul_mem mem_wx48 mem_c

private def wx50 : Matrix12ˣ := wx49 * di

private theorem eval_wx50 : (wx50 : Matrix12) = decode 12 (#[3708, 1465, 1703, 974, 3239, 568, 3719, 926, 2319, 3809, 3775, 3706]) := by
  exact mul_rows eval_wx49 eval_di (by decide +kernel)

private theorem mem_wx50 : wx50 ∈ actionGroup := actionGroup.mul_mem mem_wx49 mem_di

private def wx51 : Matrix12ˣ := wx50 * unitC

private theorem eval_wx51 : (wx51 : Matrix12) = decode 12 (#[3202, 1898, 908, 1718, 3697, 232, 3833, 1766, 2393, 3815, 3729, 3204]) := by
  exact mul_rows eval_wx50 eval_c (by decide +kernel)

private theorem mem_wx51 : wx51 ∈ actionGroup := actionGroup.mul_mem mem_wx50 mem_c

private def wx52 : Matrix12ˣ := wx51 * unitD

private theorem eval_wx52 : (wx52 : Matrix12) = decode 12 (#[3855, 1101, 184, 3658, 1590, 648, 1342, 3925, 883, 1339, 1212, 3863]) := by
  exact mul_rows eval_wx51 eval_d (by decide +kernel)

private theorem mem_wx52 : wx52 ∈ actionGroup := actionGroup.mul_mem mem_wx51 mem_d

private def wx53 : Matrix12ˣ := wx52 * unitC

private theorem eval_wx53 : (wx53 : Matrix12) = decode 12 (#[2265, 309, 616, 3276, 462, 672, 1390, 2216, 1243, 1387, 879, 2233]) := by
  exact mul_rows eval_wx52 eval_c (by decide +kernel)

private theorem mem_wx53 : wx53 ∈ actionGroup := actionGroup.mul_mem mem_wx52 mem_c

private def wx54 : Matrix12ˣ := wx53 * unitD

private theorem eval_wx54 : (wx54 : Matrix12) = decode 12 (#[2169, 2187, 2594, 3605, 2576, 2090, 4093, 2530, 1148, 4073, 574, 2553]) := by
  exact mul_rows eval_wx53 eval_d (by decide +kernel)

private theorem mem_wx54 : wx54 ∈ actionGroup := actionGroup.mul_mem mem_wx53 mem_d

private def wx55 : Matrix12ˣ := wx54 * unitC

private theorem eval_wx55 : (wx55 : Matrix12) = decode 12 (#[3335, 3934, 3572, 3256, 3517, 3412, 2688, 2916, 383, 2759, 238, 2823]) := by
  exact mul_rows eval_wx54 eval_c (by decide +kernel)

private theorem mem_wx55 : wx55 ∈ actionGroup := actionGroup.mul_mem mem_wx54 mem_c

private def wx56 : Matrix12ˣ := wx55 * unitD

private theorem eval_wx56 : (wx56 : Matrix12) = decode 12 (#[1041, 3752, 1672, 3994, 1934, 1282, 704, 2138, 2433, 988, 656, 2518]) := by
  exact mul_rows eval_wx55 eval_d (by decide +kernel)

private theorem mem_wx56 : wx56 ∈ actionGroup := actionGroup.mul_mem mem_wx55 mem_d

private def wx57 : Matrix12ˣ := wx56 * unitC

private theorem eval_wx57 : (wx57 : Matrix12) = decode 12 (#[322, 3797, 928, 2716, 1958, 1281, 656, 3340, 2943, 1783, 704, 2859]) := by
  exact mul_rows eval_wx56 eval_c (by decide +kernel)

private theorem mem_wx57 : wx57 ∈ actionGroup := actionGroup.mul_mem mem_wx56 mem_c

private def wx58 : Matrix12ˣ := wx57 * di

private theorem eval_wx58 : (wx58 : Matrix12) = decode 12 (#[2594, 1670, 768, 493, 3605, 3395, 238, 3167, 2138, 1060, 2688, 565]) := by
  exact mul_rows eval_wx57 eval_di (by decide +kernel)

private theorem mem_wx58 : wx58 ∈ actionGroup := actionGroup.mul_mem mem_wx57 mem_di

private def wx59 : Matrix12ˣ := wx58 * di

private theorem eval_wx59 : (wx59 : Matrix12) = decode 12 (#[616, 3583, 138, 2492, 3276, 1569, 2539, 1638, 2916, 3767, 490, 890]) := by
  exact mul_rows eval_wx58 eval_di (by decide +kernel)

private theorem mem_wx59 : wx59 ∈ actionGroup := actionGroup.mul_mem mem_wx58 mem_di

private def wx60 : Matrix12ˣ := wx59 * unitC

private theorem eval_wx60 : (wx60 : Matrix12) = decode 12 (#[184, 2561, 545, 2834, 3658, 394, 2886, 414, 2530, 3761, 1593, 1273]) := by
  exact mul_rows eval_wx59 eval_c (by decide +kernel)

private theorem mem_wx60 : wx60 ∈ actionGroup := actionGroup.mul_mem mem_wx59 mem_c

private def wx61 : Matrix12ˣ := wx60 * unitD

private theorem eval_wx61 : (wx61 : Matrix12) = decode 12 (#[919, 462, 2852, 2525, 1703, 2816, 2258, 2831, 232, 1084, 3422, 1268]) := by
  exact mul_rows eval_wx60 eval_d (by decide +kernel)

private theorem mem_wx61 : wx61 ∈ actionGroup := actionGroup.mul_mem mem_wx60 mem_d

/-- A reverse word certificate, needed to recover the original local generators. -/
theorem conjugated_rawX_mem : MulAut.conj basisUnit rawUnitX ∈ actionGroup := by
  have h : wx61 = MulAut.conj basisUnit rawUnitX := by
    apply Units.ext
    exact eval_wx61.trans eval_conj_x.symm
  exact h ▸ mem_wx61

private def wy0 : Matrix12ˣ := di * unitC

private theorem eval_wy0 : (wy0 : Matrix12) = decode 12 (#[100, 32, 2, 1, 7, 1705, 3524, 8, 16, 561, 2074, 1024]) := by
  exact mul_rows eval_di eval_c (by decide +kernel)

private theorem mem_wy0 : wy0 ∈ actionGroup := actionGroup.mul_mem mem_di mem_c

private def wy1 : Matrix12ˣ := wy0 * di

private theorem eval_wy1 : (wy1 : Matrix12) = decode 12 (#[2497, 938, 8, 31, 22, 3649, 1559, 2, 4, 891, 270, 3356]) := by
  exact mul_rows eval_wy0 eval_di (by decide +kernel)

private theorem mem_wy1 : wy1 ∈ actionGroup := actionGroup.mul_mem mem_wy0 mem_di

private def wy2 : Matrix12ˣ := wy1 * di

private theorem eval_wy2 : (wy2 : Matrix12) = decode 12 (#[2837, 778, 2, 16, 13, 1699, 3524, 8, 1, 2395, 75, 3163]) := by
  exact mul_rows eval_wy1 eval_di (by decide +kernel)

private theorem mem_wy2 : wy2 ∈ actionGroup := actionGroup.mul_mem mem_wy1 mem_di

private def wy3 : Matrix12ˣ := wy2 * unitC

private theorem eval_wy3 : (wy3 : Matrix12) = decode 12 (#[2488, 1185, 1, 64, 37, 907, 2666, 32, 2, 2318, 51, 3086]) := by
  exact mul_rows eval_wy2 eval_c (by decide +kernel)

private theorem mem_wy3 : wy3 ∈ actionGroup := actionGroup.mul_mem mem_wy2 mem_c

private def wy4 : Matrix12ˣ := wy3 * unitD

private theorem eval_wy4 : (wy4 : Matrix12) = decode 12 (#[509, 1513, 4, 256, 148, 164, 64, 128, 8, 624, 147, 3095]) := by
  exact mul_rows eval_wy3 eval_d (by decide +kernel)

private theorem mem_wy4 : wy4 ∈ actionGroup := actionGroup.mul_mem mem_wy3 mem_d

private def wy5 : Matrix12ˣ := wy4 * unitC

private theorem eval_wy5 : (wy5 : Matrix12) = decode 12 (#[1661, 1850, 7, 1024, 583, 527, 16, 512, 32, 216, 579, 3129]) := by
  exact mul_rows eval_wy4 eval_c (by decide +kernel)

private theorem mem_wy5 : wy5 ∈ actionGroup := actionGroup.mul_mem mem_wy4 mem_c

private def wy6 : Matrix12ˣ := wy5 * di

private theorem eval_wy6 : (wy6 : Matrix12) = decode 12 (#[1038, 3634, 22, 3356, 2742, 222, 4, 202, 938, 2636, 2743, 4015]) := by
  exact mul_rows eval_wy5 eval_di (by decide +kernel)

private theorem mem_wy6 : wy6 ∈ actionGroup := actionGroup.mul_mem mem_wy5 mem_di

private def wy7 : Matrix12ˣ := wy6 * unitC

private theorem eval_wy7 : (wy7 : Matrix12) = decode 12 (#[294, 3252, 70, 2074, 4019, 630, 7, 561, 1705, 3530, 4017, 2769]) := by
  exact mul_rows eval_wy6 eval_c (by decide +kernel)

private theorem mem_wy7 : wy7 ∈ actionGroup := actionGroup.mul_mem mem_wy6 mem_c

private def wy8 : Matrix12ˣ := wy7 * di

private theorem eval_wy8 : (wy8 : Matrix12) = decode 12 (#[995, 3987, 2659, 270, 3855, 2311, 22, 891, 3649, 1564, 3847, 2971]) := by
  exact mul_rows eval_wy7 eval_di (by decide +kernel)

private theorem mem_wy8 : wy8 ∈ actionGroup := actionGroup.mul_mem mem_wy7 mem_di

private def wy9 : Matrix12ˣ := wy8 * di

private theorem eval_wy9 : (wy9 : Matrix12) = decode 12 (#[2429, 3237, 2077, 75, 3202, 342, 13, 2395, 1699, 3537, 3200, 443]) := by
  exact mul_rows eval_wy8 eval_di (by decide +kernel)

private theorem mem_wy9 : wy9 ∈ actionGroup := actionGroup.mul_mem mem_wy8 mem_di

private def wy10 : Matrix12ˣ := wy9 * unitC

private theorem eval_wy10 : (wy10 : Matrix12) = decode 12 (#[2304, 3696, 3352, 51, 3708, 1110, 37, 2318, 907, 2607, 3709, 1643]) := by
  exact mul_rows eval_wy9 eval_c (by decide +kernel)

private theorem mem_wy10 : wy10 ∈ actionGroup := actionGroup.mul_mem mem_wy9 mem_c

private def wy11 : Matrix12ˣ := wy10 * di

private theorem eval_wy11 : (wy11 : Matrix12) = decode 12 (#[320, 1298, 3162, 953, 1297, 1915, 948, 331, 191, 628, 1294, 1027]) := by
  exact mul_rows eval_wy10 eval_di (by decide +kernel)

private theorem mem_wy11 : wy11 ∈ actionGroup := actionGroup.mul_mem mem_wy10 mem_di

private def wy12 : Matrix12ˣ := wy11 * unitC

private theorem eval_wy12 : (wy12 : Matrix12) = decode 12 (#[1040, 1345, 3084, 1770, 1346, 1531, 1743, 1075, 620, 223, 1318, 259]) := by
  exact mul_rows eval_wy11 eval_c (by decide +kernel)

private theorem mem_wy12 : wy12 ∈ actionGroup := actionGroup.mul_mem mem_wy11 mem_c

private def wy13 : Matrix12ˣ := wy12 * di

private theorem eval_wy13 : (wy13 : Matrix12) = decode 12 (#[3352, 1833, 3103, 1084, 1854, 1197, 1928, 3749, 2313, 2650, 3839, 87]) := by
  exact mul_rows eval_wy12 eval_di (by decide +kernel)

private theorem mem_wy13 : wy13 ∈ actionGroup := actionGroup.mul_mem mem_wy12 mem_di

private def wy14 : Matrix12ˣ := wy13 * di

private theorem eval_wy14 : (wy14 : Matrix12) = decode 12 (#[3162, 3617, 3084, 3761, 3635, 3722, 3508, 3906, 349, 2990, 1318, 2680]) := by
  exact mul_rows eval_wy13 eval_di (by decide +kernel)

private theorem mem_wy14 : wy14 ∈ actionGroup := actionGroup.mul_mem mem_wy13 mem_di

private def wy15 : Matrix12ˣ := wy14 * unitC

private theorem eval_wy15 : (wy15 : Matrix12) = decode 12 (#[3084, 3319, 3162, 3767, 3254, 3804, 2610, 2284, 1141, 3027, 1294, 3461]) := by
  exact mul_rows eval_wy14 eval_c (by decide +kernel)

private theorem mem_wy15 : wy15 ∈ actionGroup := actionGroup.mul_mem mem_wy14 mem_c

private def wy16 : Matrix12ˣ := wy15 * di

private theorem eval_wy16 : (wy16 : Matrix12) = decode 12 (#[3103, 1518, 1656, 3918, 3995, 1691, 620, 2275, 1222, 3027, 3415, 3170]) := by
  exact mul_rows eval_wy15 eval_di (by decide +kernel)

private theorem mem_wy16 : wy16 ∈ actionGroup := actionGroup.mul_mem mem_wy15 mem_di

private def wy17 : Matrix12ˣ := wy16 * unitC

private theorem eval_wy17 : (wy17 : Matrix12) = decode 12 (#[3097, 1854, 504, 2251, 2718, 995, 191, 3942, 790, 2990, 2089, 3172]) := by
  exact mul_rows eval_wy16 eval_c (by decide +kernel)

private theorem mem_wy17 : wy17 ∈ actionGroup := actionGroup.mul_mem mem_wy16 mem_c

private def wy18 : Matrix12ˣ := wy17 * di

private theorem eval_wy18 : (wy18 : Matrix12) = decode 12 (#[3077, 3635, 2470, 2911, 485, 2429, 922, 1375, 135, 523, 695, 1501]) := by
  exact mul_rows eval_wy17 eval_di (by decide +kernel)

private theorem mem_wy18 : wy18 ∈ actionGroup := actionGroup.mul_mem mem_wy17 mem_di

private def wy19 : Matrix12ˣ := wy18 * unitC

private theorem eval_wy19 : (wy19 : Matrix12) = decode 12 (#[3192, 3254, 2931, 2441, 1565, 2304, 1761, 1396, 516, 163, 716, 1909]) := by
  exact mul_rows eval_wy18 eval_c (by decide +kernel)

private theorem mem_wy19 : wy19 ∈ actionGroup := actionGroup.mul_mem mem_wy18 mem_c

private def wy20 : Matrix12ˣ := wy19 * di

private theorem eval_wy20 : (wy20 : Matrix12) = decode 12 (#[1498, 3995, 2137, 381, 3534, 320, 1065, 1177, 203, 925, 2691, 1100]) := by
  exact mul_rows eval_wy19 eval_di (by decide +kernel)

private theorem mem_wy20 : wy20 ∈ actionGroup := actionGroup.mul_mem mem_wy19 mem_di

private def wy21 : Matrix12ˣ := wy20 * unitC

private theorem eval_wy21 : (wy21 : Matrix12) = decode 12 (#[1905, 2718, 3343, 1149, 2635, 1040, 298, 866, 563, 1765, 4094, 311]) := by
  exact mul_rows eval_wy20 eval_c (by decide +kernel)

private theorem mem_wy21 : wy21 ∈ actionGroup := actionGroup.mul_mem mem_wy20 mem_c

private def wy22 : Matrix12ˣ := wy21 * di

private theorem eval_wy22 : (wy22 : Matrix12) = decode 12 (#[1101, 485, 3144, 1220, 2997, 3352, 992, 2370, 883, 1064, 1401, 1016]) := by
  exact mul_rows eval_wy21 eval_di (by decide +kernel)

private theorem mem_wy22 : wy22 ∈ actionGroup := actionGroup.mul_mem mem_wy21 mem_di

private def wy23 : Matrix12ˣ := wy22 * unitC

private theorem eval_wy23 : (wy23 : Matrix12) = decode 12 (#[309, 1565, 3149, 791, 2992, 2077, 1688, 2412, 1243, 296, 1402, 1784]) := by
  exact mul_rows eval_wy22 eval_c (by decide +kernel)

private theorem mem_wy23 : wy23 ∈ actionGroup := actionGroup.mul_mem mem_wy22 mem_c

private def wy24 : Matrix12ˣ := wy23 * di

private theorem eval_wy24 : (wy24 : Matrix12) = decode 12 (#[1008, 3534, 1642, 152, 516, 280, 3568, 2179, 1863, 1000, 1170, 1072]) := by
  exact mul_rows eval_wy23 eval_di (by decide +kernel)

private theorem mem_wy24 : wy24 ∈ actionGroup := actionGroup.mul_mem mem_wy23 mem_di

private def wy25 : Matrix12ˣ := wy24 * unitC

private theorem eval_wy25 : (wy25 : Matrix12) = decode 12 (#[1752, 2635, 441, 608, 135, 1120, 2597, 3966, 1428, 1720, 833, 328]) := by
  exact mul_rows eval_wy24 eval_c (by decide +kernel)

private theorem mem_wy25 : wy25 ∈ actionGroup := actionGroup.mul_mem mem_wy24 mem_c

private def wy26 : Matrix12ˣ := wy25 * unitD

private theorem eval_wy26 : (wy26 : Matrix12) = decode 12 (#[4048, 196, 2963, 2592, 790, 2023, 350, 3624, 3426, 3664, 676, 2306]) := by
  exact mul_rows eval_wy25 eval_d (by decide +kernel)

private theorem mem_wy26 : wy26 ∈ actionGroup := actionGroup.mul_mem mem_wy25 mem_d

private def wy27 : Matrix12ˣ := wy26 * unitD

private theorem eval_wy27 : (wy27 : Matrix12) = decode 12 (#[3512, 538, 2771, 330, 935, 1873, 2309, 1839, 1413, 1714, 2106, 610]) := by
  exact mul_rows eval_wy26 eval_d (by decide +kernel)

private theorem mem_wy27 : wy27 ∈ actionGroup := actionGroup.mul_mem mem_wy26 mem_d

private def wy28 : Matrix12ˣ := wy27 * unitC

private theorem eval_wy28 : (wy28 : Matrix12) = decode 12 (#[2581, 225, 4014, 1073, 1676, 1490, 2424, 1452, 1797, 969, 3348, 153]) := by
  exact mul_rows eval_wy27 eval_c (by decide +kernel)

private theorem mem_wy28 : wy28 ∈ actionGroup := actionGroup.mul_mem mem_wy27 mem_c

private def wy29 : Matrix12ˣ := wy28 * unitD

private theorem eval_wy29 : (wy29 : Matrix12) = decode 12 (#[449, 654, 3133, 1788, 3807, 3194, 1015, 3583, 1491, 428, 1026, 787]) := by
  exact mul_rows eval_wy28 eval_d (by decide +kernel)

private theorem mem_wy29 : wy29 ∈ actionGroup := actionGroup.mul_mem mem_wy28 mem_d

private def wy30 : Matrix12ˣ := wy29 * unitC

private theorem eval_wy30 : (wy30 : Matrix12) = decode 12 (#[1554, 678, 3088, 1023, 3721, 3076, 1756, 2561, 1875, 1583, 257, 1219]) := by
  exact mul_rows eval_wy29 eval_c (by decide +kernel)

private theorem mem_wy30 : wy30 ∈ actionGroup := actionGroup.mul_mem mem_wy29 mem_c

private def wy31 : Matrix12ˣ := wy30 * di

private theorem eval_wy31 : (wy31 : Matrix12) = decode 12 (#[3546, 841, 3096, 2426, 3307, 3101, 1947, 469, 2031, 3688, 95, 1857]) := by
  exact mul_rows eval_wy30 eval_di (by decide +kernel)

private theorem mem_wy31 : wy31 ∈ actionGroup := actionGroup.mul_mem mem_wy30 mem_di

private def wy32 : Matrix12ˣ := wy31 * unitC

private theorem eval_wy32 : (wy32 : Matrix12) = decode 12 (#[2572, 1202, 3101, 2308, 3654, 3096, 2019, 1621, 1980, 3269, 116, 1426]) := by
  exact mul_rows eval_wy31 eval_c (by decide +kernel)

private theorem mem_wy32 : wy32 ∈ actionGroup := actionGroup.mul_mem mem_wy31 mem_c

private def wy33 : Matrix12ˣ := wy32 * di

private theorem eval_wy33 : (wy33 : Matrix12) = decode 12 (#[457, 3738, 3076, 321, 1717, 3098, 1121, 1958, 3611, 1608, 2501, 3440]) := by
  exact mul_rows eval_wy32 eval_di (by decide +kernel)

private theorem mem_wy33 : wy33 ∈ actionGroup := actionGroup.mul_mem mem_wy32 mem_di

private def wy34 : Matrix12ˣ := wy33 * unitC

private theorem eval_wy34 : (wy34 : Matrix12) = decode 12 (#[1586, 3740, 3194, 1042, 973, 3100, 282, 1934, 3230, 432, 2920, 2085]) := by
  exact mul_rows eval_wy33 eval_c (by decide +kernel)

private theorem mem_wy34 : wy34 ∈ actionGroup := actionGroup.mul_mem mem_wy33 mem_c

private def wy35 : Matrix12ˣ := wy34 * unitD

private theorem eval_wy35 : (wy35 : Matrix12) = decode 12 (#[3408, 1194, 3480, 1648, 444, 3072, 2069, 1751, 3842, 2965, 2120, 2814]) := by
  exact mul_rows eval_wy34 eval_d (by decide +kernel)

private theorem mem_wy35 : wy35 ∈ actionGroup := actionGroup.mul_mem mem_wy34 mem_d

private def wy36 : Matrix12ˣ := wy35 * unitC

private theorem eval_wy36 : (wy36 : Matrix12) = decode 12 (#[2093, 809, 2589, 472, 1647, 3197, 3384, 980, 2300, 3000, 3405, 3971]) := by
  exact mul_rows eval_wy35 eval_c (by decide +kernel)

private theorem mem_wy36 : wy36 ∈ actionGroup := actionGroup.mul_mem mem_wy35 mem_c

private def wy37 : Matrix12ˣ := wy36 * unitD

private theorem eval_wy37 : (wy37 : Matrix12) = decode 12 (#[2812, 806, 451, 2583, 3161, 3460, 1168, 421, 2285, 2653, 1307, 3243]) := by
  exact mul_rows eval_wy36 eval_d (by decide +kernel)

private theorem mem_wy37 : wy37 ∈ actionGroup := actionGroup.mul_mem mem_wy36 mem_d

private def wy38 : Matrix12ˣ := wy37 * unitC

private theorem eval_wy38 : (wy38 : Matrix12) = decode 12 (#[3970, 1166, 1555, 3513, 3087, 2682, 832, 1549, 3904, 3464, 1379, 3670]) := by
  exact mul_rows eval_wy37 eval_c (by decide +kernel)

private theorem mem_wy38 : wy38 ∈ actionGroup := actionGroup.mul_mem mem_wy37 mem_c

private def wy39 : Matrix12ˣ := wy38 * unitD

private theorem eval_wy39 : (wy39 : Matrix12) = decode 12 (#[3247, 1399, 3540, 1950, 3091, 95, 672, 3537, 3757, 1797, 4075, 1706]) := by
  exact mul_rows eval_wy38 eval_d (by decide +kernel)

private theorem mem_wy39 : wy39 ∈ actionGroup := actionGroup.mul_mem mem_wy38 mem_d

private def wy40 : Matrix12ˣ := wy39 * unitC

private theorem eval_wy40 : (wy40 : Matrix12) = decode 12 (#[3665, 1372, 2602, 2022, 3134, 116, 648, 2607, 3792, 1413, 2758, 937]) := by
  exact mul_rows eval_wy39 eval_c (by decide +kernel)

private theorem mem_wy40 : wy40 ∈ actionGroup := actionGroup.mul_mem mem_wy39 mem_c

private def wy41 : Matrix12ˣ := wy40 * di

private theorem eval_wy41 : (wy41 : Matrix12) = decode 12 (#[1703, 1841, 618, 1151, 4025, 2501, 232, 628, 1688, 3426, 2953, 797]) := by
  exact mul_rows eval_wy40 eval_di (by decide +kernel)

private theorem mem_wy41 : wy41 ∈ actionGroup := actionGroup.mul_mem mem_wy40 mem_di

private def wy42 : Matrix12ˣ := wy41 * unitC

private theorem eval_wy42 : (wy42 : Matrix12) = decode 12 (#[908, 1482, 185, 380, 2711, 2920, 568, 223, 992, 2148, 3039, 1253]) := by
  exact mul_rows eval_wy41 eval_c (by decide +kernel)

private theorem mem_wy42 : wy42 ∈ actionGroup := actionGroup.mul_mem mem_wy41 mem_c

private def wy43 : Matrix12ˣ := wy42 * di

private theorem eval_wy43 : (wy43 : Matrix12) = decode 12 (#[169, 1820, 915, 2439, 504, 2120, 870, 2650, 2410, 2241, 3024, 1250]) := by
  exact mul_rows eval_wy42 eval_di (by decide +kernel)

private theorem mem_wy43 : wy43 ∈ actionGroup := actionGroup.mul_mem mem_wy42 mem_di

private def wy44 : Matrix12ˣ := wy43 * di

private theorem eval_wy44 : (wy44 : Matrix12) = decode 12 (#[919, 3473, 185, 374, 2470, 2920, 2371, 2990, 2186, 2901, 3012, 1268]) := by
  exact mul_rows eval_wy43 eval_di (by decide +kernel)

private theorem mem_wy44 : wy44 ∈ actionGroup := actionGroup.mul_mem mem_wy43 mem_di

private def wy45 : Matrix12ˣ := wy44 * unitC

private theorem eval_wy45 : (wy45 : Matrix12) = decode 12 (#[1732, 2623, 618, 1118, 2931, 2501, 2414, 3027, 3932, 2472, 3050, 863]) := by
  exact mul_rows eval_wy44 eval_c (by decide +kernel)

private theorem mem_wy45 : wy45 ∈ actionGroup := actionGroup.mul_mem mem_wy44 mem_c

private def wy46 : Matrix12ˣ := wy45 * di

private theorem eval_wy46 : (wy46 : Matrix12) = decode 12 (#[1949, 624, 2304, 1913, 2137, 2836, 2187, 3027, 1787, 712, 2144, 2800]) := by
  exact mul_rows eval_wy45 eval_di (by decide +kernel)

private theorem mem_wy46 : wy46 ∈ actionGroup := actionGroup.mul_mem mem_wy45 mem_di

/-- A reverse word certificate, needed to recover the original local generators. -/
theorem conjugated_rawY_mem : MulAut.conj basisUnit rawUnitY ∈ actionGroup := by
  have h : wy46 = MulAut.conj basisUnit rawUnitY := by
    apply Units.ext
    exact eval_wy46.trans eval_conj_y.symm
  exact h ▸ mem_wy46

/-- The saved right-conjugation convention is inverse-transposed for columns. -/
theorem rawMatrixX_inverse_transpose :
    (fromRows (![1, 2, 8, 4, 32, 16, 256, 512, 64, 128, 1085, 3023])).transpose * rawMatrixX = 1 ∧
    rawMatrixX * (fromRows (![1, 2, 8, 4, 32, 16, 256, 512, 64, 128, 1085, 3023])).transpose = 1 := by
  constructor <;> decide +kernel

/-- The saved right-conjugation convention is inverse-transposed for columns. -/
theorem rawMatrixY_inverse_transpose :
    (fromRows (![2, 4, 1, 16, 64, 128, 8, 1024, 2048, 2982, 32, 3714])).transpose * rawMatrixY = 1 ∧
    rawMatrixY * (fromRows (![2, 4, 1, 16, 64, 128, 8, 1024, 2048, 2982, 32, 3714])).transpose = 1 := by
  constructor <;> decide +kernel

end Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreComparison.CoordinateGenerators
