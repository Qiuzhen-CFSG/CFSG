module
public import Theory.Representation.Mathieu.M22James.NoFF.Involutions
/-!
# Perfect subgroups fixing the moved Mathieu points

The native involution has a binary four-dimensional moved space. The checked
rank factorization lists its fifteen nonzero vectors. Five pairs of literal
words in the native cover generators fix these points. Their matrices satisfy
X² = Y³ = (XY)⁵ = 1, with X nonidentity; the companion theorem uses these
relations to prove the stabilizers nonsolvable. Each product is certified
separately, so no reduction expands a long matrix word.

Source: the stabilizer consequence of Aschbacher–Smith H.12.1(5),(7),
printed pp.393–394, used in 12.6.26, p.832. This direct computation uses
only the involution moved space; it does not assume an isotropic orbit
classification. Native ATLAS matrices and attribution are retained in the
LinearModel/source directory imported through M22James.Model. Bit zero
is column zero, and all actions are on column vectors.
-/
@[expose] public section
set_option Elab.async false
namespace Sporadic.Mathieu.M22TripleCover.MovedStabilizer
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Matrix Subgroup Representation
open scoped Matrix

def inverseA : Matrix12 := fromRows ![100,32,2,1,7,1705,3524,8,16,561,2074,1024]

theorem coe_inverseA : ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = inverseA := by
  change (↑(coreA⁻¹) : Matrix12) = inverseA
  have h : inverseA * matrixA = 1 := by decide +kernel
  have hh : inverseA * (coreA : Matrix12) = 1 := by rw [coe_coreA]; exact h
  have hx := congrArg (fun M : Matrix12 => M * (↑(coreA⁻¹) : Matrix12)) hh
  simpa only [mul_assoc, Units.val_mul, Units.mul_inv, Units.val_one, mul_one, one_mul] using hx.symm

theorem coe_generatorA : ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = matrixA := coe_coreA
theorem coe_generatorB : ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = matrixB := coe_coreB

def step1 : M22TripleCover := (coreGeneratorA⁻¹) * (coreGeneratorA⁻¹)

def matrix1 : Matrix12 := fromRows ![2927,1705,32,100,70,3311,452,1,7,1275,1062,2074]

theorem coe_step1 : ((step1 : M22TripleCover) : Matrix12ˣ).val = matrix1 := by
  change ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_inverseA, coe_inverseA]
  decide +kernel

def step2 : M22TripleCover := (step1) * (coreGeneratorA⁻¹)

def matrix2 : Matrix12 := fromRows ![3339,3311,1705,2927,3558,1848,3550,100,70,829,3729,1062]

theorem coe_step2 : ((step2 : M22TripleCover) : Matrix12ˣ).val = matrix2 := by
  change ((step1 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step1, coe_inverseA]
  decide +kernel

def step3 : M22TripleCover := (step2) * (coreGeneratorB)

def matrix3 : Matrix12 := fromRows ![1643,1214,1699,2917,3788,3954,3535,2837,2077,806,1504,3916]

theorem coe_step3 : ((step3 : M22TripleCover) : Matrix12ˣ).val = matrix3 := by
  change ((step2 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step2, coe_generatorB]
  decide +kernel

def step4 : M22TripleCover := (step3) * (coreGeneratorA⁻¹)

def matrix4 : Matrix12 := fromRows ![259,3743,3278,3370,996,1393,385,1600,1120,1194,879,1020]

theorem coe_step4 : ((step4 : M22TripleCover) : Matrix12ˣ).val = matrix4 := by
  change ((step3 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step3, coe_inverseA]
  decide +kernel

def step5 : M22TripleCover := (step4) * (coreGeneratorB)

def matrix5 : Matrix12 := fromRows ![2680,1525,1956,1393,2197,3370,2512,3611,1873,3313,2853,2204]

theorem coe_step5 : ((step5 : M22TripleCover) : Matrix12ˣ).val = matrix5 := by
  change ((step4 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step4, coe_generatorB]
  decide +kernel

def step6 : M22TripleCover := (step5) * (coreGeneratorA⁻¹)

def matrix6 : Matrix12 := fromRows ![3418,782,3224,772,1129,2690,2523,3689,1948,1820,238,1036]

theorem coe_step6 : ((step6 : M22TripleCover) : Matrix12ˣ).val = matrix6 := by
  change ((step5 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step5, coe_inverseA]
  decide +kernel

def step7 : M22TripleCover := (step6) * (coreGeneratorB)

def matrix7 : Matrix12 := fromRows ![3706,63,4024,53,1865,2472,411,3401,4045,3175,2229,3148]

theorem coe_step7 : ((step7 : M22TripleCover) : Matrix12ˣ).val = matrix7 := by
  change ((step6 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step6, coe_generatorB]
  decide +kernel

def step8 : M22TripleCover := (step7) * (coreGeneratorA)

def matrix8 : Matrix12 := fromRows ![3863,402,715,278,3578,2241,3147,2932,962,3465,3890,3335]

theorem coe_step8 : ((step8 : M22TripleCover) : Matrix12ˣ).val = matrix8 := by
  change ((step7 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step7, coe_generatorA]
  decide +kernel

def step9 : M22TripleCover := (step8) * (coreGeneratorB)

def matrix9 : Matrix12 := fromRows ![3133,2499,496,2678,3802,3066,1025,2942,2946,1475,3896,1660]

theorem coe_step9 : ((step9 : M22TripleCover) : Matrix12ˣ).val = matrix9 := by
  change ((step8 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step8, coe_generatorB]
  decide +kernel

def step10 : M22TripleCover := (step9) * (coreGeneratorA)

def matrix10 : Matrix12 := fromRows ![3090,2128,3290,1931,1205,2768,2056,364,2893,1492,2411,2699]

theorem coe_step10 : ((step10 : M22TripleCover) : Matrix12ˣ).val = matrix10 := by
  change ((step9 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step9, coe_generatorA]
  decide +kernel

def step11 : M22TripleCover := (step10) * (coreGeneratorB)

def matrix11 : Matrix12 := fromRows ![3096,2113,1978,4033,3317,427,72,375,2157,3461,314,2480]

theorem coe_step11 : ((step11 : M22TripleCover) : Matrix12ˣ).val = matrix11 := by
  change ((step10 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step10, coe_generatorB]
  decide +kernel

def step12 : M22TripleCover := (step11) * (coreGeneratorA)

def matrix12 : Matrix12 := fromRows ![3076,1427,1867,862,1837,3401,159,1898,1293,87,2017,2369]

theorem coe_step12 : ((step12 : M22TripleCover) : Matrix12ˣ).val = matrix12 := by
  change ((step11 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step11, coe_generatorA]
  decide +kernel

def step13 : M22TripleCover := (step12) * (coreGeneratorA)

def matrix13 : Matrix12 := fromRows ![3480,1227,3582,1258,3579,2932,2608,3572,3827,271,1752,1012]

theorem coe_step13 : ((step13 : M22TripleCover) : Matrix12ˣ).val = matrix13 := by
  change ((step12 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step12, coe_generatorA]
  decide +kernel

def step14 : M22TripleCover := (step13) * (coreGeneratorA)

def matrix14 : Matrix12 := fromRows ![451,819,454,825,466,488,1932,322,1087,1783,309,4044]

theorem coe_step14 : ((step14 : M22TripleCover) : Matrix12ˣ).val = matrix14 := by
  change ((step13 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step13, coe_generatorA]
  decide +kernel

def step15 : M22TripleCover := (coreGeneratorA) * (coreGeneratorB)

def matrix15 : Matrix12 := fromRows ![8,31,22,938,2666,2,4,202,3356,32,64,1412]

theorem coe_step15 : ((step15 : M22TripleCover) : Matrix12ˣ).val = matrix15 := by
  change ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_generatorA, coe_generatorB]
  decide +kernel

def step16 : M22TripleCover := (step15) * (coreGeneratorA)

def matrix16 : Matrix12 := fromRows ![128,400,280,3659,1559,4,28,2875,2687,2,31,1499]

theorem coe_step16 : ((step16 : M22TripleCover) : Matrix12ˣ).val = matrix16 := by
  change ((step15 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step15, coe_generatorA]
  decide +kernel

def step17 : M22TripleCover := (step16) * (coreGeneratorA)

def matrix17 : Matrix12 := fromRows ![2976,3271,2023,3613,2586,28,412,359,1795,4,400,1108]

theorem coe_step17 : ((step17 : M22TripleCover) : Matrix12ˣ).val = matrix17 := by
  change ((step16 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step16, coe_generatorA]
  decide +kernel

def step18 : M22TripleCover := (step17) * (coreGeneratorB)

def matrix18 : Matrix12 := fromRows ![202,1980,1244,1629,2571,22,2518,365,3171,31,2497,1093]

theorem coe_step18 : ((step18 : M22TripleCover) : Matrix12ˣ).val = matrix18 := by
  change ((step17 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step17, coe_generatorB]
  decide +kernel

def step19 : M22TripleCover := (step18) * (coreGeneratorA⁻¹)

def matrix19 : Matrix12 := fromRows ![3565,3230,1490,1935,1652,37,2553,2842,1843,64,2488,1464]

theorem coe_step19 : ((step19 : M22TripleCover) : Matrix12ˣ).val = matrix19 := by
  change ((step18 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step18, coe_inverseA]
  decide +kernel

def step20 : M22TripleCover := (step19) * (coreGeneratorB)

def matrix20 : Matrix12 := fromRows ![3798,4005,3480,4062,3343,773,659,97,3944,2048,2691,1688]

theorem coe_step20 : ((step20 : M22TripleCover) : Matrix12ˣ).val = matrix20 := by
  change ((step19 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step19, coe_generatorB]
  decide +kernel

def step21 : M22TripleCover := (step20) * (coreGeneratorA⁻¹)

def matrix21 : Matrix12 := fromRows ![962,2300,3076,979,3149,583,634,2825,1367,1024,1661,2597]

theorem coe_step21 : ((step21 : M22TripleCover) : Matrix12ˣ).val = matrix21 := by
  change ((step20 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step20, coe_inverseA]
  decide +kernel

def step22 : M22TripleCover := (step21) * (coreGeneratorB)

def matrix22 : Matrix12 := fromRows ![2946,2294,3076,2963,1052,589,321,114,3645,3163,3351,2309]

theorem coe_step22 : ((step22 : M22TripleCover) : Matrix12ˣ).val = matrix22 := by
  change ((step21 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step21, coe_generatorB]
  decide +kernel

def step23 : M22TripleCover := (step22) * (coreGeneratorA⁻¹)

def matrix23 : Matrix12 := fromRows ![1545,3904,3096,1642,2078,3986,3504,2890,2274,412,3147,1142]

theorem coe_step23 : ((step23 : M22TripleCover) : Matrix12ˣ).val = matrix23 := by
  change ((step22 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step22, coe_inverseA]
  decide +kernel

def step24 : M22TripleCover := (step23) * (coreGeneratorB)

def matrix24 : Matrix12 := fromRows ![1539,1073,3090,3355,84,3992,1744,2144,2274,2518,1025,1869]

theorem coe_step24 : ((step24 : M22TripleCover) : Matrix12ˣ).val = matrix24 := by
  change ((step23 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step23, coe_generatorB]
  decide +kernel

def step25 : M22TripleCover := (step24) * (coreGeneratorA⁻¹)

def matrix25 : Matrix12 := fromRows ![2671,3792,3133,3144,3521,3637,2016,3949,3909,2553,2174,1944]

theorem coe_step25 : ((step25 : M22TripleCover) : Matrix12ˣ).val = matrix25 := by
  change ((step24 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step24, coe_inverseA]
  decide +kernel

def step26 : M22TripleCover := (step25) * (coreGeneratorB)

def matrix26 : Matrix12 := fromRows ![271,3568,3863,1043,3531,1375,1233,1852,1086,659,2910,4050]

theorem coe_step26 : ((step26 : M22TripleCover) : Matrix12ˣ).val = matrix26 := by
  change ((step25 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step25, coe_generatorB]
  decide +kernel

def step27 : M22TripleCover := (step26) * (coreGeneratorA)

def matrix27 : Matrix12 := fromRows ![1783,350,2553,2316,208,4072,695,3315,2458,2470,366,594]

theorem coe_step27 : ((step27 : M22TripleCover) : Matrix12ˣ).val = matrix27 := by
  change ((step26 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step26, coe_generatorA]
  decide +kernel

def step28 : M22TripleCover := (step27) * (coreGeneratorA)

def matrix28 : Matrix12 := fromRows ![423,2016,2518,895,2751,980,2488,1845,2503,2137,1762,529]

theorem coe_step28 : ((step28 : M22TripleCover) : Matrix12ˣ).val = matrix28 := by
  change ((step27 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step27, coe_generatorA]
  decide +kernel

def step29 : M22TripleCover := (step28) * (coreGeneratorB)

def matrix29 : Matrix12 := fromRows ![2759,1233,412,2852,2724,2974,2691,3957,397,2137,3769,2641]

theorem coe_step29 : ((step29 : M22TripleCover) : Matrix12ˣ).val = matrix29 := by
  change ((step28 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step28, coe_generatorB]
  decide +kernel

def step30 : M22TripleCover := (step29) * (coreGeneratorA)

def matrix30 : Matrix12 := fromRows ![3361,695,3163,247,3376,2769,3362,2528,3411,1043,1188,1945]

theorem coe_step30 : ((step30 : M22TripleCover) : Matrix12ˣ).val = matrix30 := by
  change ((step29 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step29, coe_generatorA]
  decide +kernel

def step31 : M22TripleCover := (coreGeneratorA) * (coreGeneratorA)

def matrix31 : Matrix12 := fromRows ![128,28,412,2976,1639,4,400,2891,2823,1513,1412,1499]

theorem coe_step31 : ((step31 : M22TripleCover) : Matrix12ˣ).val = matrix31 := by
  change ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_generatorA, coe_generatorA]
  decide +kernel

def step32 : M22TripleCover := (step31) * (coreGeneratorA)

def matrix32 : Matrix12 := fromRows ![2976,412,3163,2891,2823,28,3271,122,249,1362,1499,1108]

theorem coe_step32 : ((step32 : M22TripleCover) : Matrix12ˣ).val = matrix32 := by
  change ((step31 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step31, coe_generatorA]
  decide +kernel

def step33 : M22TripleCover := (step32) * (coreGeneratorA)

def matrix33 : Matrix12 := fromRows ![2891,3163,3095,122,249,412,1579,409,2613,3964,1108,2307]

theorem coe_step33 : ((step33 : M22TripleCover) : Matrix12ˣ).val = matrix33 := by
  change ((step32 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step32, coe_generatorA]
  decide +kernel

def step34 : M22TripleCover := (step33) * (coreGeneratorA)

def matrix34 : Matrix12 := fromRows ![122,3095,3220,409,2613,3163,2948,3151,1944,2408,2307,1007]

theorem coe_step34 : ((step34 : M22TripleCover) : Matrix12ˣ).val = matrix34 := by
  change ((step33 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step33, coe_generatorA]
  decide +kernel

def step35 : M22TripleCover := (step34) * (coreGeneratorB)

def matrix35 : Matrix12 := fromRows ![2817,3095,4015,2521,2308,1024,991,1054,4050,296,2616,2191]

theorem coe_step35 : ((step35 : M22TripleCover) : Matrix12ˣ).val = matrix35 := by
  change ((step34 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step34, coe_generatorB]
  decide +kernel

def step36 : M22TripleCover := (step35) * (coreGeneratorA)

def matrix36 : Matrix12 := fromRows ![225,3220,987,2516,1023,2048,3906,2456,594,1765,1804,3764]

theorem coe_step36 : ((step36 : M22TripleCover) : Matrix12ˣ).val = matrix36 := by
  change ((step35 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step35, coe_generatorA]
  decide +kernel

def step37 : M22TripleCover := (step36) * (coreGeneratorA)

def matrix37 : Matrix12 := fromRows ![2997,1848,3934,2368,3904,1412,2290,2499,529,163,3569,1072]

theorem coe_step37 : ((step37 : M22TripleCover) : Matrix12ˣ).val = matrix37 := by
  change ((step36 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step36, coe_generatorA]
  decide +kernel

def step38 : M22TripleCover := (step37) * (coreGeneratorA)

def matrix38 : Matrix12 := fromRows ![2655,3311,2414,1020,2294,1499,3901,2128,514,2990,342,2306]

theorem coe_step38 : ((step38 : M22TripleCover) : Matrix12ˣ).val = matrix38 := by
  change ((step37 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step37, coe_generatorA]
  decide +kernel

def step39 : M22TripleCover := (step38) * (coreGeneratorB)

def matrix39 : Matrix12 := fromRows ![516,1214,309,2204,2300,3456,3901,2113,2626,223,630,2600]

theorem coe_step39 : ((step39 : M22TripleCover) : Matrix12ˣ).val = matrix39 := by
  change ((step38 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step38, coe_generatorB]
  decide +kernel

def step40 : M22TripleCover := (step39) * (coreGeneratorA)

def matrix40 : Matrix12 := fromRows ![790,570,1905,4024,4005,67,2431,1427,1685,2607,527,1548]

theorem coe_step40 : ((step40 : M22TripleCover) : Matrix12ˣ).val = matrix40 := by
  change ((step39 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step39, coe_generatorA]
  decide +kernel

def step41 : M22TripleCover := (step40) * (coreGeneratorA)

def matrix41 : Matrix12 := fromRows ![1141,652,3192,715,863,19,622,1227,446,1564,922,2966]

theorem coe_step41 : ((step41 : M22TripleCover) : Matrix12ˣ).val = matrix41 := by
  change ((step40 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step40, coe_generatorA]
  decide +kernel

def step42 : M22TripleCover := (step41) * (coreGeneratorA)

def matrix42 : Matrix12 := fromRows ![2313,2102,3097,2105,1250,268,911,819,3165,2710,3913,2641]

theorem coe_step42 : ((step42 : M22TripleCover) : Matrix12ˣ).val = matrix42 := by
  change ((step41 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step41, coe_generatorA]
  decide +kernel

def step43 : M22TripleCover := (step42) * (coreGeneratorA)

def matrix43 : Matrix12 := fromRows ![875,1182,3084,1038,953,1787,3677,1123,3087,3126,2174,1945]

theorem coe_step43 : ((step43 : M22TripleCover) : Matrix12ˣ).val = matrix43 := by
  change ((step42 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step42, coe_generatorA]
  decide +kernel

def step44 : M22TripleCover := (step43) * (coreGeneratorA)

def matrix44 : Matrix12 := fromRows ![1532,568,3352,2200,3911,315,3845,2065,3348,3230,1025,1861]

theorem coe_step44 : ((step44 : M22TripleCover) : Matrix12ˣ).val = matrix44 := by
  change ((step43 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step43, coe_generatorA]
  decide +kernel

def step45 : M22TripleCover := (coreGeneratorA⁻¹) * (coreGeneratorB)

def matrix45 : Matrix12 := fromRows ![2837,778,2,16,13,1699,3524,8,1,2395,75,3163]

theorem coe_step45 : ((step45 : M22TripleCover) : Matrix12ˣ).val = matrix45 := by
  change ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_inverseA, coe_generatorB]
  decide +kernel

def step46 : M22TripleCover := (step45) * (coreGeneratorA⁻¹)

def matrix46 : Matrix12 := fromRows ![1600,512,32,7,103,3278,452,1,100,2454,3457,412]

theorem coe_step46 : ((step46 : M22TripleCover) : Matrix12ˣ).val = matrix46 := by
  change ((step45 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step45, coe_inverseA]
  decide +kernel

def step47 : M22TripleCover := (step46) * (coreGeneratorA⁻¹)

def matrix47 : Matrix12 := fromRows ![2031,561,1705,70,2859,501,3550,100,2927,1085,3174,28]

theorem coe_step47 : ((step47 : M22TripleCover) : Matrix12ˣ).val = matrix47 := by
  change ((step46 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step46, coe_inverseA]
  decide +kernel

def step48 : M22TripleCover := (step47) * (coreGeneratorA⁻¹)

def matrix48 : Matrix12 := fromRows ![281,1275,3311,3558,205,2836,482,2927,3339,3795,1877,4]

theorem coe_step48 : ((step48 : M22TripleCover) : Matrix12ˣ).val = matrix48 := by
  change ((step47 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step47, coe_inverseA]
  decide +kernel

def step49 : M22TripleCover := (step48) * (coreGeneratorB)

def matrix49 : Matrix12 := fromRows ![2675,1248,1214,3788,2989,116,712,2917,1643,3554,1151,31]

theorem coe_step49 : ((step49 : M22TripleCover) : Matrix12ˣ).val = matrix49 := by
  change ((step48 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step48, coe_generatorB]
  decide +kernel

def step50 : M22TripleCover := (step49) * (coreGeneratorA)

def matrix50 : Matrix12 := fromRows ![1951,957,570,1453,3039,257,2101,224,2971,90,2445,400]

theorem coe_step50 : ((step50 : M22TripleCover) : Matrix12ˣ).val = matrix50 := by
  change ((step49 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step49, coe_generatorA]
  decide +kernel

def step51 : M22TripleCover := (step50) * (coreGeneratorA)

def matrix51 : Matrix12 := fromRows ![1885,3931,652,1361,2758,1647,1170,3005,2757,411,2263,3271]

theorem coe_step51 : ((step51 : M22TripleCover) : Matrix12ˣ).val = matrix51 := by
  change ((step50 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step50, coe_generatorA]
  decide +kernel

def step52 : M22TripleCover := (step51) * (coreGeneratorA)

def matrix52 : Matrix12 := fromRows ![3302,2426,2102,3952,3369,2951,676,2783,3365,3147,3883,1579]

theorem coe_step52 : ((step52 : M22TripleCover) : Matrix12ˣ).val = matrix52 := by
  change ((step51 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step51, coe_generatorA]
  decide +kernel

def step53 : M22TripleCover := (step52) * (coreGeneratorB)

def matrix53 : Matrix12 := fromRows ![1190,299,854,1850,1379,973,2815,430,1396,1025,3873,1291]

theorem coe_step53 : ((step53 : M22TripleCover) : Matrix12ˣ).val = matrix53 := by
  change ((step52 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step52, coe_generatorB]
  decide +kernel

def step54 : M22TripleCover := (step53) * (coreGeneratorA)

def matrix54 : Matrix12 := fromRows ![954,1769,1130,3307,3702,3654,3235,3421,3942,2056,2275,3819]

theorem coe_step54 : ((step54 : M22TripleCover) : Matrix12ˣ).val = matrix54 := by
  change ((step53 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step53, coe_generatorA]
  decide +kernel

def step55 : M22TripleCover := (step45) * (coreGeneratorA)

def matrix55 : Matrix12 := fromRows ![509,1513,4,256,148,164,64,128,8,624,147,3095]

theorem coe_step55 : ((step55 : M22TripleCover) : Matrix12ˣ).val = matrix55 := by
  change ((step45 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step45, coe_generatorA]
  decide +kernel

def step56 : M22TripleCover := (step55) * (coreGeneratorA)

def matrix56 : Matrix12 := fromRows ![3150,1362,28,1639,2748,3006,31,2976,128,535,2732,3220]

theorem coe_step56 : ((step56 : M22TripleCover) : Matrix12ˣ).val = matrix56 := by
  change ((step55 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step55, coe_generatorA]
  decide +kernel

def step57 : M22TripleCover := (step56) * (coreGeneratorA)

def matrix57 : Matrix12 := fromRows ![3331,3964,412,2823,3248,2771,400,2891,2976,538,3504,1848]

theorem coe_step57 : ((step57 : M22TripleCover) : Matrix12ˣ).val = matrix57 := by
  change ((step56 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step56, coe_generatorA]
  decide +kernel

def step58 : M22TripleCover := (step57) * (coreGeneratorA)

def matrix58 : Matrix12 := fromRows ![3055,2408,3163,249,1830,3133,3271,122,2891,654,321,3311]

theorem coe_step58 : ((step58 : M22TripleCover) : Matrix12ˣ).val = matrix58 := by
  change ((step57 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step57, coe_generatorA]
  decide +kernel

def step59 : M22TripleCover := (step58) * (coreGeneratorB)

def matrix59 : Matrix12 := fromRows ![2255,296,1024,2233,3942,3863,1980,2817,2160,2559,634,1214]

theorem coe_step59 : ((step59 : M22TripleCover) : Matrix12ˣ).val = matrix59 := by
  change ((step58 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step58, coe_generatorB]
  decide +kernel

def step60 : M22TripleCover := (step59) * (coreGeneratorA)

def matrix60 : Matrix12 := fromRows ![3755,1765,2048,4014,2284,2553,1875,225,1177,2510,659,570]

theorem coe_step60 : ((step60 : M22TripleCover) : Matrix12ˣ).val = matrix60 := by
  change ((step59 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step59, coe_generatorA]
  decide +kernel

def step61 : M22TripleCover := (step60) * (coreGeneratorB)

def matrix61 : Matrix12 := fromRows ![1761,3764,64,3204,2295,659,1122,2224,4072,405,2553,2369]

theorem coe_step61 : ((step61 : M22TripleCover) : Matrix12ˣ).val = matrix61 := by
  change ((step60 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step60, coe_generatorB]
  decide +kernel

def step62 : M22TripleCover := (step61) * (coreGeneratorA)

def matrix62 : Matrix12 := fromRows ![191,1072,31,1592,3881,2470,2073,3878,980,3283,2518,1012]

theorem coe_step62 : ((step62 : M22TripleCover) : Matrix12ˣ).val = matrix62 := by
  change ((step61 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step61, coe_generatorA]
  decide +kernel

def step63 : M22TripleCover := (step62) * (coreGeneratorA)

def matrix63 : Matrix12 := fromRows ![2610,2306,400,2696,2147,2137,1036,2291,4046,1847,2372,4044]

theorem coe_step63 : ((step63 : M22TripleCover) : Matrix12ˣ).val = matrix63 := by
  change ((step62 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step62, coe_generatorA]
  decide +kernel

def step64 : M22TripleCover := (step2) * (coreGeneratorA⁻¹)

def matrix64 : Matrix12 := fromRows ![3151,1848,3311,3339,1869,3220,482,2927,3558,1256,3648,3729]

theorem coe_step64 : ((step64 : M22TripleCover) : Matrix12ˣ).val = matrix64 := by
  change ((step2 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step2, coe_inverseA]
  decide +kernel

def step65 : M22TripleCover := (step64) * (coreGeneratorB)

def matrix65 : Matrix12 := fromRows ![1054,3954,1214,1643,1142,4015,712,2917,3788,1267,3675,1504]

theorem coe_step65 : ((step65 : M22TripleCover) : Matrix12ˣ).val = matrix65 := by
  change ((step64 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step64, coe_generatorB]
  decide +kernel

def step66 : M22TripleCover := (step65) * (coreGeneratorA⁻¹)

def matrix66 : Matrix12 := fromRows ![2110,1393,3743,259,850,2269,4092,3370,996,828,941,879]

theorem coe_step66 : ((step66 : M22TripleCover) : Matrix12ˣ).val = matrix66 := by
  change ((step65 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step65, coe_inverseA]
  decide +kernel

def step67 : M22TripleCover := (step66) * (coreGeneratorB)

def matrix67 : Matrix12 := fromRows ![862,3370,1525,2680,2089,3052,1159,1393,2197,822,141,2853]

theorem coe_step67 : ((step67 : M22TripleCover) : Matrix12ˣ).val = matrix67 := by
  change ((step66 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step66, coe_generatorB]
  decide +kernel

def step68 : M22TripleCover := (step67) * (coreGeneratorA⁻¹)

def matrix68 : Matrix12 := fromRows ![4033,2690,782,3418,716,3399,2132,772,1129,1197,111,238]

theorem coe_step68 : ((step68 : M22TripleCover) : Matrix12ˣ).val = matrix68 := by
  change ((step67 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step67, coe_inverseA]
  decide +kernel

def step69 : M22TripleCover := (step68) * (coreGeneratorA⁻¹)

def matrix69 : Matrix12 := fromRows ![915,1561,514,488,4094,392,2497,547,786,3804,2858,2886]

theorem coe_step69 : ((step69 : M22TripleCover) : Matrix12ˣ).val = matrix69 := by
  change ((step68 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step68, coe_inverseA]
  decide +kernel

def step70 : M22TripleCover := (step69) * (coreGeneratorA⁻¹)

def matrix70 : Matrix12 := fromRows ![618,2633,529,2932,1402,25,2488,1244,518,995,169,3015]

theorem coe_step70 : ((step70 : M22TripleCover) : Matrix12ˣ).val = matrix70 := by
  change ((step69 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step69, coe_inverseA]
  decide +kernel

def step71 : M22TripleCover := (step70) * (coreGeneratorB)

def matrix71 : Matrix12 := fromRows ![320,536,2641,2942,3376,25,2691,2023,2653,2200,184,3021]

theorem coe_step71 : ((step71 : M22TripleCover) : Matrix12ˣ).val = matrix71 := by
  change ((step70 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step70, coe_generatorB]
  decide +kernel

def step72 : M22TripleCover := (step71) * (coreGeneratorA⁻¹)

def matrix72 : Matrix12 := fromRows ![3540,567,2966,3432,2724,98,1661,280,2965,1038,1703,2954]

theorem coe_step72 : ((step72 : M22TripleCover) : Matrix12ˣ).val = matrix72 := by
  change ((step71 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step71, coe_inverseA]
  decide +kernel

def step73 : M22TripleCover := (step72) * (coreGeneratorB)

def matrix73 : Matrix12 := fromRows ![3525,2374,988,3443,2751,2824,3351,2659,974,3150,1718,970]

theorem coe_step73 : ((step73 : M22TripleCover) : Matrix12ˣ).val = matrix73 := by
  change ((step72 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step72, coe_generatorB]
  decide +kernel

def step74 : M22TripleCover := (step73) * (coreGeneratorA)

def matrix74 : Matrix12 := fromRows ![72,996,3918,2802,3260,105,2803,1695,3658,3331,432,3670]

theorem coe_step74 : ((step74 : M22TripleCover) : Matrix12ˣ).val = matrix74 := by
  change ((step73 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step73, coe_generatorA]
  decide +kernel

def step75 : M22TripleCover := (step35) * (coreGeneratorA⁻¹)

def matrix75 : Matrix12 := fromRows ![1605,3163,2269,2494,1042,2074,4013,2110,976,1720,158,1103]

theorem coe_step75 : ((step75 : M22TripleCover) : Matrix12ˣ).val = matrix75 := by
  change ((step35 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step35, coe_inverseA]
  decide +kernel

def step76 : M22TripleCover := (step75) * (coreGeneratorA⁻¹)

def matrix76 : Matrix12 := fromRows ![1929,412,2476,661,2109,1062,2301,653,4074,3212,44,1433]

theorem coe_step76 : ((step76 : M22TripleCover) : Matrix12ˣ).val = matrix76 := by
  change ((step75 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step75, coe_inverseA]
  decide +kernel

def step77 : M22TripleCover := (step76) * (coreGeneratorA⁻¹)

def matrix77 : Matrix12 := fromRows ![2646,28,690,600,713,3729,3845,606,1407,3089,1706,2144]

theorem coe_step77 : ((step77 : M22TripleCover) : Matrix12ˣ).val = matrix77 := by
  change ((step76 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step76, coe_inverseA]
  decide +kernel

def step78 : M22TripleCover := (step77) * (coreGeneratorB)

def matrix78 : Matrix12 := fromRows ![540,22,2787,585,498,1504,3134,596,3391,3082,1713,2890]

theorem coe_step78 : ((step78 : M22TripleCover) : Matrix12ˣ).val = matrix78 := by
  change ((step77 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step77, coe_generatorB]
  decide +kernel

def step79 : M22TripleCover := (step78) * (coreGeneratorA⁻¹)

def matrix79 : Matrix12 := fromRows ![565,37,3344,3984,2898,879,2711,4080,2787,3131,3305,3012]

theorem coe_step79 : ((step79 : M22TripleCover) : Matrix12ˣ).val = matrix79 := by
  change ((step78 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step78, coe_inverseA]
  decide +kernel

def step80 : M22TripleCover := (step79) * (coreGeneratorA⁻¹)

def matrix80 : Matrix12 := fromRows ![1273,1743,3085,3636,3010,2315,1656,1369,3344,2801,1818,3055]

theorem coe_step80 : ((step80 : M22TripleCover) : Matrix12ˣ).val = matrix80 := by
  change ((step79 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step79, coe_inverseA]
  decide +kernel

def step81 : M22TripleCover := (step80) * (coreGeneratorA⁻¹)

def matrix81 : Matrix12 := fromRows ![797,1952,3197,2183,3021,1109,320,1452,3085,3383,2589,3331]

theorem coe_step81 : ((step81 : M22TripleCover) : Matrix12ˣ).val = matrix81 := by
  change ((step80 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step80, coe_inverseA]
  decide +kernel

def step82 : M22TripleCover := (step81) * (coreGeneratorA⁻¹)

def matrix82 : Matrix12 := fromRows ![577,3226,1815,1102,2954,1471,3540,3752,3197,2786,1617,3150]

theorem coe_step82 : ((step82 : M22TripleCover) : Matrix12ˣ).val = matrix82 := by
  change ((step81 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step81, coe_inverseA]
  decide +kernel

def step83 : M22TripleCover := (step17) * (coreGeneratorA)

def matrix83 : Matrix12 := fromRows ![2891,1579,1728,3866,1802,412,3163,1642,3425,28,3271,2307]

theorem coe_step83 : ((step83 : M22TripleCover) : Matrix12ˣ).val = matrix83 := by
  change ((step17 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step17, coe_generatorA]
  decide +kernel

def step84 : M22TripleCover := (step83) * (coreGeneratorB)

def matrix84 : Matrix12 := fromRows ![2160,1291,3505,3130,3195,2518,1024,3355,3435,22,1980,2616]

theorem coe_step84 : ((step84 : M22TripleCover) : Matrix12ˣ).val = matrix84 := by
  change ((step83 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step83, coe_generatorB]
  decide +kernel

def step85 : M22TripleCover := (step84) * (coreGeneratorA⁻¹)

def matrix85 : Matrix12 := fromRows ![3946,2127,2760,2709,1845,2553,2074,3144,1826,37,3230,158]

theorem coe_step85 : ((step85 : M22TripleCover) : Matrix12ˣ).val = matrix85 := by
  change ((step84 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step84, coe_inverseA]
  decide +kernel

def step86 : M22TripleCover := (step85) * (coreGeneratorA⁻¹)

def matrix86 : Matrix12 := fromRows ![1399,2435,3068,1624,3315,3863,1062,479,3250,1743,3126,44]

theorem coe_step86 : ((step86 : M22TripleCover) : Matrix12ˣ).val = matrix86 := by
  change ((step85 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step85, coe_inverseA]
  decide +kernel

def step87 : M22TripleCover := (step86) * (coreGeneratorA⁻¹)

def matrix87 : Matrix12 := fromRows ![806,1116,3392,2025,1852,3706,3729,3484,2716,1952,2710,1706]

theorem coe_step87 : ((step87 : M22TripleCover) : Matrix12ˣ).val = matrix87 := by
  change ((step86 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step86, coe_inverseA]
  decide +kernel

def step88 : M22TripleCover := (step87) * (coreGeneratorB)

def matrix88 : Matrix12 := fromRows ![829,1101,3697,1225,3949,3418,1504,1485,2492,3281,2486,1713]

theorem coe_step88 : ((step88 : M22TripleCover) : Matrix12ˣ).val = matrix88 := by
  change ((step87 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step87, coe_generatorB]
  decide +kernel

def step89 : M22TripleCover := (step88) * (coreGeneratorA⁻¹)

def matrix89 : Matrix12 := fromRows ![1256,1465,1317,1459,1329,488,879,1441,693,437,660,3305]

theorem coe_step89 : ((step89 : M22TripleCover) : Matrix12ˣ).val = matrix89 := by
  change ((step88 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step88, coe_inverseA]
  decide +kernel

def step90 : M22TripleCover := (step15) * (coreGeneratorA⁻¹)

def matrix90 : Matrix12 := fromRows ![1,64,37,1185,3453,32,2,3565,3086,1705,3524,2048]

theorem coe_step90 : ((step90 : M22TripleCover) : Matrix12ˣ).val = matrix90 := by
  change ((step15 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step15, coe_inverseA]
  decide +kernel

def step91 : M22TripleCover := (step90) * (coreGeneratorA⁻¹)

def matrix91 : Matrix12 := fromRows ![100,3524,1743,3807,1799,1705,32,1800,3129,3311,452,1024]

theorem coe_step91 : ((step91 : M22TripleCover) : Matrix12ˣ).val = matrix91 := by
  change ((step90 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step90, coe_inverseA]
  decide +kernel

def step92 : M22TripleCover := (step91) * (coreGeneratorA⁻¹)

def matrix92 : Matrix12 := fromRows ![2927,452,1952,935,2685,3311,1705,2618,2769,1848,3550,2074]

theorem coe_step92 : ((step92 : M22TripleCover) : Matrix12ˣ).val = matrix92 := by
  change ((step91 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step91, coe_inverseA]
  decide +kernel

def step93 : M22TripleCover := (step92) * (coreGeneratorA⁻¹)

def matrix93 : Matrix12 := fromRows ![3339,3550,3226,1222,3388,1848,3311,190,2974,3220,482,1062]

theorem coe_step93 : ((step93 : M22TripleCover) : Matrix12ˣ).val = matrix93 := by
  change ((step92 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step92, coe_inverseA]
  decide +kernel

def step94 : M22TripleCover := (step93) * (coreGeneratorB)

def matrix94 : Matrix12 := fromRows ![1643,3535,4026,2028,1389,3954,1214,180,980,4015,712,3916]

theorem coe_step94 : ((step94 : M22TripleCover) : Matrix12ˣ).val = matrix94 := by
  change ((step93 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step93, coe_generatorB]
  decide +kernel

def step95 : M22TripleCover := (step94) * (coreGeneratorA⁻¹)

def matrix95 : Matrix12 := fromRows ![259,385,2236,349,768,1393,3743,1700,4072,2269,4092,1020]

theorem coe_step95 : ((step95 : M22TripleCover) : Matrix12ˣ).val = matrix95 := by
  change ((step94 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step94, coe_inverseA]
  decide +kernel

def step96 : M22TripleCover := (step95) * (coreGeneratorB)

def matrix96 : Matrix12 := fromRows ![2680,2512,246,620,42,3370,1525,1700,1177,3052,1159,2204]

theorem coe_step96 : ((step96 : M22TripleCover) : Matrix12ˣ).val = matrix96 := by
  change ((step95 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorB : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step95, coe_generatorB]
  decide +kernel

def step97 : M22TripleCover := (step96) * (coreGeneratorA⁻¹)

def matrix97 : Matrix12 := fromRows ![3418,2523,2880,2399,1672,2690,782,3208,2160,3399,2132,1036]

theorem coe_step97 : ((step97 : M22TripleCover) : Matrix12ˣ).val = matrix97 := by
  change ((step96 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step96, coe_inverseA]
  decide +kernel

def step98 : M22TripleCover := (step97) * (coreGeneratorA⁻¹)

def matrix98 : Matrix12 := fromRows ![488,2462,3045,2452,2594,1561,514,3091,3946,392,2497,2073]

theorem coe_step98 : ((step98 : M22TripleCover) : Matrix12ˣ).val = matrix98 := by
  change ((step97 : M22TripleCover) : Matrix12ˣ).val * ((coreGeneratorA⁻¹ : M22TripleCover) : Matrix12ˣ).val = _
  simp only [coe_step97, coe_inverseA]
  decide +kernel

def actorX : Fin 5 → M22TripleCover := ![step14,step14,step54,step74,step89]

def actorY : Fin 5 → M22TripleCover := ![step30,step44,step63,step82,step98]

def matrixX : Fin 5 → Matrix12 := ![matrix14,matrix14,matrix54,matrix74,matrix89]

def matrixY : Fin 5 → Matrix12 := ![matrix30,matrix44,matrix63,matrix82,matrix98]

theorem coe_actorX (i : Fin 5) : ((actorX i : M22TripleCover) : Matrix12ˣ).val = matrixX i := by
  fin_cases i

  · exact coe_step14

  · exact coe_step14

  · exact coe_step54

  · exact coe_step74

  · exact coe_step89

theorem coe_actorY (i : Fin 5) : ((actorY i : M22TripleCover) : Matrix12ˣ).val = matrixY i := by
  fin_cases i

  · exact coe_step30

  · exact coe_step44

  · exact coe_step63

  · exact coe_step82

  · exact coe_step98

def matrixXY : Fin 5 → Matrix12 := ![fromRows ![1543,311,1917,887,1558,951,2216,710,127,89,3016,531],fromRows ![3524,2098,1312,658,1919,931,2074,41,2105,2859,2956,90],fromRows ![954,2671,1691,2966,3355,3361,1298,1027,2742,1348,2138,3233],fromRows ![2458,1867,3735,1919,2523,3684,1342,1043,1533,2233,3296,3374],fromRows ![2141,3839,2751,3829,2936,3830,254,3401,2989,1359,3164,428]]

def matrixXY2 : Fin 5 → Matrix12 := ![fromRows ![3036,1427,1258,3426,3021,1804,21,3197,3635,3022,2860,383],fromRows ![3836,3252,22,1103,1564,1390,3461,3317,3024,1935,1235,1477],fromRows ![2610,1294,1605,1727,277,214,1432,399,296,357,1361,3683],fromRows ![1327,3380,1273,1052,2443,3258,1,3050,4093,103,3719,1268],fromRows ![1597,622,3788,612,1227,1222,652,11,230,1511,572,3160]]

def matrixXY4 : Fin 5 → Matrix12 := ![fromRows ![2735,3296,2233,1770,2750,1881,1275,1235,787,1265,2566,1312],fromRows ![194,3719,2750,3911,281,3845,2265,3582,3830,616,503,153],fromRows ![3019,397,3547,3006,3146,1609,604,3937,1857,2065,2758,37],fromRows ![1342,1094,366,2025,3300,3456,1327,1303,3833,89,3356,1188],fromRows ![3395,3435,1452,3425,1676,3097,2372,1591,2787,3588,2370,2631]]

def matrixY2 : Fin 5 → Matrix12 := ![fromRows ![2462,2527,3150,238,2447,1881,1544,1241,490,1538,3022,1250],fromRows ![1533,2682,2447,2187,1815,3124,2602,3582,3087,938,509,618],fromRows ![451,2304,3934,2688,169,793,604,57,148,807,1438,2454],fromRows ![1399,2025,648,1094,3245,1843,2435,4004,2278,3317,2220,2056],fromRows ![3830,2733,1278,2727,1558,2583,2070,908,2859,2797,2186,2631]]

theorem x_square (i : Fin 5) : matrixX i * matrixX i = 1 := by
  revert i
  decide +kernel

theorem y_square (i : Fin 5) : matrixY i * matrixY i = matrixY2 i := by
  revert i
  decide +kernel

theorem y_cube (i : Fin 5) : matrixY2 i * matrixY i = 1 := by
  revert i
  decide +kernel

theorem xy_mul (i : Fin 5) : matrixX i * matrixY i = matrixXY i := by
  revert i
  decide +kernel

theorem xy_square (i : Fin 5) : matrixXY i * matrixXY i = matrixXY2 i := by
  revert i
  decide +kernel

theorem xy_four (i : Fin 5) : matrixXY2 i * matrixXY2 i = matrixXY4 i := by
  revert i
  decide +kernel

theorem xy_five (i : Fin 5) : matrixXY4 i * matrixXY i = 1 := by
  revert i
  decide +kernel

def point (i : Fin 15) : BinarySpace := fun j =>
  if (![17,416,433,1028,1045,1444,1461,2788,2805,2884,2901,3808,3825,3904,3921] i).testBit j.val then 1 else 0

def pairIndex : Fin 15 → Fin 5 := ![0,0,0,1,2,3,4,1,4,2,3,1,3,4,2]

theorem x_fixes (i : Fin 15) : matrixX (pairIndex i) *ᵥ point i = point i := by
  revert i
  decide +kernel
theorem y_fixes (i : Fin 15) : matrixY (pairIndex i) *ᵥ point i = point i := by
  revert i
  decide +kernel
theorem x_nonidentity (i : Fin 5) : matrixX i ≠ 1 := by
  revert i
  decide +kernel

def imageMatrix : Matrix (Fin 12) (Fin 4) (ZMod 2) := fun i j => if (![1,0,3,0,1,6,8,6,14,8,11,8] i).testBit j.val then 1 else 0

def factorMatrix : Matrix (Fin 4) (Fin 12) (ZMod 2) := fun i j => if (![17,10,800,2112] i).testBit j.val then 1 else 0

theorem displacement_factor : matrixB - 1 = imageMatrix * factorMatrix := by decide +kernel

theorem image_cases (v : Fin 4 → ZMod 2) :
    imageMatrix *ᵥ v = 0 ∨ ∃ i : Fin 15, imageMatrix *ᵥ v = point i := by
  revert v
  decide +kernel
end Sporadic.Mathieu.M22TripleCover.MovedStabilizer
