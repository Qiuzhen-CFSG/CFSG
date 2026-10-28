module
public import Theory.Representation.Mathieu.M22James.Unitary
public import Theory.Representation.Mathieu.M22James.Ambient
public import Theory.Mathieu.M22.Properties.FixedHexadLocal.KernelGeometry
public import Theory.ElementaryAbelian.AbelianNormalClosure
public import Theory.GroupTheory.CentralCoprimeCardLift

/-!
Native hexad translations in the genuine binary triple-cover module.
The three initial word certificates are reused from SourceComparison.HexadCommutant;
new short products generate the sixteen pointwise hexad translations. Small matrix
identities give six coordinates for their common fixed space and check singularity.
Source: Aschbacher--Segev (4.6), printed p.598. Existing native ATLAS matrix
attribution and licensing are inherited from the imported M22James model.
-/
public noncomputable section
namespace Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeHexadCoordinates
open Subgroup Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open scoped Matrix IsMulCommutative Pointwise
private def u0 : Matrix12 := fromRows ![3005,3006,1362,3150,2304,652,3355,1639,2748,3931,1309,2732]
private def u1 : Matrix12 := fromRows ![13,2372,3819,1177,2875,3579,2059,3074,3093,208,2544,1875]
private def u2 : Matrix12 := fromRows ![2602,222,4,1038,204,2636,2743,3757,1498,2295,1244,1642]
private def gen : Fin 3 → Matrix12 := ![u0,u1,u2]
private theorem coe_inv_of_mul (u : Matrix12ˣ) (m : Matrix12) (hm : (u : Matrix12)*m=1) :
    (↑u⁻¹ : Matrix12)=m := by
  calc
    (↑u⁻¹ : Matrix12) = (↑u⁻¹ : Matrix12)*((u : Matrix12)*m) := by rw [hm,mul_one]
    _ = m := by rw [←mul_assoc,←Units.val_mul,inv_mul_cancel,Units.val_one,one_mul]
private def invA : Matrix12 := fromRows ![100,32,2,1,7,1705,3524,8,16,561,2074,1024]
private theorem coe_invA : (↑coreA⁻¹ : Matrix12)=invA := by
  apply coe_inv_of_mul
  rw [coe_coreA]
  decide +kernel
private def invB : Matrix12 := fromRows ![16,2,31,8,1,778,2048,938,2666,2624,3163,64]
private theorem coe_invB : (↑coreB⁻¹ : Matrix12)=invB := by
  apply coe_inv_of_mul
  rw [coe_coreB]
  decide +kernel
private def prefix0_1 : Matrix12 := fromRows ![2927,1705,32,100,70,3311,452,1,7,1275,1062,2074]
private theorem step0_1 : invA * invA = prefix0_1 := by decide +kernel
private def prefix0_2 : Matrix12 := fromRows ![2917,1699,778,2837,2077,1214,479,16,13,1248,3916,75]
private theorem step0_2 : prefix0_1 * matrixB = prefix0_2 := by decide +kernel
private def prefix0_3 : Matrix12 := fromRows ![224,164,1513,509,1040,570,3144,256,148,957,2154,147]
private theorem step0_3 : prefix0_2 * matrixA = prefix0_3 := by decide +kernel
private def prefix0_4 : Matrix12 := fromRows ![3005,3006,1362,3150,2304,652,3355,1639,2748,3931,1309,2732]
private theorem step0_4 : prefix0_3 * matrixA = prefix0_4 := by decide +kernel
private def lift0 : derivedGroup := coreGeneratorA⁻¹*coreGeneratorA⁻¹*coreGeneratorB*coreGeneratorA*coreGeneratorA
private theorem lift0_matrix : ((lift0 : Matrix12ˣ) : Matrix12)=u0 := by
  change (((coreA⁻¹*coreA⁻¹*coreB*coreA*coreA : Matrix12ˣ)) : Matrix12)=u0
  simp only [Units.val_mul,coe_coreA,coe_coreB,coe_invA,step0_1,step0_2,step0_3,step0_4]
  rfl
private theorem lift0_hexad : m22Hexad123.image (corePermutationAction lift0)=m22Hexad123 := by
  simp only [lift0,map_mul,map_inv,corePermutationAction_coreGeneratorA,corePermutationAction_coreGeneratorB]
  decide +kernel
private def prefix1_1 : Matrix12 := fromRows ![256,4,400,128,8,1513,1412,3659,1559,1681,3095,31]
private theorem step1_1 : invB * matrixA = prefix1_1 := by decide +kernel
private def prefix1_2 : Matrix12 := fromRows ![1639,28,3271,2976,128,1362,1499,3613,2586,418,3220,400]
private theorem step1_2 : prefix1_1 * matrixA = prefix1_2 := by decide +kernel
private def prefix1_3 : Matrix12 := fromRows ![2823,412,1579,2891,2976,3964,1108,3866,1802,3521,1848,3271]
private theorem step1_3 : prefix1_2 * matrixA = prefix1_3 := by decide +kernel
private def prefix1_4 : Matrix12 := fromRows ![103,2518,1291,2160,202,1837,1093,3130,3195,3531,3954,1980]
private theorem step1_4 : prefix1_3 * matrixB = prefix1_4 := by decide +kernel
private def prefix1_5 : Matrix12 := fromRows ![13,2372,3819,1177,2875,3579,2059,3074,3093,208,2544,1875]
private theorem step1_5 : prefix1_4 * matrixA = prefix1_5 := by decide +kernel
private def lift1 : derivedGroup := coreGeneratorB⁻¹*coreGeneratorA*coreGeneratorA*coreGeneratorA*coreGeneratorB*coreGeneratorA
private theorem lift1_matrix : ((lift1 : Matrix12ˣ) : Matrix12)=u1 := by
  change (((coreB⁻¹*coreA*coreA*coreA*coreB*coreA : Matrix12ˣ)) : Matrix12)=u1
  simp only [Units.val_mul,coe_coreA,coe_coreB,coe_invB,step1_1,step1_2,step1_3,step1_4,step1_5]
  rfl
private theorem lift1_hexad : m22Hexad123.image (corePermutationAction lift1)=m22Hexad123 := by
  simp only [lift1,map_mul,map_inv,corePermutationAction_coreGeneratorA,corePermutationAction_coreGeneratorB]
  decide +kernel
private def prefix2_1 : Matrix12 := fromRows ![7,32,64,1,100,512,1024,1185,3453,3061,412,3524]
private theorem step2_1 : invB * invA = prefix2_1 := by decide +kernel
private def prefix2_2 : Matrix12 := fromRows ![70,1705,3524,100,2927,561,2074,3807,1799,3365,28,452]
private theorem step2_2 : prefix2_1 * invA = prefix2_2 := by decide +kernel
private def prefix2_3 : Matrix12 := fromRows ![2077,1699,3524,2837,2917,2395,75,3573,3196,1396,22,479]
private theorem step2_3 : prefix2_2 * matrixB = prefix2_3 := by decide +kernel
private def prefix2_4 : Matrix12 := fromRows ![1040,164,64,509,224,624,147,330,3077,3942,280,3144]
private theorem step2_4 : prefix2_3 * matrixA = prefix2_4 := by decide +kernel
private def prefix2_5 : Matrix12 := fromRows ![2304,3006,31,3150,3005,535,2732,1788,3472,2284,2023,3355]
private theorem step2_5 : prefix2_4 * matrixA = prefix2_5 := by decide +kernel
private def prefix2_6 : Matrix12 := fromRows ![2602,222,4,1038,204,2636,2743,3757,1498,2295,1244,1642]
private theorem step2_6 : prefix2_5 * matrixB = prefix2_6 := by decide +kernel
private def lift2 : derivedGroup := coreGeneratorB⁻¹*coreGeneratorA⁻¹*coreGeneratorA⁻¹*coreGeneratorB*coreGeneratorA*coreGeneratorA*coreGeneratorB
private theorem lift2_matrix : ((lift2 : Matrix12ˣ) : Matrix12)=u2 := by
  change (((coreB⁻¹*coreA⁻¹*coreA⁻¹*coreB*coreA*coreA*coreB : Matrix12ˣ)) : Matrix12)=u2
  simp only [Units.val_mul,coe_coreA,coe_coreB,coe_invA,coe_invB,step2_1,step2_2,step2_3,step2_4,step2_5,step2_6]
  rfl
private theorem lift2_hexad : m22Hexad123.image (corePermutationAction lift2)=m22Hexad123 := by
  simp only [lift2,map_mul,map_inv,corePermutationAction_coreGeneratorA,corePermutationAction_coreGeneratorB]
  decide +kernel
private def liftGen : Fin 3 → derivedGroup := ![lift0,lift1,lift2]
private theorem liftGen_matrix (k : Fin 3) : ((liftGen k : Matrix12ˣ) : Matrix12)=gen k := by
  fin_cases k
  · exact lift0_matrix
  · exact lift1_matrix
  · exact lift2_matrix
private theorem liftGen_hexad (k : Fin 3) : m22Hexad123.image (corePermutationAction (liftGen k))=m22Hexad123 := by
  fin_cases k
  · exact lift0_hexad
  · exact lift1_hexad
  · exact lift2_hexad

private def translation0_0 : Matrix12 := fromRows ![13,2372,3819,1177,2875,3579,2059,3074,3093,208,2544,1875]
private theorem translation0_0_step : 1 * u1 = translation0_0 := by decide +kernel
private def translation0_1 : Matrix12 := fromRows ![3616,2307,2797,1177,3901,1804,2192,616,2132,1238,3370,2430]
private theorem translation0_1_step : translation0_0 * u2 = translation0_1 := by decide +kernel
private def translation0_2 : Matrix12 := fromRows ![904,527,1038,2653,3801,3911,106,441,2696,365,656,1723]
private theorem translation0_2_step : translation0_1 * u1 = translation0_2 := by decide +kernel
private def translation0_3 : Matrix12 := fromRows ![1934,1545,8,2758,179,4060,1067,4051,1086,2817,1686,1788]
private theorem translation0_3_step : translation0_2 * u2 = translation0_3 := by decide +kernel
private def translation0_4 : Matrix12 := fromRows ![2561,3508,1177,1061,907,1830,2523,1053,3078,2971,2486,411]
private theorem translation0_4_step : translation0_3 * u1 = translation0_4 := by decide +kernel
private def translation0_5 : Matrix12 := fromRows ![1207,837,1177,1214,3450,871,2460,2608,620,3036,1863,1345]
private theorem translation0_5_step : translation0_4 * u2 = translation0_5 := by decide +kernel
def translation0 : M22TripleCover := lift1*lift2*lift1*lift2*lift1*lift2
private theorem translation0_matrix : ((translation0 : Matrix12ˣ) : Matrix12) = translation0_5 := by
  change ((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12)*((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12)*((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12) = _
  rw [lift1_matrix,lift2_matrix]
  have h0 : u1 = translation0_0 := by simpa using translation0_0_step
  nth_rw 1 [h0]
  rw [translation0_1_step,translation0_2_step,translation0_3_step,translation0_4_step,translation0_5_step]
def permutation0 : Equiv.Perm (Fin 22) where
  toFun := ![4,1,2,3,0,13,11,17,21,15,10,6,14,5,12,9,19,7,18,16,20,8]
  invFun := ![4,1,2,3,0,13,11,17,21,15,10,6,14,5,12,9,19,7,18,16,20,8]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem translation0_permutation : corePermutationAction translation0 = permutation0 := by
  simp only [translation0,lift1,lift2,map_mul,map_inv,corePermutationAction_coreGeneratorA,corePermutationAction_coreGeneratorB]
  decide +kernel
private def translation1_0 : Matrix12 := fromRows ![3005,3006,1362,3150,2304,652,3355,1639,2748,3931,1309,2732]
private theorem translation1_0_step : 1 * u0 = translation1_0 := by decide +kernel
private def translation1_1 : Matrix12 := fromRows ![2859,610,3985,1438,2886,1696,1117,2930,1843,3206,1185,3080]
private theorem translation1_1_step : translation1_0 * u1 = translation1_1 := by decide +kernel
private def translation1_2 : Matrix12 := fromRows ![4081,2258,3024,2995,298,2250,135,2990,2437,3265,2583,1720]
private theorem translation1_2_step : translation1_1 * u2 = translation1_2 := by decide +kernel
private def translation1_3 : Matrix12 := fromRows ![162,293,1188,2077,3123,3719,2976,2393,2466,2727,2842,1915]
private theorem translation1_3_step : translation1_2 * u1 = translation1_3 := by decide +kernel
private def translation1_4 : Matrix12 := fromRows ![1087,1464,57,2182,706,3612,4006,2031,1935,140,3931,1852]
private theorem translation1_4_step : translation1_3 * u2 = translation1_4 := by decide +kernel
private def translation1_5 : Matrix12 := fromRows ![3083,3006,596,3326,3485,3898,1072,4092,2572,1648,3206,2439]
private theorem translation1_5_step : translation1_4 * u1 = translation1_5 := by decide +kernel
private def translation1_6 : Matrix12 := fromRows ![3148,3006,648,2296,1837,459,3676,1291,2711,3100,3265,2029]
private theorem translation1_6_step : translation1_5 * u2 = translation1_6 := by decide +kernel
private def translation1_7 : Matrix12 := fromRows ![2998,2,1394,1554,215,3469,3565,1004,4033,4013,3952,2987]
private theorem translation1_7_step : translation1_6 * u0 = translation1_7 := by decide +kernel
def translation1 : M22TripleCover := lift0*lift1*lift2*lift1*lift2*lift1*lift2*lift0
private theorem translation1_matrix : ((translation1 : Matrix12ˣ) : Matrix12) = translation1_7 := by
  change ((lift0 : Matrix12ˣ) : Matrix12)*((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12)*((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12)*((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12)*((lift0 : Matrix12ˣ) : Matrix12) = _
  rw [lift0_matrix,lift1_matrix,lift2_matrix]
  have h0 : u0 = translation1_0 := by simpa using translation1_0_step
  nth_rw 1 [h0]
  rw [translation1_1_step,translation1_2_step,translation1_3_step,translation1_4_step,translation1_5_step,translation1_6_step,translation1_7_step]
def permutation1 : Equiv.Perm (Fin 22) where
  toFun := ![15,1,2,3,9,11,13,8,7,4,10,5,19,6,16,0,14,21,18,12,20,17]
  invFun := ![15,1,2,3,9,11,13,8,7,4,10,5,19,6,16,0,14,21,18,12,20,17]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem translation1_permutation : corePermutationAction translation1 = permutation1 := by
  simp only [translation1,lift0,lift1,lift2,map_mul,map_inv,corePermutationAction_coreGeneratorA,corePermutationAction_coreGeneratorB]
  decide +kernel
private def translation2_0 : Matrix12 := fromRows ![3005,3006,1362,3150,2304,652,3355,1639,2748,3931,1309,2732]
private theorem translation2_0_step : 1 * u0 = translation2_0 := by decide +kernel
private def translation2_1 : Matrix12 := fromRows ![2859,610,3985,1438,2886,1696,1117,2930,1843,3206,1185,3080]
private theorem translation2_1_step : translation2_0 * u1 = translation2_1 := by decide +kernel
private def translation2_2 : Matrix12 := fromRows ![4081,2258,3024,2995,298,2250,135,2990,2437,3265,2583,1720]
private theorem translation2_2_step : translation2_1 * u2 = translation2_2 := by decide +kernel
private def translation2_3 : Matrix12 := fromRows ![283,878,3383,675,4032,1568,822,2306,2200,3952,2470,3043]
private theorem translation2_3_step : translation2_2 * u0 = translation2_3 := by decide +kernel
private def translation2_4 : Matrix12 := fromRows ![2814,2563,980,2144,1647,1243,3498,514,1267,3245,3344,2861]
private theorem translation2_4_step : translation2_3 * u1 = translation2_4 := by decide +kernel
private def translation2_5 : Matrix12 := fromRows ![1235,1129,2559,1681,558,3824,1885,2089,178,2167,1952,3883]
private theorem translation2_5_step : translation2_4 * u2 = translation2_5 := by decide +kernel
private def translation2_6 : Matrix12 := fromRows ![1890,3449,2559,3740,3957,26,1600,4051,1621,2410,1041,1175]
private theorem translation2_6_step : translation2_5 * u0 = translation2_6 := by decide +kernel
private def translation2_7 : Matrix12 := fromRows ![2433,2281,2740,824,587,1766,299,1053,1270,875,710,2411]
private theorem translation2_7_step : translation2_6 * u1 = translation2_7 := by decide +kernel
private def translation2_8 : Matrix12 := fromRows ![1847,1560,2740,931,3258,679,364,2608,2716,812,3127,3505]
private theorem translation2_8_step : translation2_7 * u2 = translation2_8 := by decide +kernel
def translation2 : M22TripleCover := lift0*lift1*lift2*lift0*lift1*lift2*lift0*lift1*lift2
private theorem translation2_matrix : ((translation2 : Matrix12ˣ) : Matrix12) = translation2_8 := by
  change ((lift0 : Matrix12ˣ) : Matrix12)*((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12)*((lift0 : Matrix12ˣ) : Matrix12)*((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12)*((lift0 : Matrix12ˣ) : Matrix12)*((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12) = _
  rw [lift0_matrix,lift1_matrix,lift2_matrix]
  have h0 : u0 = translation2_0 := by simpa using translation2_0_step
  nth_rw 1 [h0]
  rw [translation2_1_step,translation2_2_step,translation2_3_step,translation2_4_step,translation2_5_step,translation2_6_step,translation2_7_step,translation2_8_step]
def permutation2 : Equiv.Perm (Fin 22) where
  toFun := ![6,1,2,3,11,9,0,12,19,5,10,4,7,15,17,13,21,14,18,8,20,16]
  invFun := ![6,1,2,3,11,9,0,12,19,5,10,4,7,15,17,13,21,14,18,8,20,16]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem translation2_permutation : corePermutationAction translation2 = permutation2 := by
  simp only [translation2,lift0,lift1,lift2,map_mul,map_inv,corePermutationAction_coreGeneratorA,corePermutationAction_coreGeneratorB]
  decide +kernel
private def translation3_0 : Matrix12 := fromRows ![13,2372,3819,1177,2875,3579,2059,3074,3093,208,2544,1875]
private theorem translation3_0_step : 1 * u1 = translation3_0 := by decide +kernel
private def translation3_1 : Matrix12 := fromRows ![3616,2307,2797,1177,3901,1804,2192,616,2132,1238,3370,2430]
private theorem translation3_1_step : translation3_0 * u2 = translation3_1 := by decide +kernel
private def translation3_2 : Matrix12 := fromRows ![614,19,3750,3465,891,2534,1483,3202,3045,2445,113,1061]
private theorem translation3_2_step : translation3_1 * u0 = translation3_2 := by decide +kernel
private def translation3_3 : Matrix12 := fromRows ![655,626,2085,2592,4062,1307,3132,3045,3202,3387,3782,2797]
private theorem translation3_3_step : translation3_2 * u1 = translation3_3 := by decide +kernel
private def translation3_4 : Matrix12 := fromRows ![2212,2078,1544,1233,3993,3888,3132,3903,3269,790,3713,3819]
private theorem translation3_4_step : translation3_3 * u2 = translation3_4 := by decide +kernel
private def translation3_5 : Matrix12 := fromRows ![2837,270,1544,3292,706,474,3361,2245,2594,523,3376,1367]
private theorem translation3_5_step : translation3_4 * u0 = translation3_5 := by decide +kernel
private def translation3_6 : Matrix12 := fromRows ![3659,3875,3513,3043,3485,3834,3904,3516,828,3328,1142,375]
private theorem translation3_6_step : translation3_5 * u1 = translation3_6 := by decide +kernel
private def translation3_7 : Matrix12 := fromRows ![3596,3875,3429,4069,1837,11,1324,1867,935,1900,1073,3869]
private theorem translation3_7_step : translation3_6 * u2 = translation3_7 := by decide +kernel
private def translation3_8 : Matrix12 := fromRows ![2550,2265,1141,3401,215,3149,1073,428,1117,1649,1324,503]
private theorem translation3_8_step : translation3_7 * u0 = translation3_8 := by decide +kernel
def translation3 : M22TripleCover := lift1*lift2*lift0*lift1*lift2*lift0*lift1*lift2*lift0
private theorem translation3_matrix : ((translation3 : Matrix12ˣ) : Matrix12) = translation3_8 := by
  change ((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12)*((lift0 : Matrix12ˣ) : Matrix12)*((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12)*((lift0 : Matrix12ˣ) : Matrix12)*((lift1 : Matrix12ˣ) : Matrix12)*((lift2 : Matrix12ˣ) : Matrix12)*((lift0 : Matrix12ˣ) : Matrix12) = _
  rw [lift0_matrix,lift1_matrix,lift2_matrix]
  have h0 : u1 = translation3_0 := by simpa using translation3_0_step
  nth_rw 1 [h0]
  rw [translation3_1_step,translation3_2_step,translation3_3_step,translation3_4_step,translation3_5_step,translation3_6_step,translation3_7_step,translation3_8_step]
def permutation3 : Equiv.Perm (Fin 22) where
  toFun := ![19,1,2,3,16,17,8,13,6,14,10,21,15,7,9,12,4,5,18,0,20,11]
  invFun := ![19,1,2,3,16,17,8,13,6,14,10,21,15,7,9,12,4,5,18,0,20,11]
  left_inv := by decide +kernel
  right_inv := by decide +kernel
theorem translation3_permutation : corePermutationAction translation3 = permutation3 := by
  simp only [translation3,lift0,lift1,lift2,map_mul,map_inv,corePermutationAction_coreGeneratorA,corePermutationAction_coreGeneratorB]
  decide +kernel
def generator : Fin 4 → M22TripleCover := ![translation0,translation1,translation2,translation3]
def generatorMatrix : Fin 4 → Matrix12 := ![fromRows ![1207,837,1177,1214,3450,871,2460,2608,620,3036,1863,1345],fromRows ![2998,2,1394,1554,215,3469,3565,1004,4033,4013,3952,2987],fromRows ![1847,1560,2740,931,3258,679,364,2608,2716,812,3127,3505],fromRows ![2550,2265,1141,3401,215,3149,1073,428,1117,1649,1324,503]]
def generatorPerm : Fin 4 → Equiv.Perm (Fin 22) := ![permutation0,permutation1,permutation2,permutation3]
theorem generator_matrix (k : Fin 4) : ((generator k : Matrix12ˣ) : Matrix12) = generatorMatrix k := by
  fin_cases k
  · exact translation0_matrix
  · exact translation1_matrix
  · exact translation2_matrix
  · exact translation3_matrix

theorem generator_permutation (k : Fin 4) : corePermutationAction (generator k) = generatorPerm k := by
  fin_cases k
  · exact translation0_permutation
  · exact translation1_permutation
  · exact translation2_permutation
  · exact translation3_permutation

private theorem generatorMatrix_square (k : Fin 4) : generatorMatrix k * generatorMatrix k = 1 := by
  fin_cases k <;> decide +kernel
private theorem generatorMatrix_commute (i j : Fin 4) :
    generatorMatrix i * generatorMatrix j = generatorMatrix j * generatorMatrix i := by
  revert i j
  decide +kernel

theorem generator_square (k : Fin 4) : generator k ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  simp only [pow_two, Subgroup.coe_mul, Units.val_mul, Subgroup.coe_one, Units.val_one, generator_matrix, generatorMatrix_square]

theorem generator_commute (i j : Fin 4) : generator i * generator j = generator j * generator i := by
  apply Subtype.ext
  apply Units.ext
  change ((generator i : Matrix12ˣ) : Matrix12) * ((generator j : Matrix12ˣ) : Matrix12) =
    ((generator j : Matrix12ˣ) : Matrix12) * ((generator i : Matrix12ˣ) : Matrix12)
  rw [generator_matrix,generator_matrix,generatorMatrix_commute]

def translations : Subgroup M22TripleCover := closure (Set.range generator)

theorem translations_elementary : IsElementaryAbelian 2 translations := by
  let : IsMulCommutative (closure (Set.range generator)) := isMulCommutative_closure (by
    rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩
    exact generator_commute i j)
  apply IsElementaryAbelian.closure_of_isMulCommutative
  rintro x ⟨i,rfl⟩
  exact generator_square i

private def rect {m n : ℕ} (rows : Fin m → ℕ) : Matrix (Fin m) (Fin n) (ZMod 2) :=
  fun i j => if (rows i).testBit j.val then 1 else 0
def inclusion : Matrix (Fin 12) (Fin 6) (ZMod 2) := rect ![1,2,4,8,16,11,32,39,7,32,58,28]
private def equations : Matrix (Fin 6) (Fin 12) (ZMod 2) := rect ![1206,839,1181,3434,2999,1398]
private def selector : Matrix (Fin 6) (Fin 12) (ZMod 2) := rect ![1,2,4,8,16,64]
private def equationSection : Matrix (Fin 12) (Fin 6) (ZMod 2) := rect ![0,0,0,0,0,5,0,63,30,28,59,40]
private theorem selector_inclusion : selector * inclusion = 1 := by decide +kernel
private theorem reconstruction : inclusion * selector + equationSection * equations = 1 := by decide +kernel
private theorem inclusion_fixed (i : Fin 4) : generatorMatrix i * inclusion = inclusion := by
  fin_cases i <;> decide +kernel
set_option maxRecDepth 4000 in
theorem inclusion_singular : ∀ v : Fin 6 → ZMod 2,
    Unitary.quadraticForm (inclusion *ᵥ v) = 0 := by decide +kernel
private theorem equation0 : equations 0 = (generatorMatrix 0 - 1) 0 := by decide +kernel
private theorem equation1 : equations 1 = (generatorMatrix 0 - 1) 1 := by decide +kernel
private theorem equation2 : equations 2 = (generatorMatrix 0 - 1) 2 := by decide +kernel
private theorem equation3 : equations 3 = (generatorMatrix 0 - 1) 4 := by decide +kernel
private theorem equation4 : equations 4 = (generatorMatrix 1 - 1) 0 := by decide +kernel
private theorem equation5 : equations 5 = (generatorMatrix 1 - 1) 2 := by decide +kernel
private theorem fixed_coordinates (v : BinarySpace) (hv : ∀ i, generatorMatrix i *ᵥ v = v) :
    inclusion *ᵥ (selector *ᵥ v) = v := by
  have hz (i : Fin 4) : (generatorMatrix i - 1) *ᵥ v = 0 := by
    rw [Matrix.sub_mulVec,hv,Matrix.one_mulVec,sub_self]
  have he : equations *ᵥ v = 0 := by
    ext i
    fin_cases i
    · exact (show (equations 0) ⬝ᵥ v = ((generatorMatrix 0 - 1) *ᵥ v) 0 by rw [equation0]; rfl).trans (congrFun (hz 0) 0)
    · exact (show (equations 1) ⬝ᵥ v = ((generatorMatrix 0 - 1) *ᵥ v) 1 by rw [equation1]; rfl).trans (congrFun (hz 0) 1)
    · exact (show (equations 2) ⬝ᵥ v = ((generatorMatrix 0 - 1) *ᵥ v) 2 by rw [equation2]; rfl).trans (congrFun (hz 0) 2)
    · exact (show (equations 3) ⬝ᵥ v = ((generatorMatrix 0 - 1) *ᵥ v) 4 by rw [equation3]; rfl).trans (congrFun (hz 0) 4)
    · exact (show (equations 4) ⬝ᵥ v = ((generatorMatrix 1 - 1) *ᵥ v) 0 by rw [equation4]; rfl).trans (congrFun (hz 1) 0)
    · exact (show (equations 5) ⬝ᵥ v = ((generatorMatrix 1 - 1) *ᵥ v) 2 by rw [equation5]; rfl).trans (congrFun (hz 1) 2)
  have h := congrArg (fun M : Matrix12 => M *ᵥ v) reconstruction
  simpa only [Matrix.add_mulVec,← Matrix.mulVec_mulVec,he,Matrix.mulVec_zero,add_zero,Matrix.one_mulVec] using h

/-- The common fixed space of the four actual hexad translations. -/
def fixedSpace : Submodule (ZMod 2) BinarySpace where
  carrier := {v | ∀ i, generatorMatrix i *ᵥ v = v}
  zero_mem' := by intro i; exact Matrix.mulVec_zero _
  add_mem' := by
    intro v w hv hw i
    rw [Matrix.mulVec_add,hv,hw]
  smul_mem' := by
    intro a v hv i
    rw [Matrix.mulVec_smul,hv]

theorem fixedSpace_mem (v : BinarySpace) :
    v ∈ fixedSpace ↔ ∀ i, generatorMatrix i *ᵥ v = v := Iff.rfl

/-- Six explicit independent coordinates parametrize the whole fixed space. -/
def fixedSpaceEquiv : (Fin 6 → ZMod 2) ≃ₗ[ZMod 2] fixedSpace where
  toFun v := ⟨inclusion *ᵥ v,by
    intro i
    rw [Matrix.mulVec_mulVec,inclusion_fixed]⟩
  invFun v := selector *ᵥ v.val
  left_inv v := by
    change selector *ᵥ (inclusion *ᵥ v) = v
    rw [Matrix.mulVec_mulVec,selector_inclusion,Matrix.one_mulVec]
  right_inv v := Subtype.ext (fixed_coordinates v.val v.property)
  map_add' v w := Subtype.ext (Matrix.mulVec_add inclusion v w)
  map_smul' a v := Subtype.ext (Matrix.mulVec_smul inclusion a v)

theorem fixedSpace_card : Nat.card fixedSpace = 64 := by
  rw [←Nat.card_congr fixedSpaceEquiv.toEquiv]
  simp

theorem fixedSpace_finrank : Module.finrank (ZMod 2) fixedSpace = 6 := by
  rw [←fixedSpaceEquiv.finrank_eq]
  simp

theorem fixedSpace_singular (v : BinarySpace) (hv : v ∈ fixedSpace) :
    Unitary.quadraticForm v = 0 := by
  rw [←fixed_coordinates v hv]
  exact inclusion_singular _

/-- The generator equations are equivalent to fixing the entire actual subgroup. -/
theorem fixedSpace_iff_translations (v : BinarySpace) :
    v ∈ fixedSpace ↔ ∀ g ∈ translations, binaryRepresentation g v = v := by
  constructor
  · intro hv g hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      obtain ⟨i,rfl⟩ := hg
      rw [binaryRepresentation_apply,generator_matrix]
      exact hv i
    | one => rw [map_one]; rfl
    | mul g h _ _ hg hh =>
      rw [map_mul,Module.End.mul_apply,hh,hg]
    | inv g _ hg =>
      have he := congrArg (binaryRepresentation g⁻¹) hg
      rw [←Module.End.mul_apply,←map_mul,inv_mul_cancel,map_one] at he
      exact he.symm
  · intro hv i
    rw [←generator_matrix,←binaryRepresentation_apply]
    exact hv _ (subset_closure ⟨i,rfl⟩)

private theorem generator_mem_hexadKernel (i : Fin 4) :
    Uniqueness.quotientMap (generator i) ∈ m22HexadPointwiseKernel m22Hexad123 := by
  apply (mem_m22HexadPointwiseKernel _ _).mpr
  change ∀ a ∈ m22Hexad123, corePermutationAction (generator i) a = a
  rw [generator_permutation]
  revert i
  decide +kernel

private def maskWord (a : Fin 16) : M22TripleCover :=
  generator 0 ^ (a.val % 2) * generator 1 ^ (a.val / 2 % 2) *
    generator 2 ^ (a.val / 4 % 2) * generator 3 ^ (a.val / 8 % 2)

private def maskPerm (a : Fin 16) : Equiv.Perm (Fin 22) :=
  generatorPerm 0 ^ (a.val % 2) * generatorPerm 1 ^ (a.val / 2 % 2) *
    generatorPerm 2 ^ (a.val / 4 % 2) * generatorPerm 3 ^ (a.val / 8 % 2)

private theorem maskWord_mem (a : Fin 16) : maskWord a ∈ translations := by
  have hg (i : Fin 4) : generator i ∈ translations := subset_closure ⟨i,rfl⟩
  exact translations.mul_mem (translations.mul_mem
    (translations.mul_mem (translations.pow_mem (hg 0) _)
      (translations.pow_mem (hg 1) _)) (translations.pow_mem (hg 2) _))
    (translations.pow_mem (hg 3) _)

private theorem maskWord_permutation (a : Fin 16) :
    corePermutationAction (maskWord a) = maskPerm a := by
  simp only [maskWord,maskPerm,map_mul,map_pow,generator_permutation]

private theorem maskPerm_injective : Function.Injective (fun a : Fin 16 => maskPerm a 0) := by
  decide +kernel

/-- The four matrix translations project onto the exact pointwise hexad kernel. -/
theorem translations_image :
    translations.map Uniqueness.quotientMap = m22HexadPointwiseKernel m22Hexad123 := by
  have hle : translations.map Uniqueness.quotientMap ≤
      m22HexadPointwiseKernel m22Hexad123 := by
    apply map_le_iff_le_comap.mpr
    apply (closure_le _).mpr
    rintro g ⟨i,rfl⟩
    exact generator_mem_hexadKernel i
  apply eq_of_le_of_card_ge hle
  rw [m22HexadPointwiseKernel_card m22Hexad123_mem]
  let f (a : Fin 16) : translations.map Uniqueness.quotientMap :=
    ⟨Uniqueness.quotientMap (maskWord a),mem_map.mpr ⟨maskWord a,maskWord_mem a,rfl⟩⟩
  have hf : Function.Injective f := by
    intro a b hab
    apply maskPerm_injective
    have h := congrArg (fun g : translations.map Uniqueness.quotientMap =>
      (g.val.val : Equiv.Perm (Fin 22)) 0) hab
    change corePermutationAction (maskWord a) 0 = corePermutationAction (maskWord b) 0 at h
    simpa only [maskWord_permutation] using h
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

private theorem quotient_coprime : (Nat.card Uniqueness.quotientMap.ker).Coprime 2 := by
  rw [Uniqueness.quotientMap_ker,center_card]
  decide

theorem translations_projection_injective :
    Function.Injective (Uniqueness.quotientMap.subgroupMap translations) := by
  let : IsElementaryAbelian 2 translations := translations_elementary
  intro a b hab
  apply Subtype.ext
  exact Uniqueness.quotientMap.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker
    (Uniqueness.quotientMap_ker.le) quotient_coprime
    (congrArg Subtype.val hab)
    (elemPow_eq_one_of_isElementaryAbelian a.val a.property)
    (elemPow_eq_one_of_isElementaryAbelian b.val b.property)

theorem translations_card : Nat.card translations = 16 := by
  let e := MulEquiv.ofBijective (Uniqueness.quotientMap.subgroupMap translations)
    ⟨translations_projection_injective,Uniqueness.quotientMap.subgroupMap_surjective _⟩
  rw [Nat.card_congr e.toEquiv,translations_image,m22HexadPointwiseKernel_card m22Hexad123_mem]

/-- The matrix subgroup is the unique elementary lift of the literal kernel. -/
theorem translations_unique (P : Subgroup M22TripleCover)
    (hp : IsElementaryAbelian 2 P)
    (hi : P.map Uniqueness.quotientMap = m22HexadPointwiseKernel m22Hexad123) :
    P = translations := by
  let : IsElementaryAbelian 2 P := hp
  let : IsElementaryAbelian 2 translations := translations_elementary
  have images : P.map Uniqueness.quotientMap = translations.map Uniqueness.quotientMap :=
    hi.trans translations_image.symm
  apply le_antisymm
  · intro x hx
    obtain ⟨y,hy,he⟩ := images.le (mem_map_of_mem Uniqueness.quotientMap hx)
    have hxy : x = y := Uniqueness.quotientMap.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker
      Uniqueness.quotientMap_ker.le quotient_coprime he.symm
      (elemPow_eq_one_of_isElementaryAbelian x hx)
      (elemPow_eq_one_of_isElementaryAbelian y hy)
    exact hxy.symm ▸ hy
  · intro x hx
    obtain ⟨y,hy,he⟩ := images.ge (mem_map_of_mem Uniqueness.quotientMap hx)
    have hxy : x = y := Uniqueness.quotientMap.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker
      Uniqueness.quotientMap_ker.le quotient_coprime he.symm
      (elemPow_eq_one_of_isElementaryAbelian x hx)
      (elemPow_eq_one_of_isElementaryAbelian y hy)
    exact hxy.symm ▸ hy

/-- Every lift of a hexad stabilizer normalizes its elementary translation lift. -/
theorem translations_normalized :
    (MulAction.stabilizer M22 m22Hexad123).comap Uniqueness.quotientMap ≤
      normalizer (translations : Set M22TripleCover) := by
  let : IsElementaryAbelian 2 translations := translations_elementary
  intro g hg
  apply mem_normalizer_iff.mpr
  intro x
  have hdir (g : M22TripleCover)
      (hg : Uniqueness.quotientMap g ∈ MulAction.stabilizer M22 m22Hexad123)
      (x : M22TripleCover) (hx : x ∈ translations) : g*x*g⁻¹ ∈ translations := by
    have hn : Uniqueness.quotientMap g ∈
        normalizer (m22HexadPointwiseKernel m22Hexad123 : Set M22) := by
      rwa [m22HexadPointwiseKernel_normalizer m22Hexad123_mem]
    have hq : Uniqueness.quotientMap (g*x*g⁻¹) ∈ m22HexadPointwiseKernel m22Hexad123 := by
      rw [map_mul,map_mul,map_inv]
      exact (mem_normalizer_iff.mp hn _).mp (translations_image.le
        (mem_map_of_mem Uniqueness.quotientMap hx))
    obtain ⟨y,hy,he⟩ := translations_image.ge hq
    have heq : g*x*g⁻¹ = y :=
      Uniqueness.quotientMap.eq_of_map_eq_of_pow_eq_one_of_central_coprime_ker
        Uniqueness.quotientMap_ker.le quotient_coprime he.symm
        (by rw [conj_pow,elemPow_eq_one_of_isElementaryAbelian x hx]; simp)
        (elemPow_eq_one_of_isElementaryAbelian y hy)
    exact heq.symm ▸ hy
  constructor
  · exact hdir g hg x
  · intro hx
    have hi : Uniqueness.quotientMap g⁻¹ ∈ MulAction.stabilizer M22 m22Hexad123 := by
      rw [map_inv]
      exact (MulAction.stabilizer M22 m22Hexad123).inv_mem hg
    simpa only [inv_inv,mul_assoc,inv_mul_cancel,mul_one,inv_mul_cancel_left] using hdir g⁻¹ hi (g*x*g⁻¹) hx

end Theory.GroupTheory.Recognition.JankoFour.SourceRecognition.NativeHexadCoordinates