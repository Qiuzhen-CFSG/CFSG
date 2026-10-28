module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.RadicalAction.NativePositions
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SylowOrbit

/-! Three-coset certificates for the actual native moving parabolic in 14.4.12.
All words use the published native ATLAS matrices and the certified Sylow generators. -/

@[expose] public section
noncomputable section
open Matrix Subgroup Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender
open scoped Matrix
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.SecondActorPosition
open SylowCertificates OrbitCertificates RadicalAction

def rotationActor : Group := actor0 * actor1 * actor3 * actor1 * actor2 * actor1 * actor3 * actor0 * actor1 * actor2
theorem rotationActor_matrix : ((rotationActor : Matrix12ˣ) : Matrix12) = fromRows ![58, 718, 3198, 1236, 2850, 496, 1979, 3490, 2131, 1802, 3256, 628] := by
  simp only [rotationActor, Subgroup.coe_mul, Units.val_mul, actor0_matrix, actor1_matrix, actor3_matrix, actor2_matrix]
  rw [show (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) * (fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907]) = (fromRows ![1491, 2454, 3278, 1120, 2410, 4095, 385, 1600, 3370, 958, 2616, 37]) by decide +kernel]
  rw [show (fromRows ![1491, 2454, 3278, 1120, 2410, 4095, 385, 1600, 3370, 958, 2616, 37]) * (fromRows ![565, 891, 270, 2659, 1122, 4072, 7, 3987, 2066, 2224, 3204, 1561]) = (fromRows ![3630, 1935, 3359, 875, 2300, 1026, 1460, 1075, 1151, 3245, 3904, 3283]) by decide +kernel]
  rw [show (fromRows ![3630, 1935, 3359, 875, 2300, 1026, 1460, 1075, 1151, 3245, 3904, 3283]) * (fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907]) = (fromRows ![2559, 2204, 1980, 1390, 2031, 1572, 464, 1511, 3374, 1064, 2800, 2914]) by decide +kernel]
  rw [show (fromRows ![2559, 2204, 1980, 1390, 2031, 1572, 464, 1511, 3374, 1064, 2800, 2914]) * (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) = (fromRows ![121, 3092, 855, 1324, 3689, 2920, 3228, 3169, 3374, 2373, 3611, 709]) by decide +kernel]
  rw [show (fromRows ![121, 3092, 855, 1324, 3689, 2920, 3228, 3169, 3374, 2373, 3611, 709]) * (fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907]) = (fromRows ![3946, 691, 3075, 1356, 2488, 1629, 2027, 1399, 1151, 3317, 3676, 3984]) by decide +kernel]
  rw [show (fromRows ![3946, 691, 3075, 1356, 2488, 1629, 2027, 1399, 1151, 3317, 3676, 3984]) * (fromRows ![565, 891, 270, 2659, 1122, 4072, 7, 3987, 2066, 2224, 3204, 1561]) = (fromRows ![3272, 3559, 3027, 4092, 113, 2313, 1911, 3931, 3370, 3512, 3365, 462]) by decide +kernel]
  rw [show (fromRows ![3272, 3559, 3027, 4092, 113, 2313, 1911, 3931, 3370, 3512, 3365, 462]) * (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) = (fromRows ![2569, 1345, 2650, 3954, 2512, 2028, 2051, 35, 712, 598, 980, 1670]) by decide +kernel]
  rw [show (fromRows ![2569, 1345, 2650, 3954, 2512, 2028, 2051, 35, 712, 598, 980, 1670]) * (fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907]) = (fromRows ![2492, 3970, 3167, 3443, 711, 3260, 819, 1095, 1342, 898, 469, 3027]) by decide +kernel]
  rw [show (fromRows ![2492, 3970, 3167, 3443, 711, 3260, 819, 1095, 1342, 898, 469, 3027]) * (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) = (fromRows ![58, 718, 3198, 1236, 2850, 496, 1979, 3490, 2131, 1802, 3256, 628]) by decide +kernel]

theorem rotationActor_cube : rotationActor ^ 3 = 1 := by
  apply Subtype.ext
  apply Units.ext
  change ((rotationActor : Matrix12ˣ) : Matrix12) ^ 3 = 1
  rw [rotationActor_matrix, pow_succ, pow_two]
  rw [show (fromRows ![58, 718, 3198, 1236, 2850, 496, 1979, 3490, 2131, 1802, 3256, 628]) * (fromRows ![58, 718, 3198, 1236, 2850, 496, 1979, 3490, 2131, 1802, 3256, 628]) = (fromRows ![3272, 1911, 2497, 509, 3603, 2200, 689, 2051, 3097, 1531, 3432, 1565]) by decide +kernel]
  decide +kernel

def coefficient00 : Group := s0
theorem coefficient00_matrix : ((coefficient00 : Matrix12ˣ) : Matrix12) = fromRows ![3449, 1774, 2689, 547, 3744, 3682, 397, 1875, 712, 1533, 783, 4051] := by
  exact s0_matrix
def coefficient01 : Group := s0 * s3 * s1 * s4 * s3
theorem coefficient01_matrix : ((coefficient01 : Matrix12ˣ) : Matrix12) = fromRows ![3819, 3782, 3776, 32, 3235, 8, 3702, 3305, 2275, 3655, 3942, 954] := by
  simp only [coefficient01, Subgroup.coe_mul, Units.val_mul, s0_matrix, s3_matrix, s1_matrix, s4_matrix]
  rw [show (fromRows ![3449, 1774, 2689, 547, 3744, 3682, 397, 1875, 712, 1533, 783, 4051]) * (fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920]) = (fromRows ![2264, 3688, 3821, 3660, 2572, 3093, 3079, 1217, 1679, 1464, 620, 2673]) by decide +kernel]
  rw [show (fromRows ![2264, 3688, 3821, 3660, 2572, 3093, 3079, 1217, 1679, 1464, 620, 2673]) * (fromRows ![958, 2055, 1094, 3300, 1573, 139, 3829, 1917, 1188, 1491, 688, 4093]) = (fromRows ![3252, 2564, 2689, 3785, 652, 3216, 690, 2182, 773, 2851, 783, 459]) by decide +kernel]
  rw [show (fromRows ![3252, 2564, 2689, 3785, 652, 3216, 690, 2182, 773, 2851, 783, 459]) * (fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361]) = (fromRows ![2264, 3688, 3121, 882, 3866, 1015, 3401, 1217, 921, 1464, 802, 2221]) by decide +kernel]
  rw [show (fromRows ![2264, 3688, 3121, 882, 3866, 1015, 3401, 1217, 921, 1464, 802, 2221]) * (fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920]) = (fromRows ![3819, 3782, 3776, 32, 3235, 8, 3702, 3305, 2275, 3655, 3942, 954]) by decide +kernel]
def coefficient02 : Group := s3 * s4 * s3
theorem coefficient02_matrix : ((coefficient02 : Matrix12ˣ) : Matrix12) = fromRows ![958, 2055, 1128, 525, 2910, 3660, 1779, 1917, 2527, 1491, 2742, 4051] := by
  simp only [coefficient02, Subgroup.coe_mul, Units.val_mul, s3_matrix, s4_matrix]
  rw [show (fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920]) * (fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361]) = (fromRows ![3858, 196, 3078, 3133, 2279, 547, 561, 3495, 2760, 3294, 2960, 1590]) by decide +kernel]
  rw [show (fromRows ![3858, 196, 3078, 3133, 2279, 547, 561, 3495, 2760, 3294, 2960, 1590]) * (fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920]) = (fromRows ![958, 2055, 1128, 525, 2910, 3660, 1779, 1917, 2527, 1491, 2742, 4051]) by decide +kernel]
def coefficient10 : Group := s1
theorem coefficient10_matrix : ((coefficient10 : Matrix12ˣ) : Matrix12) = fromRows ![958, 2055, 1094, 3300, 1573, 139, 3829, 1917, 1188, 1491, 688, 4093] := by
  exact s1_matrix
def coefficient11 : Group := s1
theorem coefficient11_matrix : ((coefficient11 : Matrix12ˣ) : Matrix12) = fromRows ![958, 2055, 1094, 3300, 1573, 139, 3829, 1917, 1188, 1491, 688, 4093] := by
  exact s1_matrix
def coefficient12 : Group := s1
theorem coefficient12_matrix : ((coefficient12 : Matrix12ˣ) : Matrix12) = fromRows ![958, 2055, 1094, 3300, 1573, 139, 3829, 1917, 1188, 1491, 688, 4093] := by
  exact s1_matrix
def coefficient20 : Group := s2
theorem coefficient20_matrix : ((coefficient20 : Matrix12ˣ) : Matrix12) = fromRows ![618, 181, 1426, 1461, 2397, 1857, 1648, 2534, 3094, 1072, 3100, 358] := by
  exact s2_matrix
def coefficient21 : Group := s5 * s4 * s5
theorem coefficient21_matrix : ((coefficient21 : Matrix12ˣ) : Matrix12) = fromRows ![2512, 181, 179, 1327, 2503, 2368, 2937, 2534, 1188, 3096, 277, 4093] := by
  simp only [coefficient21, Subgroup.coe_mul, Units.val_mul, s5_matrix, s4_matrix]
  rw [show (fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504]) * (fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361]) = (fromRows ![3146, 37, 1321, 1471, 2771, 3290, 1779, 4051, 3979, 441, 2618, 3637]) by decide +kernel]
  rw [show (fromRows ![3146, 37, 1321, 1471, 2771, 3290, 1779, 4051, 3979, 441, 2618, 3637]) * (fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504]) = (fromRows ![2512, 181, 179, 1327, 2503, 2368, 2937, 2534, 1188, 3096, 277, 4093]) by decide +kernel]
def coefficient22 : Group := s4
theorem coefficient22_matrix : ((coefficient22 : Matrix12ˣ) : Matrix12) = fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361] := by
  exact s4_matrix
def coefficient30 : Group := s3
theorem coefficient30_matrix : ((coefficient30 : Matrix12ˣ) : Matrix12) = fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920] := by
  exact s3_matrix
def coefficient31 : Group := s0 * s4 * s3 * s4 * s0
theorem coefficient31_matrix : ((coefficient31 : Matrix12ˣ) : Matrix12) = fromRows ![3494, 3269, 3740, 2751, 2109, 1661, 1154, 786, 2085, 2023, 2154, 3920] := by
  simp only [coefficient31, Subgroup.coe_mul, Units.val_mul, s0_matrix, s4_matrix, s3_matrix]
  rw [show (fromRows ![3449, 1774, 2689, 547, 3744, 3682, 397, 1875, 712, 1533, 783, 4051]) * (fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361]) = (fromRows ![1362, 3781, 3121, 991, 598, 2751, 2443, 174, 3603, 444, 802, 328]) by decide +kernel]
  rw [show (fromRows ![1362, 3781, 3121, 991, 598, 2751, 2443, 174, 3603, 444, 802, 328]) * (fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920]) = (fromRows ![1180, 556, 3776, 3274, 797, 2368, 3401, 828, 660, 2225, 3942, 1560]) by decide +kernel]
  rw [show (fromRows ![1180, 556, 3776, 3274, 797, 2368, 3401, 828, 660, 2225, 3942, 1560]) * (fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361]) = (fromRows ![2890, 3578, 2160, 3722, 2762, 614, 690, 3963, 1609, 3472, 1265, 1220]) by decide +kernel]
  rw [show (fromRows ![2890, 3578, 2160, 3722, 2762, 614, 690, 3963, 1609, 3472, 1265, 1220]) * (fromRows ![3449, 1774, 2689, 547, 3744, 3682, 397, 1875, 712, 1533, 783, 4051]) = (fromRows ![3494, 3269, 3740, 2751, 2109, 1661, 1154, 786, 2085, 2023, 2154, 3920]) by decide +kernel]
def coefficient32 : Group := s5 * s3 * s5
theorem coefficient32_matrix : ((coefficient32 : Matrix12ˣ) : Matrix12) = fromRows ![1564, 3269, 41, 3300, 3572, 1321, 2615, 786, 1476, 4047, 1759, 2655] := by
  simp only [coefficient32, Subgroup.coe_mul, Units.val_mul, s5_matrix, s3_matrix]
  rw [show (fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504]) * (fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920]) = (fromRows ![1703, 2635, 146, 3915, 649, 179, 895, 1560, 3540, 2073, 3091, 2216]) by decide +kernel]
  rw [show (fromRows ![1703, 2635, 146, 3915, 649, 179, 895, 1560, 3540, 2073, 3091, 2216]) * (fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504]) = (fromRows ![1564, 3269, 41, 3300, 3572, 1321, 2615, 786, 1476, 4047, 1759, 2655]) by decide +kernel]
def coefficient40 : Group := s4
theorem coefficient40_matrix : ((coefficient40 : Matrix12ˣ) : Matrix12) = fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361] := by
  exact s4_matrix
def coefficient41 : Group := s2
theorem coefficient41_matrix : ((coefficient41 : Matrix12ˣ) : Matrix12) = fromRows ![618, 181, 1426, 1461, 2397, 1857, 1648, 2534, 3094, 1072, 3100, 358] := by
  exact s2_matrix
def coefficient42 : Group := s5 * s4 * s5
theorem coefficient42_matrix : ((coefficient42 : Matrix12ˣ) : Matrix12) = fromRows ![2512, 181, 179, 1327, 2503, 2368, 2937, 2534, 1188, 3096, 277, 4093] := by
  simp only [coefficient42, Subgroup.coe_mul, Units.val_mul, s5_matrix, s4_matrix]
  rw [show (fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504]) * (fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361]) = (fromRows ![3146, 37, 1321, 1471, 2771, 3290, 1779, 4051, 3979, 441, 2618, 3637]) by decide +kernel]
  rw [show (fromRows ![3146, 37, 1321, 1471, 2771, 3290, 1779, 4051, 3979, 441, 2618, 3637]) * (fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504]) = (fromRows ![2512, 181, 179, 1327, 2503, 2368, 2937, 2534, 1188, 3096, 277, 4093]) by decide +kernel]
def coefficient50 : Group := s5
theorem coefficient50_matrix : ((coefficient50 : Matrix12ˣ) : Matrix12) = fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504] := by
  exact s5_matrix
def coefficient51 : Group := s5
theorem coefficient51_matrix : ((coefficient51 : Matrix12ˣ) : Matrix12) = fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504] := by
  exact s5_matrix
def coefficient52 : Group := s5
theorem coefficient52_matrix : ((coefficient52 : Matrix12ˣ) : Matrix12) = fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504] := by
  exact s5_matrix
def coefficient60 : Group := 1
theorem coefficient60_matrix : ((coefficient60 : Matrix12ˣ) : Matrix12) = fromRows ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048] := by
  decide +kernel
def coefficient61 : Group := 1
theorem coefficient61_matrix : ((coefficient61 : Matrix12ˣ) : Matrix12) = fromRows ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048] := by
  decide +kernel
def coefficient62 : Group := 1
theorem coefficient62_matrix : ((coefficient62 : Matrix12ˣ) : Matrix12) = fromRows ![1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048] := by
  decide +kernel

def actor : Fin 7 → Group := ![s0,s1,s2,s3,s4,s5,rotationActor]
def representative : Fin 3 → Group := ![1,rotationActor,rotationActor * rotationActor]
def coefficient : Fin 7 → Fin 3 → Group := ![![coefficient00,coefficient01,coefficient02], ![coefficient10,coefficient11,coefficient12], ![coefficient20,coefficient21,coefficient22], ![coefficient30,coefficient31,coefficient32], ![coefficient40,coefficient41,coefficient42], ![coefficient50,coefficient51,coefficient52], ![coefficient60,coefficient61,coefficient62]]
def next : Fin 7 → Fin 3 → Fin 3 := ![![0,1,2],![0,1,2],![0,1,2],![0,1,2],![0,1,2],![0,2,1],![1,2,0]]
def previous : Fin 7 → Fin 3 → Fin 3 := ![![0,1,2],![0,1,2],![0,1,2],![0,1,2],![0,1,2],![0,2,1],![2,0,1]]
theorem next_previous (a : Fin 7) (i : Fin 3) : next a (previous a i) = i := by revert a i; decide +kernel

theorem coefficient_mem (a : Fin 7) (i : Fin 3) : coefficient a i ∈ candidate := by
  have hs (j : Fin 6) : generator j ∈ candidate := subset_closure ⟨j,rfl⟩
  have h0 : s0 ∈ candidate := hs 0
  have h1 : s1 ∈ candidate := hs 1
  have h2 : s2 ∈ candidate := hs 2
  have h3 : s3 ∈ candidate := hs 3
  have h4 : s4 ∈ candidate := hs 4
  have h5 : s5 ∈ candidate := hs 5
  fin_cases a <;> fin_cases i
  · exact h0
  · exact candidate.mul_mem (candidate.mul_mem (candidate.mul_mem (candidate.mul_mem (h0) h3) h1) h4) h3
  · exact candidate.mul_mem (candidate.mul_mem (h3) h4) h3
  · exact h1
  · exact h1
  · exact h1
  · exact h2
  · exact candidate.mul_mem (candidate.mul_mem (h5) h4) h5
  · exact h4
  · exact h3
  · exact candidate.mul_mem (candidate.mul_mem (candidate.mul_mem (candidate.mul_mem (h0) h4) h3) h4) h0
  · exact candidate.mul_mem (candidate.mul_mem (h5) h3) h5
  · exact h4
  · exact h2
  · exact candidate.mul_mem (candidate.mul_mem (h5) h4) h5
  · exact h5
  · exact h5
  · exact h5
  · exact candidate.one_mem
  · exact candidate.one_mem
  · exact candidate.one_mem

theorem rotationActor_square_matrix : (((rotationActor * rotationActor : Group) : Matrix12ˣ) : Matrix12) = fromRows ![3272, 1911, 2497, 509, 3603, 2200, 689, 2051, 3097, 1531, 3432, 1565] := by
  change ((rotationActor : Matrix12ˣ) : Matrix12) * ((rotationActor : Matrix12ˣ) : Matrix12) = _
  rw [rotationActor_matrix]
  decide +kernel

theorem transition00 : representative 0 * actor 0 = coefficient 0 0 * representative (next 0 0) := by
  apply Subtype.ext
  apply Units.ext
  change ((1 : Group).val : Matrix12) * ((s0 : Matrix12ˣ) : Matrix12) = ((coefficient00 : Matrix12ˣ) : Matrix12) * ((1 : Group).val : Matrix12)
  rw [Subgroup.coe_one, Units.val_one, s0_matrix, coefficient00_matrix]
  decide +kernel

theorem transition01 : representative 1 * actor 0 = coefficient 0 1 * representative (next 0 1) := by
  apply Subtype.ext
  apply Units.ext
  change ((rotationActor : Group).val : Matrix12) * ((s0 : Matrix12ˣ) : Matrix12) = ((coefficient01 : Matrix12ˣ) : Matrix12) * ((rotationActor : Group).val : Matrix12)
  rw [rotationActor_matrix, s0_matrix, coefficient01_matrix]
  decide +kernel

theorem transition02 : representative 2 * actor 0 = coefficient 0 2 * representative (next 0 2) := by
  apply Subtype.ext
  apply Units.ext
  change (((rotationActor * rotationActor) : Group).val : Matrix12) * ((s0 : Matrix12ˣ) : Matrix12) = ((coefficient02 : Matrix12ˣ) : Matrix12) * (((rotationActor * rotationActor) : Group).val : Matrix12)
  rw [rotationActor_square_matrix, s0_matrix, coefficient02_matrix]
  decide +kernel

theorem transition10 : representative 0 * actor 1 = coefficient 1 0 * representative (next 1 0) := by
  apply Subtype.ext
  apply Units.ext
  change ((1 : Group).val : Matrix12) * ((s1 : Matrix12ˣ) : Matrix12) = ((coefficient10 : Matrix12ˣ) : Matrix12) * ((1 : Group).val : Matrix12)
  rw [Subgroup.coe_one, Units.val_one, s1_matrix, coefficient10_matrix]
  decide +kernel

theorem transition11 : representative 1 * actor 1 = coefficient 1 1 * representative (next 1 1) := by
  apply Subtype.ext
  apply Units.ext
  change ((rotationActor : Group).val : Matrix12) * ((s1 : Matrix12ˣ) : Matrix12) = ((coefficient11 : Matrix12ˣ) : Matrix12) * ((rotationActor : Group).val : Matrix12)
  rw [rotationActor_matrix, s1_matrix, coefficient11_matrix]
  decide +kernel

theorem transition12 : representative 2 * actor 1 = coefficient 1 2 * representative (next 1 2) := by
  apply Subtype.ext
  apply Units.ext
  change (((rotationActor * rotationActor) : Group).val : Matrix12) * ((s1 : Matrix12ˣ) : Matrix12) = ((coefficient12 : Matrix12ˣ) : Matrix12) * (((rotationActor * rotationActor) : Group).val : Matrix12)
  rw [rotationActor_square_matrix, s1_matrix, coefficient12_matrix]
  decide +kernel

theorem transition20 : representative 0 * actor 2 = coefficient 2 0 * representative (next 2 0) := by
  apply Subtype.ext
  apply Units.ext
  change ((1 : Group).val : Matrix12) * ((s2 : Matrix12ˣ) : Matrix12) = ((coefficient20 : Matrix12ˣ) : Matrix12) * ((1 : Group).val : Matrix12)
  rw [Subgroup.coe_one, Units.val_one, s2_matrix, coefficient20_matrix]
  decide +kernel

theorem transition21 : representative 1 * actor 2 = coefficient 2 1 * representative (next 2 1) := by
  apply Subtype.ext
  apply Units.ext
  change ((rotationActor : Group).val : Matrix12) * ((s2 : Matrix12ˣ) : Matrix12) = ((coefficient21 : Matrix12ˣ) : Matrix12) * ((rotationActor : Group).val : Matrix12)
  rw [rotationActor_matrix, s2_matrix, coefficient21_matrix]
  decide +kernel

theorem transition22 : representative 2 * actor 2 = coefficient 2 2 * representative (next 2 2) := by
  apply Subtype.ext
  apply Units.ext
  change (((rotationActor * rotationActor) : Group).val : Matrix12) * ((s2 : Matrix12ˣ) : Matrix12) = ((coefficient22 : Matrix12ˣ) : Matrix12) * (((rotationActor * rotationActor) : Group).val : Matrix12)
  rw [rotationActor_square_matrix, s2_matrix, coefficient22_matrix]
  decide +kernel

theorem transition30 : representative 0 * actor 3 = coefficient 3 0 * representative (next 3 0) := by
  apply Subtype.ext
  apply Units.ext
  change ((1 : Group).val : Matrix12) * ((s3 : Matrix12ˣ) : Matrix12) = ((coefficient30 : Matrix12ˣ) : Matrix12) * ((1 : Group).val : Matrix12)
  rw [Subgroup.coe_one, Units.val_one, s3_matrix, coefficient30_matrix]
  decide +kernel

theorem transition31 : representative 1 * actor 3 = coefficient 3 1 * representative (next 3 1) := by
  apply Subtype.ext
  apply Units.ext
  change ((rotationActor : Group).val : Matrix12) * ((s3 : Matrix12ˣ) : Matrix12) = ((coefficient31 : Matrix12ˣ) : Matrix12) * ((rotationActor : Group).val : Matrix12)
  rw [rotationActor_matrix, s3_matrix, coefficient31_matrix]
  decide +kernel

theorem transition32 : representative 2 * actor 3 = coefficient 3 2 * representative (next 3 2) := by
  apply Subtype.ext
  apply Units.ext
  change (((rotationActor * rotationActor) : Group).val : Matrix12) * ((s3 : Matrix12ˣ) : Matrix12) = ((coefficient32 : Matrix12ˣ) : Matrix12) * (((rotationActor * rotationActor) : Group).val : Matrix12)
  rw [rotationActor_square_matrix, s3_matrix, coefficient32_matrix]
  decide +kernel

theorem transition40 : representative 0 * actor 4 = coefficient 4 0 * representative (next 4 0) := by
  apply Subtype.ext
  apply Units.ext
  change ((1 : Group).val : Matrix12) * ((s4 : Matrix12ˣ) : Matrix12) = ((coefficient40 : Matrix12ˣ) : Matrix12) * ((1 : Group).val : Matrix12)
  rw [Subgroup.coe_one, Units.val_one, s4_matrix, coefficient40_matrix]
  decide +kernel

theorem transition41 : representative 1 * actor 4 = coefficient 4 1 * representative (next 4 1) := by
  apply Subtype.ext
  apply Units.ext
  change ((rotationActor : Group).val : Matrix12) * ((s4 : Matrix12ˣ) : Matrix12) = ((coefficient41 : Matrix12ˣ) : Matrix12) * ((rotationActor : Group).val : Matrix12)
  rw [rotationActor_matrix, s4_matrix, coefficient41_matrix]
  decide +kernel

theorem transition42 : representative 2 * actor 4 = coefficient 4 2 * representative (next 4 2) := by
  apply Subtype.ext
  apply Units.ext
  change (((rotationActor * rotationActor) : Group).val : Matrix12) * ((s4 : Matrix12ˣ) : Matrix12) = ((coefficient42 : Matrix12ˣ) : Matrix12) * (((rotationActor * rotationActor) : Group).val : Matrix12)
  rw [rotationActor_square_matrix, s4_matrix, coefficient42_matrix]
  decide +kernel

theorem transition50 : representative 0 * actor 5 = coefficient 5 0 * representative (next 5 0) := by
  apply Subtype.ext
  apply Units.ext
  change ((1 : Group).val : Matrix12) * ((s5 : Matrix12ˣ) : Matrix12) = ((coefficient50 : Matrix12ˣ) : Matrix12) * ((1 : Group).val : Matrix12)
  rw [Subgroup.coe_one, Units.val_one, s5_matrix, coefficient50_matrix]
  decide +kernel

theorem transition51 : representative 1 * actor 5 = coefficient 5 1 * representative (next 5 1) := by
  apply Subtype.ext
  apply Units.ext
  change ((rotationActor : Group).val : Matrix12) * ((s5 : Matrix12ˣ) : Matrix12) = ((coefficient51 : Matrix12ˣ) : Matrix12) * (((rotationActor * rotationActor) : Group).val : Matrix12)
  rw [rotationActor_square_matrix, rotationActor_matrix, s5_matrix, coefficient51_matrix]
  decide +kernel

theorem transition52 : representative 2 * actor 5 = coefficient 5 2 * representative (next 5 2) := by
  apply Subtype.ext
  apply Units.ext
  change (((rotationActor * rotationActor) : Group).val : Matrix12) * ((s5 : Matrix12ˣ) : Matrix12) = ((coefficient52 : Matrix12ˣ) : Matrix12) * ((rotationActor : Group).val : Matrix12)
  rw [rotationActor_square_matrix, rotationActor_matrix, s5_matrix, coefficient52_matrix]
  decide +kernel

theorem transition60 : representative 0 * actor 6 = coefficient 6 0 * representative (next 6 0) := by
  apply Subtype.ext
  apply Units.ext
  change ((1 : Group).val : Matrix12) * ((rotationActor : Matrix12ˣ) : Matrix12) = ((coefficient60 : Matrix12ˣ) : Matrix12) * ((rotationActor : Group).val : Matrix12)
  rw [Subgroup.coe_one, Units.val_one, rotationActor_matrix, coefficient60_matrix]
  decide +kernel

theorem transition61 : representative 1 * actor 6 = coefficient 6 1 * representative (next 6 1) := by
  apply Subtype.ext
  apply Units.ext
  change ((rotationActor : Group).val : Matrix12) * ((rotationActor : Matrix12ˣ) : Matrix12) = ((coefficient61 : Matrix12ˣ) : Matrix12) * (((rotationActor * rotationActor) : Group).val : Matrix12)
  rw [rotationActor_square_matrix, rotationActor_matrix, coefficient61_matrix]
  decide +kernel

theorem transition62 : representative 2 * actor 6 = coefficient 6 2 * representative (next 6 2) := by
  apply Subtype.ext
  apply Units.ext
  change (((rotationActor * rotationActor) : Group).val : Matrix12) * ((rotationActor : Matrix12ˣ) : Matrix12) = ((coefficient62 : Matrix12ˣ) : Matrix12) * ((1 : Group).val : Matrix12)
  rw [Subgroup.coe_one, Units.val_one, rotationActor_square_matrix, rotationActor_matrix, coefficient62_matrix]
  decide +kernel

theorem transition (a : Fin 7) (i : Fin 3) : representative i * actor a = coefficient a i * representative (next a i) := by
  fin_cases a <;> fin_cases i
  · exact transition00
  · exact transition01
  · exact transition02
  · exact transition10
  · exact transition11
  · exact transition12
  · exact transition20
  · exact transition21
  · exact transition22
  · exact transition30
  · exact transition31
  · exact transition32
  · exact transition40
  · exact transition41
  · exact transition42
  · exact transition50
  · exact transition51
  · exact transition52
  · exact transition60
  · exact transition61
  · exact transition62

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native.SecondActorPosition
