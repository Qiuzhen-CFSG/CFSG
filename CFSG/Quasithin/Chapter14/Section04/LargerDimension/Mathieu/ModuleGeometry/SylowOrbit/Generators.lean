module
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.SylowOrbit.Orbit
public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ActorCatalogue.Native
public import Theory.LinearAlgebra.BinaryTriangularPGroup

/-!
# A triangular two-subgroup in the native Mathieu parabolic

Six explicit parabolic words fix the marked vector. A checked change of basis
makes them lower triangular over F₂. Closure inside the triangular submonoid
and the faithful triangular representation prove that their generated subgroup
is a two-group. The cardinality of the native ambient group is obtained from
the genuine triple cover and its already proved index-two extension.

These are the small certificates for the Sylow marking in Aschbacher–Smith
H.12.1(9) and 14.4.12, printed pp.393–394 and 1011–1012. Matrix identities are
kernel checked; `Orbit` retains the attribution of the underlying ATLAS data.
-/

@[expose] public section
noncomputable section
open Matrix Representation.SL2FourNatural
open Sporadic.Mathieu M22TripleCover
open Janko4.OuterReduction.FixedGenerator.NormalizerSquares.TwoCoreLinearModel
open Representation.BinaryOffender Subgroup
open scoped Matrix
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native
namespace SylowCertificates
open OrbitCertificates
def s0 : Group := actor0 * actor1 * actor0
theorem s0_matrix : ((s0 : Matrix12ˣ) : Matrix12) = fromRows ![3449, 1774, 2689, 547, 3744, 3682, 397, 1875, 712, 1533, 783, 4051] := by
  simp only [s0, Subgroup.coe_mul, Units.val_mul, actor0_matrix, actor1_matrix]
  rw [show (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) * (fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907]) = fromRows ![1491, 2454, 3278, 1120, 2410, 4095, 385, 1600, 3370, 958, 2616, 37] by decide +kernel]
  rw [show (fromRows ![1491, 2454, 3278, 1120, 2410, 4095, 385, 1600, 3370, 958, 2616, 37]) * (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) = fromRows ![3449, 1774, 2689, 547, 3744, 3682, 397, 1875, 712, 1533, 783, 4051] by decide +kernel]
theorem s0_mem : s0 ∈ parabolic := (parabolic.mul_mem (parabolic.mul_mem actor0_mem actor1_mem) actor0_mem)

def s1 : Group := actor1 * actor0 * actor1
theorem s1_matrix : ((s1 : Matrix12ˣ) : Matrix12) = fromRows ![958, 2055, 1094, 3300, 1573, 139, 3829, 1917, 1188, 1491, 688, 4093] := by
  simp only [s1, Subgroup.coe_mul, Units.val_mul, actor0_matrix, actor1_matrix]
  rw [show (fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907]) * (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) = fromRows ![2875, 1875, 547, 2689, 1538, 280, 2372, 1774, 3477, 400, 2132, 2059] by decide +kernel]
  rw [show (fromRows ![2875, 1875, 547, 2689, 1538, 280, 2372, 1774, 3477, 400, 2132, 2059]) * (fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907]) = fromRows ![958, 2055, 1094, 3300, 1573, 139, 3829, 1917, 1188, 1491, 688, 4093] by decide +kernel]
theorem s1_mem : s1 ∈ parabolic := (parabolic.mul_mem (parabolic.mul_mem actor1_mem actor0_mem) actor1_mem)

def s2 : Group := actor2 * actor0 * actor3 * actor0 * actor2
theorem s2_matrix : ((s2 : Matrix12ˣ) : Matrix12) = fromRows ![618, 181, 1426, 1461, 2397, 1857, 1648, 2534, 3094, 1072, 3100, 358] := by
  simp only [s2, Subgroup.coe_mul, Units.val_mul, actor0_matrix, actor2_matrix, actor3_matrix]
  rw [show (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) * (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) = fromRows ![400, 1559, 4051, 1446, 1499, 3659, 128, 1477, 3220, 3737, 2586, 1639] by decide +kernel]
  rw [show (fromRows ![400, 1559, 4051, 1446, 1499, 3659, 128, 1477, 3220, 3737, 2586, 1639]) * (fromRows ![565, 891, 270, 2659, 1122, 4072, 7, 3987, 2066, 2224, 3204, 1561]) = fromRows ![995, 22, 135, 1688, 1101, 2311, 3987, 2105, 98, 394, 979, 2971] by decide +kernel]
  rw [show (fromRows ![995, 22, 135, 1688, 1101, 2311, 3987, 2105, 98, 394, 979, 2971]) * (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) = fromRows ![618, 148, 282, 350, 3572, 1888, 1586, 2468, 2268, 153, 3133, 3145] by decide +kernel]
  rw [show (fromRows ![618, 148, 282, 350, 3572, 1888, 1586, 2468, 2268, 153, 3133, 3145]) * (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) = fromRows ![618, 181, 1426, 1461, 2397, 1857, 1648, 2534, 3094, 1072, 3100, 358] by decide +kernel]
theorem s2_mem : s2 ∈ parabolic := (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem actor2_mem actor0_mem) actor3_mem) actor0_mem) actor2_mem)

def s3 : Group := actor3 * actor0 * actor2 * actor1 * actor2
theorem s3_matrix : ((s3 : Matrix12ˣ) : Matrix12) = fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920] := by
  simp only [s3, Subgroup.coe_mul, Units.val_mul, actor0_matrix, actor1_matrix, actor2_matrix, actor3_matrix]
  rw [show (fromRows ![565, 891, 270, 2659, 1122, 4072, 7, 3987, 2066, 2224, 3204, 1561]) * (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) = fromRows ![1268, 624, 147, 1040, 675, 3942, 280, 1586, 1787, 2098, 3090, 204] by decide +kernel]
  rw [show (fromRows ![1268, 624, 147, 1040, 675, 3942, 280, 1586, 1787, 2098, 3090, 204]) * (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) = fromRows ![3411, 3062, 209, 185, 2853, 3876, 1490, 1648, 3903, 1309, 2297, 2411] by decide +kernel]
  rw [show (fromRows ![3411, 3062, 209, 185, 2853, 3876, 1490, 1648, 3903, 1309, 2297, 2411]) * (fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907]) = fromRows ![3957, 225, 2613, 1691, 3220, 3824, 912, 449, 1978, 1679, 399, 540] by decide +kernel]
  rw [show (fromRows ![3957, 225, 2613, 1691, 3220, 3824, 912, 449, 1978, 1679, 399, 540]) * (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) = fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920] by decide +kernel]
theorem s3_mem : s3 ∈ parabolic := (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem actor3_mem actor0_mem) actor2_mem) actor1_mem) actor2_mem)

def s4 : Group := actor2 * actor0 * actor2 * actor3 * actor2 * actor0 * actor2
theorem s4_matrix : ((s4 : Matrix12ˣ) : Matrix12) = fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361] := by
  simp only [s4, Subgroup.coe_mul, Units.val_mul, actor0_matrix, actor2_matrix, actor3_matrix]
  rw [show (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) * (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) = fromRows ![400, 1559, 4051, 1446, 1499, 3659, 128, 1477, 3220, 3737, 2586, 1639] by decide +kernel]
  rw [show (fromRows ![400, 1559, 4051, 1446, 1499, 3659, 128, 1477, 3220, 3737, 2586, 1639]) * (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) = fromRows ![3230, 1652, 4016, 3170, 1464, 1935, 3565, 3073, 1393, 1885, 1845, 2859] by decide +kernel]
  rw [show (fromRows ![3230, 1652, 4016, 3170, 1464, 1935, 3565, 3073, 1393, 1885, 1845, 2859]) * (fromRows ![565, 891, 270, 2659, 1122, 4072, 7, 3987, 2066, 2224, 3204, 1561]) = fromRows ![2426, 3767, 3622, 1545, 2796, 2454, 2987, 2216, 3374, 283, 1175, 638] by decide +kernel]
  rw [show (fromRows ![2426, 3767, 3622, 1545, 2796, 2454, 2987, 2216, 3374, 283, 1175, 638]) * (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) = fromRows ![3504, 953, 808, 4045, 2018, 1275, 2954, 364, 3374, 1427, 3376, 3890] by decide +kernel]
  rw [show (fromRows ![3504, 953, 808, 4045, 2018, 1275, 2954, 364, 3374, 1427, 3376, 3890]) * (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) = fromRows ![594, 1253, 1387, 181, 2437, 809, 3525, 2127, 704, 2926, 592, 2539] by decide +kernel]
  rw [show (fromRows ![594, 1253, 1387, 181, 2437, 809, 3525, 2127, 704, 2926, 592, 2539]) * (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) = fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361] by decide +kernel]
theorem s4_mem : s4 ∈ parabolic := (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem actor2_mem actor0_mem) actor2_mem) actor3_mem) actor2_mem) actor0_mem) actor2_mem)

def s5 : Group := actor2 * actor1 * actor3 * actor0 * actor3 * actor1 * actor2
theorem s5_matrix : ((s5 : Matrix12ˣ) : Matrix12) = fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504] := by
  simp only [s5, Subgroup.coe_mul, Units.val_mul, actor0_matrix, actor1_matrix, actor2_matrix, actor3_matrix]
  rw [show (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) * (fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907]) = fromRows ![512, 103, 1639, 3061, 412, 7, 1600, 2510, 2553, 1850, 1799, 1907] by decide +kernel]
  rw [show (fromRows ![512, 103, 1639, 3061, 412, 7, 1600, 2510, 2553, 1850, 1799, 1907]) * (fromRows ![565, 891, 270, 2659, 1122, 4072, 7, 3987, 2066, 2224, 3204, 1561]) = fromRows ![2224, 4015, 2971, 414, 2190, 64, 1075, 2441, 579, 3764, 3174, 1765] by decide +kernel]
  rw [show (fromRows ![2224, 4015, 2971, 414, 2190, 64, 1075, 2441, 579, 3764, 3174, 1765]) * (fromRows ![400, 128, 8, 4, 28, 3659, 1559, 2, 31, 2875, 2687, 1639]) = fromRows ![2098, 2153, 3145, 141, 1769, 1559, 1336, 2030, 3132, 2430, 1228, 2178] by decide +kernel]
  rw [show (fromRows ![2098, 2153, 3145, 141, 1769, 1559, 1336, 2030, 3132, 2430, 1228, 2178]) * (fromRows ![565, 891, 270, 2659, 1122, 4072, 7, 3987, 2066, 2224, 3204, 1561]) = fromRows ![3816, 416, 716, 1739, 3102, 22, 1407, 1100, 2682, 3472, 2173, 2801] by decide +kernel]
  rw [show (fromRows ![3816, 416, 716, 1739, 3102, 22, 1407, 1100, 2682, 3472, 2173, 2801]) * (fromRows ![512, 1600, 1120, 3278, 452, 7, 103, 2454, 3457, 1, 100, 1907]) = fromRows ![558, 1040, 350, 282, 2109, 996, 175, 2221, 3160, 708, 3193, 3392] by decide +kernel]
  rw [show (fromRows ![558, 1040, 350, 282, 2109, 996, 175, 2221, 3160, 708, 3193, 3392]) * (fromRows ![1, 64, 37, 1185, 3453, 32, 2, 3565, 3086, 1705, 3524, 2048]) = fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504] by decide +kernel]
theorem s5_mem : s5 ∈ parabolic := (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem (parabolic.mul_mem actor2_mem actor1_mem) actor3_mem) actor0_mem) actor3_mem) actor1_mem) actor2_mem)

def generator : Fin 6 → Group := ![s0, s1, s2, s3, s4, s5]
def generatorMatrix : Fin 6 → Matrix12 := ![(fromRows ![3449, 1774, 2689, 547, 3744, 3682, 397, 1875, 712, 1533, 783, 4051]), (fromRows ![958, 2055, 1094, 3300, 1573, 139, 3829, 1917, 1188, 1491, 688, 4093]), (fromRows ![618, 181, 1426, 1461, 2397, 1857, 1648, 2534, 3094, 1072, 3100, 358]), (fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920]), (fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361]), (fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504])]
theorem generator_matrix : ∀ i, ((generator i : Matrix12ˣ) : Matrix12) = generatorMatrix i := by
  intro i
  fin_cases i
  · exact s0_matrix
  · exact s1_matrix
  · exact s2_matrix
  · exact s3_matrix
  · exact s4_matrix
  · exact s5_matrix
theorem generator_mem : ∀ i, generator i ∈ parabolic := by
  intro i
  fin_cases i
  · exact s0_mem
  · exact s1_mem
  · exact s2_mem
  · exact s3_mem
  · exact s4_mem
  · exact s5_mem
theorem generator_fixed : ∀ i, generatorMatrix i *ᵥ markedVector = markedVector := by decide +kernel

def candidate : Subgroup Group := closure (Set.range generator)

theorem candidate_le_parabolic : candidate ≤ parabolic :=
  (closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact generator_mem i)

theorem candidate_le_pointCentralizer : candidate ≤ pointCentralizer := by
  apply (closure_le _).mpr
  rintro _ ⟨i, rfl⟩
  refine ⟨mem_top _, ?_⟩
  intro v hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
  rw [map_smul]
  change a • (((generator i : Matrix12ˣ) : Matrix12) *ᵥ markedVector) = a • markedVector
  rw [generator_matrix]
  exact congrArg (fun v => a • v) (generator_fixed i)
def flag : Matrix12 := fromRows ![2397, 2478, 2416, 3464, 1860, 3392, 256, 160, 3072, 512, 2048, 128]
def flagInverse : Matrix12 := fromRows ![2045, 3002, 1584, 2376, 3492, 2176, 352, 2048, 64, 512, 1280, 1024]
theorem flag_inv : flag * flagInverse = 1 := by decide +kernel
theorem inv_flag : flagInverse * flag = 1 := by decide +kernel

def flagUnit : Matrix12ˣ := ⟨flagInverse, flag, inv_flag, flag_inv⟩

def coordinateHom : Group →* Matrix12 :=
  ((Units.coeHom Matrix12).comp (MulAut.conj flagUnit).toMonoidHom).comp actionGroup.subtype

theorem coordinateHom_apply (g : Group) :
    coordinateHom g = flagInverse * ((g : Matrix12ˣ) : Matrix12) * flag := rfl

theorem coordinateHom_injective : Function.Injective coordinateHom := by
  intro g h he
  apply Subtype.ext
  apply (MulAut.conj flagUnit).injective
  exact Units.ext he
theorem coordinates_s0 : coordinateHom s0 = fromRows ![1, 2, 4, 9, 16, 32, 67, 151, 261, 513, 1059, 2571] := by
  rw [coordinateHom_apply, s0_matrix]
  rw [show flagInverse * (fromRows ![3449, 1774, 2689, 547, 3744, 3682, 397, 1875, 712, 1533, 783, 4051]) = fromRows ![2045, 3002, 1584, 3765, 3492, 2176, 3367, 4051, 397, 1533, 455, 783] by decide +kernel]
  decide +kernel
theorem coordinates_s1 : coordinateHom s1 = fromRows ![1, 2, 5, 8, 17, 32, 66, 129, 265, 535, 1076, 2212] := by
  rw [coordinateHom_apply, s1_matrix]
  rw [show flagInverse * (fromRows ![958, 2055, 1094, 3300, 1573, 139, 3829, 1917, 1188, 1491, 688, 4093]) = fromRows ![2045, 3002, 461, 2376, 2649, 2176, 2778, 4093, 3829, 1491, 1556, 688] by decide +kernel]
  decide +kernel
theorem coordinates_s2 : coordinateHom s2 = fromRows ![1, 2, 4, 9, 17, 32, 67, 158, 260, 516, 1062, 2876] := by
  rw [coordinateHom_apply, s2_matrix]
  rw [show flagInverse * (fromRows ![618, 181, 1426, 1461, 2397, 1857, 1648, 2534, 3094, 1072, 3100, 358]) = fromRows ![2045, 3002, 1584, 3765, 2649, 2176, 3367, 358, 1648, 1072, 10, 3100] by decide +kernel]
  decide +kernel
theorem coordinates_s3 : coordinateHom s3 = fromRows ![1, 2, 5, 8, 27, 36, 66, 196, 263, 813, 1076, 2462] := by
  rw [coordinateHom_apply, s3_matrix]
  rw [show flagInverse * (fromRows ![536, 3534, 976, 3869, 1393, 991, 2615, 480, 818, 581, 1318, 3920]) = fromRows ![2045, 3002, 461, 2376, 2219, 3760, 2778, 3920, 2615, 581, 1556, 1318] by decide +kernel]
  decide +kernel
theorem coordinates_s4 : coordinateHom s4 = fromRows ![1, 2, 7, 10, 17, 62, 64, 157, 349, 605, 2020, 2234] := by
  rw [coordinateHom_apply, s4_matrix]
  rw [show flagInverse * (fromRows ![2966, 47, 1288, 148, 2503, 3623, 1025, 3271, 2886, 1601, 3030, 3361]) = fromRows ![2045, 3002, 2679, 754, 2649, 486, 352, 3361, 1025, 1601, 144, 3030] by decide +kernel]
  decide +kernel
theorem coordinates_s5 : coordinateHom s5 = fromRows ![1, 3, 5, 8, 17, 32, 79, 168, 264, 563, 1053, 4095] := by
  rw [coordinateHom_apply, s5_matrix]
  rw [show flagInverse * (fromRows ![589, 185, 1461, 1426, 472, 1869, 2312, 328, 3098, 2915, 3131, 2504]) = fromRows ![2045, 3143, 461, 2376, 2649, 2176, 607, 2504, 2312, 2915, 33, 3131] by decide +kernel]
  decide +kernel
theorem coordinates_lower : ∀ i, (coordinateHom (generator i)).IsLowerTriangular := by
  intro i
  fin_cases i
  · change (coordinateHom s0).IsLowerTriangular
    rw [coordinates_s0]
    decide +kernel
  · change (coordinateHom s1).IsLowerTriangular
    rw [coordinates_s1]
    decide +kernel
  · change (coordinateHom s2).IsLowerTriangular
    rw [coordinates_s2]
    decide +kernel
  · change (coordinateHom s3).IsLowerTriangular
    rw [coordinates_s3]
    decide +kernel
  · change (coordinateHom s4).IsLowerTriangular
    rw [coordinates_s4]
    decide +kernel
  · change (coordinateHom s5).IsLowerTriangular
    rw [coordinates_s5]
    decide +kernel
theorem candidate_isPGroup : IsPGroup 2 candidate := by
  let B : Submonoid Group := (Matrix.blockTriangularSubsemiring (ZMod 2)
    (OrderDual.toDual : Fin 12 → (Fin 12)ᵒᵈ)).toSubmonoid.comap coordinateHom
  have hB : candidate.toSubmonoid ≤ B := by
    rw [candidate, Subgroup.closure_toSubmonoid_of_isOfFinOrder
      (fun g _ => isOfFinOrder_of_finite g)]
    apply Submonoid.closure_le.mpr
    rintro _ ⟨i, rfl⟩
    exact coordinates_lower i
  apply IsPGroup.of_injective_binary_lowerTriangular (coordinateHom.comp candidate.subtype)
    (coordinateHom_injective.comp Subtype.val_injective)
  intro g i j hij
  exact hB g.property hij

theorem group_card : Nat.card Group = 2661120 := by
  have hcard : Nat.card ActorCatalogue.Native.component = 1330560 := by
    exact (Nat.card_congr (subgroupOfEquivOfLe derivedGroup_le_actionGroup).toEquiv).trans
      M22TripleCover.card
  have h := ActorCatalogue.Native.component.card_mul_index
  rw [hcard, ActorCatalogue.Native.component_index] at h
  exact h.symm

end SylowCertificates
end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Mathieu.ModuleGeometry.Native
