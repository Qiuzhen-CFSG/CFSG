module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second
import Mathlib.Tactic.FinCases

/-!
# The representative alternatives at indices 30 through 39

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

private theorem r30_value : value (representative 30) = wordMatrix194 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix194_expansion.symm

private def obstruction30 : quotientSubgroup := (representative 30) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob30M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob30_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob30M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob30M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob30_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob30M2 = ob30M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob30M0 : QuotientMatrix := quotientDecode #v[2065, 3311, 2185, 658, 2974, 3594, 3735, 4005, 3991, 2493, 3865, 1057]

private theorem ob30_mul0 : quotientDecode #v[936, 2929, 1018, 1273, 2185, 1999, 2634, 1612, 2057, 2864, 732, 3330] * ob30M1 = ob30M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob30_value : value (obstruction30) = ob30M0 := by
  simp only [obstruction30, r30_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[936, 2929, 1018, 1273, 2185, 1999, 2634, 1612, 2057, 2864, 732, 3330] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob30_mul2, ob30_mul1, ob30_mul0]

private theorem obstruction30_mem : obstruction30 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 30)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 30)).mul_mem (representative_mem_join 30) ((baseSubgroup ⊔ Subgroup.zpowers (representative 30)).mul_mem (sylow_mem_join 30 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 30)).mul_mem (sylow_mem_join 30 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 30)).inv_mem (sylow_mem_join 30 2)))))

private def ob30Power2 : QuotientMatrix := quotientDecode #v[1966, 2789, 263, 361, 196, 3320, 2761, 3109, 1374, 909, 3087, 2306]

private theorem ob30_power2 : value (obstruction30 ^ 2) = ob30Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob30_value) (by rw [pow_one]; exact ob30_value)
  intro i
  fin_cases i <;> rfl

private def ob30Power3 : QuotientMatrix := quotientDecode #v[3688, 572, 992, 1417, 2491, 3340, 1581, 1450, 883, 2949, 1501, 1881]

private theorem ob30_power3 : value (obstruction30 ^ 3) = ob30Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob30_value) ob30_power2
  intro i
  fin_cases i <;> rfl

private def ob30Power4 : QuotientMatrix := quotientDecode #v[138, 1586, 2322, 1448, 2027, 3764, 2724, 3932, 2519, 3382, 2088, 1721]

private theorem ob30_power4 : value (obstruction30 ^ 4) = ob30Power4 := by
  apply power_step _ 2 2 _ _ _ ob30_power2 ob30_power2
  intro i
  fin_cases i <;> rfl

private def ob30Power7 : QuotientMatrix := quotientDecode #v[543, 2259, 4013, 2945, 2685, 3068, 1946, 909, 418, 1180, 4060, 1188]

private theorem ob30_power7 : value (obstruction30 ^ 7) = ob30Power7 := by
  apply power_step _ 3 4 _ _ _ ob30_power3 ob30_power4
  intro i
  fin_cases i <;> rfl

private def ob30Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob30_power14 : value (obstruction30 ^ 14) = ob30Power14 := by
  apply power_step _ 7 7 _ _ _ ob30_power7 ob30_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction30_small_power : (obstruction30 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction30 ^ 14) = 1
  rw [ob30_power14]
  exact decode_identity

private theorem obstruction30_nonidentity : obstruction30 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob30_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1966, 2789, 263, 361, 196, 3320, 2761, 3109, 1374, 909, 3087, 2306]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative30 :
    representative 30 ∈ involutionMatrixLineStabilizer ∨
    representative 30 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 30), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction30 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 30)).pow_mem obstruction30_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction30_small_power obstruction30_nonidentity

private theorem r31_value : value (representative 31) = wordMatrix199 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix199_expansion.symm

private def obstruction31 : quotientSubgroup := (representative 31) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob31M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob31_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob31M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob31M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob31_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob31M3 = ob31M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob31M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob31_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob31M2 = ob31M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob31M0 : QuotientMatrix := quotientDecode #v[1696, 2159, 285, 2934, 2288, 3057, 965, 3708, 2180, 647, 3823, 1855]

private theorem ob31_mul0 : quotientDecode #v[4054, 2565, 433, 451, 1035, 1512, 1644, 1138, 2627, 1560, 2088, 2191] * ob31M1 = ob31M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob31_value : value (obstruction31) = ob31M0 := by
  simp only [obstruction31, r31_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[4054, 2565, 433, 451, 1035, 1512, 1644, 1138, 2627, 1560, 2088, 2191] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob31_mul3, ob31_mul2, ob31_mul1, ob31_mul0]

private theorem obstruction31_mem : obstruction31 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 31)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 31)).mul_mem (representative_mem_join 31) ((baseSubgroup ⊔ Subgroup.zpowers (representative 31)).mul_mem (sylow_mem_join 31 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 31)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 31)).inv_mem (sylow_mem_join 31 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 31)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 31)).inv_mem (sylow_mem_join 31 2)) (sylow_mem_join 31 1)))))

private def ob31Power2 : QuotientMatrix := quotientDecode #v[2533, 2991, 3263, 1162, 2439, 1316, 7, 504, 2142, 809, 2491, 841]

private theorem ob31_power2 : value (obstruction31 ^ 2) = ob31Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob31_value) (by rw [pow_one]; exact ob31_value)
  intro i
  fin_cases i <;> rfl

private def ob31Power3 : QuotientMatrix := quotientDecode #v[3662, 3093, 9, 906, 3605, 3207, 4050, 3402, 3598, 3108, 1919, 1040]

private theorem ob31_power3 : value (obstruction31 ^ 3) = ob31Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob31_value) ob31_power2
  intro i
  fin_cases i <;> rfl

private def ob31Power4 : QuotientMatrix := quotientDecode #v[2710, 1693, 3542, 1894, 1050, 2174, 3829, 392, 2387, 828, 140, 1567]

private theorem ob31_power4 : value (obstruction31 ^ 4) = ob31Power4 := by
  apply power_step _ 2 2 _ _ _ ob31_power2 ob31_power2
  intro i
  fin_cases i <;> rfl

private def ob31Power7 : QuotientMatrix := quotientDecode #v[1911, 1481, 3568, 2588, 1781, 1734, 262, 206, 2434, 827, 3785, 1174]

private theorem ob31_power7 : value (obstruction31 ^ 7) = ob31Power7 := by
  apply power_step _ 3 4 _ _ _ ob31_power3 ob31_power4
  intro i
  fin_cases i <;> rfl

private def ob31Power8 : QuotientMatrix := quotientDecode #v[3066, 1540, 4076, 1827, 1389, 2211, 502, 4029, 2472, 3259, 2872, 273]

private theorem ob31_power8 : value (obstruction31 ^ 8) = ob31Power8 := by
  apply power_step _ 4 4 _ _ _ ob31_power4 ob31_power4
  intro i
  fin_cases i <;> rfl

private def ob31Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob31_power15 : value (obstruction31 ^ 15) = ob31Power15 := by
  apply power_step _ 7 8 _ _ _ ob31_power7 ob31_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction31_small_power : (obstruction31 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction31 ^ 15) = 1
  rw [ob31_power15]
  exact decode_identity

private theorem obstruction31_nonidentity : obstruction31 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob31_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3662, 3093, 9, 906, 3605, 3207, 4050, 3402, 3598, 3108, 1919, 1040]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative31 :
    representative 31 ∈ involutionMatrixLineStabilizer ∨
    representative 31 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 31), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction31 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 31)).pow_mem obstruction31_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction31_small_power obstruction31_nonidentity

private theorem r32_value : value (representative 32) = wordMatrix203 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix203_expansion.symm

private def obstruction32 : quotientSubgroup := (representative 32) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob32M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob32_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob32M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob32M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob32_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob32M3 = ob32M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob32M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob32_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob32M2 = ob32M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob32M0 : QuotientMatrix := quotientDecode #v[475, 3254, 2212, 193, 747, 3714, 3246, 478, 4029, 3309, 2509, 3282]

private theorem ob32_mul0 : quotientDecode #v[1247, 379, 1976, 1356, 629, 1730, 2910, 1564, 2153, 2298, 2113, 3846] * ob32M1 = ob32M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob32_value : value (obstruction32) = ob32M0 := by
  simp only [obstruction32, r32_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[1247, 379, 1976, 1356, 629, 1730, 2910, 1564, 2153, 2298, 2113, 3846] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob32_mul3, ob32_mul2, ob32_mul1, ob32_mul0]

private theorem obstruction32_mem : obstruction32 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 32)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 32)).mul_mem (representative_mem_join 32) ((baseSubgroup ⊔ Subgroup.zpowers (representative 32)).mul_mem (sylow_mem_join 32 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 32)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 32)).inv_mem (sylow_mem_join 32 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 32)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 32)).inv_mem (sylow_mem_join 32 2)) (sylow_mem_join 32 1)))))

private def ob32Power2 : QuotientMatrix := quotientDecode #v[3466, 3258, 2858, 3243, 691, 1178, 3728, 1269, 582, 3923, 1953, 1586]

private theorem ob32_power2 : value (obstruction32 ^ 2) = ob32Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob32_value) (by rw [pow_one]; exact ob32_value)
  intro i
  fin_cases i <;> rfl

private def ob32Power3 : QuotientMatrix := quotientDecode #v[1803, 1247, 3447, 2031, 3127, 1679, 2759, 427, 1105, 1383, 1050, 1535]

private theorem ob32_power3 : value (obstruction32 ^ 3) = ob32Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob32_value) ob32_power2
  intro i
  fin_cases i <;> rfl

private def ob32Power4 : QuotientMatrix := quotientDecode #v[1841, 862, 4012, 3175, 3263, 502, 2182, 3405, 1619, 405, 1873, 609]

private theorem ob32_power4 : value (obstruction32 ^ 4) = ob32Power4 := by
  apply power_step _ 2 2 _ _ _ ob32_power2 ob32_power2
  intro i
  fin_cases i <;> rfl

private def ob32Power7 : QuotientMatrix := quotientDecode #v[2207, 2433, 3439, 782, 954, 3117, 3580, 736, 1113, 945, 1239, 3620]

private theorem ob32_power7 : value (obstruction32 ^ 7) = ob32Power7 := by
  apply power_step _ 3 4 _ _ _ ob32_power3 ob32_power4
  intro i
  fin_cases i <;> rfl

private def ob32Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob32_power14 : value (obstruction32 ^ 14) = ob32Power14 := by
  apply power_step _ 7 7 _ _ _ ob32_power7 ob32_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction32_small_power : (obstruction32 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction32 ^ 14) = 1
  rw [ob32_power14]
  exact decode_identity

private theorem obstruction32_nonidentity : obstruction32 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob32_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3466, 3258, 2858, 3243, 691, 1178, 3728, 1269, 582, 3923, 1953, 1586]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative32 :
    representative 32 ∈ involutionMatrixLineStabilizer ∨
    representative 32 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 32), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction32 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 32)).pow_mem obstruction32_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction32_small_power obstruction32_nonidentity

private theorem r33_value : value (representative 33) = wordMatrix206 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix206_expansion.symm

private def obstruction33 : quotientSubgroup := (representative 33) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob33M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob33_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob33M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob33M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob33_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob33M3 = ob33M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob33M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob33_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob33M2 = ob33M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob33M0 : QuotientMatrix := quotientDecode #v[3709, 1856, 330, 2662, 258, 1753, 965, 3619, 1435, 1114, 4095, 1791]

private theorem ob33_mul0 : quotientDecode #v[3829, 1201, 2660, 2209, 2998, 2381, 1644, 1463, 2826, 1809, 330, 3603] * ob33M1 = ob33M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob33_value : value (obstruction33) = ob33M0 := by
  simp only [obstruction33, r33_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3829, 1201, 2660, 2209, 2998, 2381, 1644, 1463, 2826, 1809, 330, 3603] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob33_mul3, ob33_mul2, ob33_mul1, ob33_mul0]

private theorem obstruction33_mem : obstruction33 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 33)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 33)).mul_mem (representative_mem_join 33) ((baseSubgroup ⊔ Subgroup.zpowers (representative 33)).mul_mem (sylow_mem_join 33 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 33)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 33)).inv_mem (sylow_mem_join 33 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 33)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 33)).inv_mem (sylow_mem_join 33 2)) (sylow_mem_join 33 1)))))

private def ob33Power2 : QuotientMatrix := quotientDecode #v[3093, 3579, 2936, 435, 731, 858, 784, 702, 1566, 30, 237, 905]

private theorem ob33_power2 : value (obstruction33 ^ 2) = ob33Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob33_value) (by rw [pow_one]; exact ob33_value)
  intro i
  fin_cases i <;> rfl

private def ob33Power3 : QuotientMatrix := quotientDecode #v[1845, 1533, 2374, 1374, 3045, 3616, 195, 462, 1739, 3438, 3694, 3065]

private theorem ob33_power3 : value (obstruction33 ^ 3) = ob33Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob33_value) ob33_power2
  intro i
  fin_cases i <;> rfl

private def ob33Power5 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob33_power5 : value (obstruction33 ^ 5) = ob33Power5 := by
  apply power_step _ 2 3 _ _ _ ob33_power2 ob33_power3
  intro i
  fin_cases i <;> rfl

private theorem obstruction33_small_power : (obstruction33 ^ 1) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction33 ^ 5) = 1
  rw [ob33_power5]
  exact decode_identity

private theorem obstruction33_nonidentity : obstruction33 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob33_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[3709, 1856, 330, 2662, 258, 1753, 965, 3619, 1435, 1114, 4095, 1791]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative33 :
    representative 33 ∈ involutionMatrixLineStabilizer ∨
    representative 33 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 33), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction33 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 33)).pow_mem obstruction33_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction33_small_power obstruction33_nonidentity

private theorem r34_value : value (representative 34) = wordMatrix209 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix209_expansion.symm

private def obstruction34 : quotientSubgroup := (representative 34) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob34M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob34_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob34M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob34M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob34_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob34M2 = ob34M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob34M0 : QuotientMatrix := quotientDecode #v[1196, 434, 1501, 1782, 2601, 2042, 2256, 595, 1817, 381, 25, 3533]

private theorem ob34_mul0 : quotientDecode #v[3788, 3096, 4, 4089, 2374, 1274, 755, 1442, 1455, 1928, 2780, 2364] * ob34M1 = ob34M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob34_value : value (obstruction34) = ob34M0 := by
  simp only [obstruction34, r34_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[3788, 3096, 4, 4089, 2374, 1274, 755, 1442, 1455, 1928, 2780, 2364] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob34_mul2, ob34_mul1, ob34_mul0]

private theorem obstruction34_mem : obstruction34 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 34)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 34)).mul_mem (representative_mem_join 34) ((baseSubgroup ⊔ Subgroup.zpowers (representative 34)).mul_mem (sylow_mem_join 34 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 34)).mul_mem (sylow_mem_join 34 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 34)).inv_mem (sylow_mem_join 34 2)))))

private def ob34Power2 : QuotientMatrix := quotientDecode #v[1691, 2347, 45, 603, 2320, 1641, 3431, 1690, 3598, 1437, 2163, 1993]

private theorem ob34_power2 : value (obstruction34 ^ 2) = ob34Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob34_value) (by rw [pow_one]; exact ob34_value)
  intro i
  fin_cases i <;> rfl

private def ob34Power3 : QuotientMatrix := quotientDecode #v[2806, 3782, 125, 108, 253, 3092, 1316, 3674, 3632, 2301, 3536, 3748]

private theorem ob34_power3 : value (obstruction34 ^ 3) = ob34Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob34_value) ob34_power2
  intro i
  fin_cases i <;> rfl

private def ob34Power5 : QuotientMatrix := quotientDecode #v[4054, 2268, 1779, 2424, 105, 1671, 57, 1312, 1374, 1952, 857, 2809]

private theorem ob34_power5 : value (obstruction34 ^ 5) = ob34Power5 := by
  apply power_step _ 2 3 _ _ _ ob34_power2 ob34_power3
  intro i
  fin_cases i <;> rfl

private def ob34Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob34_power10 : value (obstruction34 ^ 10) = ob34Power10 := by
  apply power_step _ 5 5 _ _ _ ob34_power5 ob34_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction34_small_power : (obstruction34 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction34 ^ 10) = 1
  rw [ob34_power10]
  exact decode_identity

private theorem obstruction34_nonidentity : obstruction34 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob34_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[1691, 2347, 45, 603, 2320, 1641, 3431, 1690, 3598, 1437, 2163, 1993]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative34 :
    representative 34 ∈ involutionMatrixLineStabilizer ∨
    representative 34 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 34), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction34 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 34)).pow_mem obstruction34_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction34_small_power obstruction34_nonidentity

private theorem r35_value : value (representative 35) = wordMatrix213 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix213_expansion.symm

private def obstruction35 : quotientSubgroup := (representative 35) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob35M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob35_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob35M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob35M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob35_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob35M3 = ob35M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob35M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob35_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob35M2 = ob35M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob35M0 : QuotientMatrix := quotientDecode #v[829, 2479, 1479, 3819, 2487, 3692, 965, 2030, 278, 512, 2930, 1791]

private theorem ob35_mul0 : quotientDecode #v[3705, 3225, 681, 108, 1724, 1095, 1644, 3574, 967, 563, 2439, 3603] * ob35M1 = ob35M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob35_value : value (obstruction35) = ob35M0 := by
  simp only [obstruction35, r35_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3705, 3225, 681, 108, 1724, 1095, 1644, 3574, 967, 563, 2439, 3603] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob35_mul3, ob35_mul2, ob35_mul1, ob35_mul0]

private theorem obstruction35_mem : obstruction35 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 35)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 35)).mul_mem (representative_mem_join 35) ((baseSubgroup ⊔ Subgroup.zpowers (representative 35)).mul_mem (sylow_mem_join 35 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 35)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 35)).inv_mem (sylow_mem_join 35 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 35)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 35)).inv_mem (sylow_mem_join 35 2)) (sylow_mem_join 35 1)))))

private def ob35Power2 : QuotientMatrix := quotientDecode #v[3292, 4053, 282, 435, 2185, 2312, 455, 160, 1225, 512, 2136, 2876]

private theorem ob35_power2 : value (obstruction35 ^ 2) = ob35Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob35_value) (by rw [pow_one]; exact ob35_value)
  intro i
  fin_cases i <;> rfl

private def ob35Power3 : QuotientMatrix := quotientDecode #v[2877, 1533, 4069, 2993, 3271, 2306, 2664, 2434, 655, 512, 614, 2334]

private theorem ob35_power3 : value (obstruction35 ^ 3) = ob35Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob35_value) ob35_power2
  intro i
  fin_cases i <;> rfl

private def ob35Power5 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob35_power5 : value (obstruction35 ^ 5) = ob35Power5 := by
  apply power_step _ 2 3 _ _ _ ob35_power2 ob35_power3
  intro i
  fin_cases i <;> rfl

private theorem obstruction35_small_power : (obstruction35 ^ 1) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction35 ^ 5) = 1
  rw [ob35_power5]
  exact decode_identity

private theorem obstruction35_nonidentity : obstruction35 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob35_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[829, 2479, 1479, 3819, 2487, 3692, 965, 2030, 278, 512, 2930, 1791]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative35 :
    representative 35 ∈ involutionMatrixLineStabilizer ∨
    representative 35 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 35), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction35 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 35)).pow_mem obstruction35_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction35_small_power obstruction35_nonidentity

private theorem r36_value : value (representative 36) = wordMatrix216 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix216_expansion.symm

private def obstruction36 : quotientSubgroup := (representative 36) * ((sylowGenerator 3) * ((sylowGenerator 1) * ((sylowGenerator 3))))

private def ob36M2 : QuotientMatrix := quotientDecode #v[1315, 703, 679, 1669, 1324, 254, 3774, 2665, 1908, 3570, 1024, 1172]

private theorem ob36_mul2 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] = ob36M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob36M1 : QuotientMatrix := quotientDecode #v[2640, 3249, 33, 2031, 1751, 752, 1605, 2836, 754, 2147, 1047, 3303]

private theorem ob36_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob36M2 = ob36M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob36M0 : QuotientMatrix := quotientDecode #v[3886, 414, 1283, 2862, 1216, 797, 2674, 2836, 1828, 655, 3250, 1368]

private theorem ob36_mul0 : quotientDecode #v[1640, 379, 2208, 639, 2374, 3166, 3957, 128, 1478, 4041, 3954, 3102] * ob36M1 = ob36M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob36_value : value (obstruction36) = ob36M0 := by
  simp only [obstruction36, r36_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[1640, 379, 2208, 639, 2374, 3166, 3957, 128, 1478, 4041, 3954, 3102] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100]))) = _
  rw [ob36_mul2, ob36_mul1, ob36_mul0]

private theorem obstruction36_mem : obstruction36 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 36)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 36)).mul_mem (representative_mem_join 36) ((baseSubgroup ⊔ Subgroup.zpowers (representative 36)).mul_mem (sylow_mem_join 36 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 36)).mul_mem (sylow_mem_join 36 1) (sylow_mem_join 36 3))))

private def ob36Power2 : QuotientMatrix := quotientDecode #v[239, 1859, 1318, 3165, 3540, 104, 3046, 304, 3847, 2310, 1213, 3594]

private theorem ob36_power2 : value (obstruction36 ^ 2) = ob36Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob36_value) (by rw [pow_one]; exact ob36_value)
  intro i
  fin_cases i <;> rfl

private def ob36Power3 : QuotientMatrix := quotientDecode #v[742, 3547, 3094, 1627, 3691, 577, 1557, 249, 2034, 1761, 376, 469]

private theorem ob36_power3 : value (obstruction36 ^ 3) = ob36Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob36_value) ob36_power2
  intro i
  fin_cases i <;> rfl

private def ob36Power4 : QuotientMatrix := quotientDecode #v[1129, 3830, 2487, 1297, 1940, 2003, 208, 699, 3644, 872, 421, 2223]

private theorem ob36_power4 : value (obstruction36 ^ 4) = ob36Power4 := by
  apply power_step _ 2 2 _ _ _ ob36_power2 ob36_power2
  intro i
  fin_cases i <;> rfl

private def ob36Power7 : QuotientMatrix := quotientDecode #v[401, 3399, 2527, 2567, 751, 2001, 2183, 852, 43, 796, 3002, 1565]

private theorem ob36_power7 : value (obstruction36 ^ 7) = ob36Power7 := by
  apply power_step _ 3 4 _ _ _ ob36_power3 ob36_power4
  intro i
  fin_cases i <;> rfl

private def ob36Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob36_power14 : value (obstruction36 ^ 14) = ob36Power14 := by
  apply power_step _ 7 7 _ _ _ ob36_power7 ob36_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction36_small_power : (obstruction36 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction36 ^ 14) = 1
  rw [ob36_power14]
  exact decode_identity

private theorem obstruction36_nonidentity : obstruction36 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob36_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[239, 1859, 1318, 3165, 3540, 104, 3046, 304, 3847, 2310, 1213, 3594]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative36 :
    representative 36 ∈ involutionMatrixLineStabilizer ∨
    representative 36 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 36), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction36 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 36)).pow_mem obstruction36_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction36_small_power obstruction36_nonidentity

private theorem r37_value : value (representative 37) = wordMatrix218 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix218_expansion.symm

private def obstruction37 : quotientSubgroup := (representative 37) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 3) * ((sylowGenerator 1)))))

private def ob37M3 : QuotientMatrix := quotientDecode #v[1315, 3788, 3161, 658, 1953, 612, 2750, 3689, 2461, 795, 1024, 3312]

private theorem ob37_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob37M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob37M2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem ob37_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob37M3 = ob37M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob37M1 : QuotientMatrix := quotientDecode #v[2704, 1044, 1492, 2567, 2887, 649, 4053, 1033, 1232, 4003, 1047, 251]

private theorem ob37_mul1 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob37M2 = ob37M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob37M0 : QuotientMatrix := quotientDecode #v[697, 4061, 2794, 378, 2235, 1167, 839, 2361, 3298, 3354, 1510, 2081]

private theorem ob37_mul0 : quotientDecode #v[3577, 3664, 664, 3412, 2495, 210, 3706, 2281, 3126, 4089, 856, 1000] * ob37M1 = ob37M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob37_value : value (obstruction37) = ob37M0 := by
  simp only [obstruction37, r37_value, s1_inverse_value, s2_inverse_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[3577, 3664, 664, 3412, 2495, 210, 3706, 2281, 3126, 4089, 856, 1000] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob37_mul3, ob37_mul2, ob37_mul1, ob37_mul0]

private theorem obstruction37_mem : obstruction37 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 37)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 37)).mul_mem (representative_mem_join 37) ((baseSubgroup ⊔ Subgroup.zpowers (representative 37)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 37)).inv_mem (sylow_mem_join 37 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 37)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 37)).inv_mem (sylow_mem_join 37 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 37)).mul_mem (sylow_mem_join 37 3) (sylow_mem_join 37 1)))))

private def ob37Power2 : QuotientMatrix := quotientDecode #v[3028, 2003, 1389, 3382, 306, 2603, 1329, 2868, 3307, 1849, 706, 3607]

private theorem ob37_power2 : value (obstruction37 ^ 2) = ob37Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob37_value) (by rw [pow_one]; exact ob37_value)
  intro i
  fin_cases i <;> rfl

private def ob37Power3 : QuotientMatrix := quotientDecode #v[502, 3007, 2021, 2086, 3851, 3498, 1929, 3847, 3880, 3049, 2233, 4072]

private theorem ob37_power3 : value (obstruction37 ^ 3) = ob37Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob37_value) ob37_power2
  intro i
  fin_cases i <;> rfl

private def ob37Power5 : QuotientMatrix := quotientDecode #v[2889, 436, 903, 1666, 1590, 3012, 1222, 3693, 26, 1801, 2264, 3615]

private theorem ob37_power5 : value (obstruction37 ^ 5) = ob37Power5 := by
  apply power_step _ 2 3 _ _ _ ob37_power2 ob37_power3
  intro i
  fin_cases i <;> rfl

private def ob37Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob37_power10 : value (obstruction37 ^ 10) = ob37Power10 := by
  apply power_step _ 5 5 _ _ _ ob37_power5 ob37_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction37_small_power : (obstruction37 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction37 ^ 10) = 1
  rw [ob37_power10]
  exact decode_identity

private theorem obstruction37_nonidentity : obstruction37 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob37_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3028, 2003, 1389, 3382, 306, 2603, 1329, 2868, 3307, 1849, 706, 3607]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative37 :
    representative 37 ∈ involutionMatrixLineStabilizer ∨
    representative 37 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 37), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction37 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 37)).pow_mem obstruction37_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction37_small_power obstruction37_nonidentity

private theorem r38_value : value (representative 38) = wordMatrix222 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix222_expansion.symm

private def obstruction38 : quotientSubgroup := (representative 38) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob38M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob38_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob38M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob38M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob38_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob38M3 = ob38M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob38M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob38_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob38M2 = ob38M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob38M0 : QuotientMatrix := quotientDecode #v[3000, 1475, 1773, 647, 1337, 3204, 839, 1612, 218, 2497, 695, 2145]

private theorem ob38_mul0 : quotientDecode #v[3773, 2797, 3271, 1560, 25, 3668, 132, 4018, 1807, 2581, 3030, 2736] * ob38M1 = ob38M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob38_value : value (obstruction38) = ob38M0 := by
  simp only [obstruction38, r38_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3773, 2797, 3271, 1560, 25, 3668, 132, 4018, 1807, 2581, 3030, 2736] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob38_mul3, ob38_mul2, ob38_mul1, ob38_mul0]

private theorem obstruction38_mem : obstruction38 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 38)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 38)).mul_mem (representative_mem_join 38) ((baseSubgroup ⊔ Subgroup.zpowers (representative 38)).mul_mem (sylow_mem_join 38 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 38)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 38)).inv_mem (sylow_mem_join 38 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 38)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 38)).inv_mem (sylow_mem_join 38 2)) (sylow_mem_join 38 1)))))

private def ob38Power2 : QuotientMatrix := quotientDecode #v[3084, 2333, 3371, 1819, 751, 2679, 714, 3163, 1910, 1544, 3750, 3098]

private theorem ob38_power2 : value (obstruction38 ^ 2) = ob38Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob38_value) (by rw [pow_one]; exact ob38_value)
  intro i
  fin_cases i <;> rfl

private def ob38Power3 : QuotientMatrix := quotientDecode #v[3772, 592, 2676, 617, 2655, 972, 2958, 84, 632, 2545, 2801, 2219]

private theorem ob38_power3 : value (obstruction38 ^ 3) = ob38Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob38_value) ob38_power2
  intro i
  fin_cases i <;> rfl

private def ob38Power4 : QuotientMatrix := quotientDecode #v[2188, 4031, 3511, 3901, 3535, 2170, 1695, 147, 444, 4021, 1710, 3669]

private theorem ob38_power4 : value (obstruction38 ^ 4) = ob38Power4 := by
  apply power_step _ 2 2 _ _ _ ob38_power2 ob38_power2
  intro i
  fin_cases i <;> rfl

private def ob38Power7 : QuotientMatrix := quotientDecode #v[226, 1253, 3965, 1761, 3849, 2703, 3578, 1767, 930, 1244, 2773, 3762]

private theorem ob38_power7 : value (obstruction38 ^ 7) = ob38Power7 := by
  apply power_step _ 3 4 _ _ _ ob38_power3 ob38_power4
  intro i
  fin_cases i <;> rfl

private def ob38Power8 : QuotientMatrix := quotientDecode #v[3148, 1645, 1765, 2369, 2802, 3581, 510, 2671, 1552, 1775, 3271, 2341]

private theorem ob38_power8 : value (obstruction38 ^ 8) = ob38Power8 := by
  apply power_step _ 4 4 _ _ _ ob38_power4 ob38_power4
  intro i
  fin_cases i <;> rfl

private def ob38Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob38_power15 : value (obstruction38 ^ 15) = ob38Power15 := by
  apply power_step _ 7 8 _ _ _ ob38_power7 ob38_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction38_small_power : (obstruction38 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction38 ^ 15) = 1
  rw [ob38_power15]
  exact decode_identity

private theorem obstruction38_nonidentity : obstruction38 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob38_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3772, 592, 2676, 617, 2655, 972, 2958, 84, 632, 2545, 2801, 2219]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative38 :
    representative 38 ∈ involutionMatrixLineStabilizer ∨
    representative 38 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 38), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction38 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 38)).pow_mem obstruction38_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction38_small_power obstruction38_nonidentity

private theorem r39_value : value (representative 39) = wordMatrix226 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix226_expansion.symm

private def obstruction39 : quotientSubgroup := (representative 39) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 3) * ((sylowGenerator 1)))))

private def ob39M3 : QuotientMatrix := quotientDecode #v[1315, 3788, 3161, 658, 1953, 612, 2750, 3689, 2461, 795, 1024, 3312]

private theorem ob39_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob39M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob39M2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem ob39_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob39M3 = ob39M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob39M1 : QuotientMatrix := quotientDecode #v[2704, 1044, 1492, 2567, 2887, 649, 4053, 1033, 1232, 4003, 1047, 251]

private theorem ob39_mul1 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob39M2 = ob39M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob39M0 : QuotientMatrix := quotientDecode #v[1279, 2420, 1125, 1485, 1755, 1254, 279, 310, 2635, 494, 1510, 1673]

private theorem ob39_mul0 : quotientDecode #v[734, 3426, 2185, 3663, 4027, 3221, 4058, 600, 3844, 2399, 856, 1079] * ob39M1 = ob39M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob39_value : value (obstruction39) = ob39M0 := by
  simp only [obstruction39, r39_value, s1_inverse_value, s2_inverse_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[734, 3426, 2185, 3663, 4027, 3221, 4058, 600, 3844, 2399, 856, 1079] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob39_mul3, ob39_mul2, ob39_mul1, ob39_mul0]

private theorem obstruction39_mem : obstruction39 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 39)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 39)).mul_mem (representative_mem_join 39) ((baseSubgroup ⊔ Subgroup.zpowers (representative 39)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 39)).inv_mem (sylow_mem_join 39 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 39)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 39)).inv_mem (sylow_mem_join 39 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 39)).mul_mem (sylow_mem_join 39 3) (sylow_mem_join 39 1)))))

private def ob39Power2 : QuotientMatrix := quotientDecode #v[3033, 2957, 141, 2779, 2740, 3120, 1406, 1383, 3638, 1616, 1659, 1036]

private theorem ob39_power2 : value (obstruction39 ^ 2) = ob39Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob39_value) (by rw [pow_one]; exact ob39_value)
  intro i
  fin_cases i <;> rfl

private def ob39Power3 : QuotientMatrix := quotientDecode #v[2788, 2381, 1121, 2523, 9, 338, 1115, 946, 3501, 964, 3940, 1102]

private theorem ob39_power3 : value (obstruction39 ^ 3) = ob39Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob39_value) ob39_power2
  intro i
  fin_cases i <;> rfl

private def ob39Power4 : QuotientMatrix := quotientDecode #v[1989, 2178, 1256, 638, 306, 1267, 2668, 474, 2467, 4065, 2398, 3117]

private theorem ob39_power4 : value (obstruction39 ^ 4) = ob39Power4 := by
  apply power_step _ 2 2 _ _ _ ob39_power2 ob39_power2
  intro i
  fin_cases i <;> rfl

private def ob39Power7 : QuotientMatrix := quotientDecode #v[2145, 3761, 4, 563, 1467, 2687, 3897, 2779, 2218, 2332, 2374, 3366]

private theorem ob39_power7 : value (obstruction39 ^ 7) = ob39Power7 := by
  apply power_step _ 3 4 _ _ _ ob39_power3 ob39_power4
  intro i
  fin_cases i <;> rfl

private def ob39Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob39_power14 : value (obstruction39 ^ 14) = ob39Power14 := by
  apply power_step _ 7 7 _ _ _ ob39_power7 ob39_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction39_small_power : (obstruction39 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction39 ^ 14) = 1
  rw [ob39_power14]
  exact decode_identity

private theorem obstruction39_nonidentity : obstruction39 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob39_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 3) h
  have hn : (quotientDecode #v[3033, 2957, 141, 2779, 2740, 3120, 1406, 1383, 3638, 1616, 1659, 1036]) 0 3 ≠ (1 : QuotientMatrix) 0 3 := by decide +kernel
  exact hn hc

theorem alternative39 :
    representative 39 ∈ involutionMatrixLineStabilizer ∨
    representative 39 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 39), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction39 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 39)).pow_mem obstruction39_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction39_small_power obstruction39_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
