module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second
import Mathlib.Tactic.FinCases

/-!
# The representative alternatives at indices 20 through 29

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

private theorem r20_value : value (representative 20) = wordMatrix151 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix151_expansion.symm

private def obstruction20 : quotientSubgroup := (representative 20) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob20M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob20_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob20M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob20M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob20_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob20M2 = ob20M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob20M0 : QuotientMatrix := quotientDecode #v[19, 2049, 1295, 2257, 285, 687, 2837, 533, 1249, 2354, 1067, 1606]

private theorem ob20_mul0 : quotientDecode #v[1872, 3555, 1551, 2147, 4056, 2791, 3979, 2747, 1737, 2933, 142, 553] * ob20M1 = ob20M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob20_value : value (obstruction20) = ob20M0 := by
  simp only [obstruction20, r20_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[1872, 3555, 1551, 2147, 4056, 2791, 3979, 2747, 1737, 2933, 142, 553] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob20_mul2, ob20_mul1, ob20_mul0]

private theorem obstruction20_mem : obstruction20 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 20)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 20)).mul_mem (representative_mem_join 20) ((baseSubgroup ⊔ Subgroup.zpowers (representative 20)).mul_mem (sylow_mem_join 20 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 20)).mul_mem (sylow_mem_join 20 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 20)).inv_mem (sylow_mem_join 20 2)))))

private def ob20Power2 : QuotientMatrix := quotientDecode #v[2319, 1621, 1286, 3656, 2097, 3140, 3988, 3379, 3991, 2324, 1607, 2818]

private theorem ob20_power2 : value (obstruction20 ^ 2) = ob20Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob20_value) (by rw [pow_one]; exact ob20_value)
  intro i
  fin_cases i <;> rfl

private def ob20Power3 : QuotientMatrix := quotientDecode #v[1899, 525, 3524, 2203, 1511, 3191, 2489, 3372, 427, 1717, 2833, 916]

private theorem ob20_power3 : value (obstruction20 ^ 3) = ob20Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob20_value) ob20_power2
  intro i
  fin_cases i <;> rfl

private def ob20Power5 : QuotientMatrix := quotientDecode #v[518, 2901, 1395, 3858, 3439, 3320, 2708, 1496, 4082, 2588, 3263, 1671]

private theorem ob20_power5 : value (obstruction20 ^ 5) = ob20Power5 := by
  apply power_step _ 2 3 _ _ _ ob20_power2 ob20_power3
  intro i
  fin_cases i <;> rfl

private def ob20Power10 : QuotientMatrix := quotientDecode #v[1082, 999, 285, 2540, 148, 3057, 351, 3708, 2648, 2965, 3397, 3931]

private theorem ob20_power10 : value (obstruction20 ^ 10) = ob20Power10 := by
  apply power_step _ 5 5 _ _ _ ob20_power5 ob20_power5
  intro i
  fin_cases i <;> rfl

private def ob20Power6 : QuotientMatrix := quotientDecode #v[1084, 1153, 127, 1698, 2810, 14, 2419, 6, 3341, 951, 1542, 529]

private theorem ob20_power6 : value (obstruction20 ^ 6) = ob20Power6 := by
  apply power_step _ 3 3 _ _ _ ob20_power3 ob20_power3
  intro i
  fin_cases i <;> rfl

private def ob20Power11 : QuotientMatrix := quotientDecode #v[1865, 2913, 2097, 1238, 1543, 308, 2853, 3622, 3501, 3457, 2181, 1397]

private theorem ob20_power11 : value (obstruction20 ^ 11) = ob20Power11 := by
  apply power_step _ 5 6 _ _ _ ob20_power5 ob20_power6
  intro i
  fin_cases i <;> rfl

private def ob20Power21 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob20_power21 : value (obstruction20 ^ 21) = ob20Power21 := by
  apply power_step _ 10 11 _ _ _ ob20_power10 ob20_power11
  intro i
  fin_cases i <;> rfl

private theorem obstruction20_small_power : (obstruction20 ^ 3) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction20 ^ 21) = 1
  rw [ob20_power21]
  exact decode_identity

private theorem obstruction20_nonidentity : obstruction20 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob20_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[1899, 525, 3524, 2203, 1511, 3191, 2489, 3372, 427, 1717, 2833, 916]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative20 :
    representative 20 ∈ involutionMatrixLineStabilizer ∨
    representative 20 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 20), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction20 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 20)).pow_mem obstruction20_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction20_small_power obstruction20_nonidentity

private theorem r21_value : value (representative 21) = wordMatrix155 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix155_expansion.symm

private def obstruction21 : quotientSubgroup := (representative 21) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob21M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob21_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob21M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob21M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob21_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob21M2 = ob21M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob21M0 : QuotientMatrix := quotientDecode #v[1430, 561, 4062, 3163, 3030, 153, 132, 1699, 2285, 2310, 1626, 3173]

private theorem ob21_mul0 : quotientDecode #v[3277, 3705, 1867, 486, 3419, 2754, 1881, 1968, 3309, 508, 1314, 1763] * ob21M1 = ob21M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob21_value : value (obstruction21) = ob21M0 := by
  simp only [obstruction21, r21_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[3277, 3705, 1867, 486, 3419, 2754, 1881, 1968, 3309, 508, 1314, 1763] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob21_mul2, ob21_mul1, ob21_mul0]

private theorem obstruction21_mem : obstruction21 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 21)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 21)).mul_mem (representative_mem_join 21) ((baseSubgroup ⊔ Subgroup.zpowers (representative 21)).mul_mem (sylow_mem_join 21 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 21)).mul_mem (sylow_mem_join 21 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 21)).inv_mem (sylow_mem_join 21 2)))))

private def ob21Power2 : QuotientMatrix := quotientDecode #v[3629, 2015, 1937, 2705, 3472, 1208, 2429, 3777, 3272, 2407, 2660, 106]

private theorem ob21_power2 : value (obstruction21 ^ 2) = ob21Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob21_value) (by rw [pow_one]; exact ob21_value)
  intro i
  fin_cases i <;> rfl

private def ob21Power3 : QuotientMatrix := quotientDecode #v[1459, 3682, 3922, 3456, 4007, 2029, 2384, 136, 67, 3308, 2720, 3703]

private theorem ob21_power3 : value (obstruction21 ^ 3) = ob21Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob21_value) ob21_power2
  intro i
  fin_cases i <;> rfl

private def ob21Power5 : QuotientMatrix := quotientDecode #v[2231, 2419, 3219, 2055, 3003, 4066, 2127, 1104, 143, 1034, 884, 3423]

private theorem ob21_power5 : value (obstruction21 ^ 5) = ob21Power5 := by
  apply power_step _ 2 3 _ _ _ ob21_power2 ob21_power3
  intro i
  fin_cases i <;> rfl

private def ob21Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob21_power10 : value (obstruction21 ^ 10) = ob21Power10 := by
  apply power_step _ 5 5 _ _ _ ob21_power5 ob21_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction21_small_power : (obstruction21 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction21 ^ 10) = 1
  rw [ob21_power10]
  exact decode_identity

private theorem obstruction21_nonidentity : obstruction21 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob21_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[3629, 2015, 1937, 2705, 3472, 1208, 2429, 3777, 3272, 2407, 2660, 106]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative21 :
    representative 21 ∈ involutionMatrixLineStabilizer ∨
    representative 21 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 21), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction21 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 21)).pow_mem obstruction21_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction21_small_power obstruction21_nonidentity

private theorem r22_value : value (representative 22) = wordMatrix160 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix160_expansion.symm

private def obstruction22 : quotientSubgroup := (representative 22) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob22M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob22_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob22M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob22M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob22_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob22M3 = ob22M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob22M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob22_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob22M2 = ob22M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob22M0 : QuotientMatrix := quotientDecode #v[1530, 1350, 3344, 1952, 3587, 3411, 1776, 2438, 1672, 1518, 1525, 2494]

private theorem ob22_mul0 : quotientDecode #v[1972, 3111, 2939, 1665, 2124, 2271, 1057, 501, 2109, 4037, 3462, 1579] * ob22M1 = ob22M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob22_value : value (obstruction22) = ob22M0 := by
  simp only [obstruction22, r22_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[1972, 3111, 2939, 1665, 2124, 2271, 1057, 501, 2109, 4037, 3462, 1579] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob22_mul3, ob22_mul2, ob22_mul1, ob22_mul0]

private theorem obstruction22_mem : obstruction22 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 22)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 22)).mul_mem (representative_mem_join 22) ((baseSubgroup ⊔ Subgroup.zpowers (representative 22)).mul_mem (sylow_mem_join 22 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 22)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 22)).inv_mem (sylow_mem_join 22 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 22)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 22)).inv_mem (sylow_mem_join 22 2)) (sylow_mem_join 22 1)))))

private def ob22Power2 : QuotientMatrix := quotientDecode #v[3517, 3547, 1216, 582, 2329, 652, 3133, 3814, 3645, 3758, 1969, 2582]

private theorem ob22_power2 : value (obstruction22 ^ 2) = ob22Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob22_value) (by rw [pow_one]; exact ob22_value)
  intro i
  fin_cases i <;> rfl

private def ob22Power3 : QuotientMatrix := quotientDecode #v[3935, 3242, 2691, 2888, 879, 1752, 81, 982, 1471, 646, 2495, 2565]

private theorem ob22_power3 : value (obstruction22 ^ 3) = ob22Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob22_value) ob22_power2
  intro i
  fin_cases i <;> rfl

private def ob22Power5 : QuotientMatrix := quotientDecode #v[3824, 3664, 2616, 1278, 2242, 155, 2201, 586, 2591, 2387, 1976, 3525]

private theorem ob22_power5 : value (obstruction22 ^ 5) = ob22Power5 := by
  apply power_step _ 2 3 _ _ _ ob22_power2 ob22_power3
  intro i
  fin_cases i <;> rfl

private def ob22Power10 : QuotientMatrix := quotientDecode #v[420, 885, 2097, 1444, 2374, 3798, 3395, 2916, 562, 1825, 2585, 3705]

private theorem ob22_power10 : value (obstruction22 ^ 10) = ob22Power10 := by
  apply power_step _ 5 5 _ _ _ ob22_power5 ob22_power5
  intro i
  fin_cases i <;> rfl

private def ob22Power6 : QuotientMatrix := quotientDecode #v[1411, 342, 2208, 1573, 910, 153, 3169, 504, 2143, 1913, 3045, 3423]

private theorem ob22_power6 : value (obstruction22 ^ 6) = ob22Power6 := by
  apply power_step _ 3 3 _ _ _ ob22_power3 ob22_power3
  intro i
  fin_cases i <;> rfl

private def ob22Power11 : QuotientMatrix := quotientDecode #v[3917, 3628, 3860, 2744, 400, 134, 3215, 3179, 1016, 3642, 9, 3679]

private theorem ob22_power11 : value (obstruction22 ^ 11) = ob22Power11 := by
  apply power_step _ 5 6 _ _ _ ob22_power5 ob22_power6
  intro i
  fin_cases i <;> rfl

private def ob22Power21 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob22_power21 : value (obstruction22 ^ 21) = ob22Power21 := by
  apply power_step _ 10 11 _ _ _ ob22_power10 ob22_power11
  intro i
  fin_cases i <;> rfl

private theorem obstruction22_small_power : (obstruction22 ^ 3) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction22 ^ 21) = 1
  rw [ob22_power21]
  exact decode_identity

private theorem obstruction22_nonidentity : obstruction22 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob22_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[3935, 3242, 2691, 2888, 879, 1752, 81, 982, 1471, 646, 2495, 2565]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative22 :
    representative 22 ∈ involutionMatrixLineStabilizer ∨
    representative 22 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 22), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction22 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 22)).pow_mem obstruction22_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction22_small_power obstruction22_nonidentity

private theorem r23_value : value (representative 23) = wordMatrix164 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix164_expansion.symm

private def obstruction23 : quotientSubgroup := (representative 23) * ((sylowGenerator 3) * ((sylowGenerator 1) * ((sylowGenerator 3))))

private def ob23M2 : QuotientMatrix := quotientDecode #v[1315, 703, 679, 1669, 1324, 254, 3774, 2665, 1908, 3570, 1024, 1172]

private theorem ob23_mul2 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] = ob23M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob23M1 : QuotientMatrix := quotientDecode #v[2640, 3249, 33, 2031, 1751, 752, 1605, 2836, 754, 2147, 1047, 3303]

private theorem ob23_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob23M2 = ob23M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob23M0 : QuotientMatrix := quotientDecode #v[372, 288, 237, 2275, 2585, 1251, 939, 478, 1007, 931, 388, 1332]

private theorem ob23_mul0 : quotientDecode #v[1201, 3475, 4025, 2324, 4091, 2146, 1881, 1854, 1055, 182, 3536, 1763] * ob23M1 = ob23M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob23_value : value (obstruction23) = ob23M0 := by
  simp only [obstruction23, r23_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[1201, 3475, 4025, 2324, 4091, 2146, 1881, 1854, 1055, 182, 3536, 1763] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100]))) = _
  rw [ob23_mul2, ob23_mul1, ob23_mul0]

private theorem obstruction23_mem : obstruction23 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 23)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 23)).mul_mem (representative_mem_join 23) ((baseSubgroup ⊔ Subgroup.zpowers (representative 23)).mul_mem (sylow_mem_join 23 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 23)).mul_mem (sylow_mem_join 23 1) (sylow_mem_join 23 3))))

private def ob23Power2 : QuotientMatrix := quotientDecode #v[3667, 1804, 4076, 1014, 1305, 1862, 3526, 685, 3712, 1317, 732, 3196]

private theorem ob23_power2 : value (obstruction23 ^ 2) = ob23Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob23_value) (by rw [pow_one]; exact ob23_value)
  intro i
  fin_cases i <;> rfl

private def ob23Power3 : QuotientMatrix := quotientDecode #v[3829, 2502, 2660, 3342, 485, 942, 1255, 4068, 1741, 1809, 961, 495]

private theorem ob23_power3 : value (obstruction23 ^ 3) = ob23Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob23_value) ob23_power2
  intro i
  fin_cases i <;> rfl

private def ob23Power5 : QuotientMatrix := quotientDecode #v[1806, 1399, 3125, 2870, 1810, 1368, 3138, 708, 2779, 563, 2717, 1000]

private theorem ob23_power5 : value (obstruction23 ^ 5) = ob23Power5 := by
  apply power_step _ 2 3 _ _ _ ob23_power2 ob23_power3
  intro i
  fin_cases i <;> rfl

private def ob23Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob23_power10 : value (obstruction23 ^ 10) = ob23Power10 := by
  apply power_step _ 5 5 _ _ _ ob23_power5 ob23_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction23_small_power : (obstruction23 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction23 ^ 10) = 1
  rw [ob23_power10]
  exact decode_identity

private theorem obstruction23_nonidentity : obstruction23 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob23_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[3667, 1804, 4076, 1014, 1305, 1862, 3526, 685, 3712, 1317, 732, 3196]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative23 :
    representative 23 ∈ involutionMatrixLineStabilizer ∨
    representative 23 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 23), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction23 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 23)).pow_mem obstruction23_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction23_small_power obstruction23_nonidentity

private theorem r24_value : value (representative 24) = wordMatrix169 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix169_expansion.symm

private def obstruction24 : quotientSubgroup := (representative 24) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob24M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob24_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob24M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob24M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob24_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob24M3 = ob24M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob24M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob24_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob24M2 = ob24M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob24M0 : QuotientMatrix := quotientDecode #v[3215, 3977, 1125, 298, 3587, 1062, 122, 1657, 3351, 222, 3536, 1601]

private theorem ob24_mul0 : quotientDecode #v[3106, 3555, 237, 3165, 2124, 841, 3837, 191, 2905, 3915, 1200, 1889] * ob24M1 = ob24M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob24_value : value (obstruction24) = ob24M0 := by
  simp only [obstruction24, r24_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3106, 3555, 237, 3165, 2124, 841, 3837, 191, 2905, 3915, 1200, 1889] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob24_mul3, ob24_mul2, ob24_mul1, ob24_mul0]

private theorem obstruction24_mem : obstruction24 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 24)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 24)).mul_mem (representative_mem_join 24) ((baseSubgroup ⊔ Subgroup.zpowers (representative 24)).mul_mem (sylow_mem_join 24 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 24)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 24)).inv_mem (sylow_mem_join 24 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 24)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 24)).inv_mem (sylow_mem_join 24 2)) (sylow_mem_join 24 1)))))

private def ob24Power2 : QuotientMatrix := quotientDecode #v[2977, 3460, 358, 1938, 2121, 538, 1276, 2804, 4070, 710, 3718, 507]

private theorem ob24_power2 : value (obstruction24 ^ 2) = ob24Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob24_value) (by rw [pow_one]; exact ob24_value)
  intro i
  fin_cases i <;> rfl

private def ob24Power3 : QuotientMatrix := quotientDecode #v[1368, 1178, 679, 2026, 2974, 126, 1209, 3804, 3985, 3377, 1754, 797]

private theorem ob24_power3 : value (obstruction24 ^ 3) = ob24Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob24_value) ob24_power2
  intro i
  fin_cases i <;> rfl

private def ob24Power4 : QuotientMatrix := quotientDecode #v[3988, 2825, 1506, 3231, 2356, 153, 3113, 1536, 685, 44, 2989, 2570]

private theorem ob24_power4 : value (obstruction24 ^ 4) = ob24Power4 := by
  apply power_step _ 2 2 _ _ _ ob24_power2 ob24_power2
  intro i
  fin_cases i <;> rfl

private def ob24Power7 : QuotientMatrix := quotientDecode #v[130, 783, 1994, 1034, 1483, 2032, 1803, 3051, 902, 1331, 3850, 3420]

private theorem ob24_power7 : value (obstruction24 ^ 7) = ob24Power7 := by
  apply power_step _ 3 4 _ _ _ ob24_power3 ob24_power4
  intro i
  fin_cases i <;> rfl

private def ob24Power8 : QuotientMatrix := quotientDecode #v[2544, 2944, 2233, 883, 1256, 3135, 565, 2945, 92, 2532, 2299, 3504]

private theorem ob24_power8 : value (obstruction24 ^ 8) = ob24Power8 := by
  apply power_step _ 4 4 _ _ _ ob24_power4 ob24_power4
  intro i
  fin_cases i <;> rfl

private def ob24Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob24_power15 : value (obstruction24 ^ 15) = ob24Power15 := by
  apply power_step _ 7 8 _ _ _ ob24_power7 ob24_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction24_small_power : (obstruction24 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction24 ^ 15) = 1
  rw [ob24_power15]
  exact decode_identity

private theorem obstruction24_nonidentity : obstruction24 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob24_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1368, 1178, 679, 2026, 2974, 126, 1209, 3804, 3985, 3377, 1754, 797]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative24 :
    representative 24 ∈ involutionMatrixLineStabilizer ∨
    representative 24 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 24), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction24 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 24)).pow_mem obstruction24_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction24_small_power obstruction24_nonidentity

private theorem r25_value : value (representative 25) = wordMatrix173 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix173_expansion.symm

private def obstruction25 : quotientSubgroup := (representative 25) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob25M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob25_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob25M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob25M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob25_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob25M3 = ob25M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob25M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob25_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob25M2 = ob25M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob25M0 : QuotientMatrix := quotientDecode #v[3999, 29, 845, 838, 743, 3633, 1010, 1612, 3083, 298, 1815, 175]

private theorem ob25_mul0 : quotientDecode #v[1907, 2278, 2165, 2563, 33, 1891, 2944, 4018, 111, 3165, 3940, 960] * ob25M1 = ob25M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob25_value : value (obstruction25) = ob25M0 := by
  simp only [obstruction25, r25_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[1907, 2278, 2165, 2563, 33, 1891, 2944, 4018, 111, 3165, 3940, 960] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob25_mul3, ob25_mul2, ob25_mul1, ob25_mul0]

private theorem obstruction25_mem : obstruction25 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 25)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 25)).mul_mem (representative_mem_join 25) ((baseSubgroup ⊔ Subgroup.zpowers (representative 25)).mul_mem (sylow_mem_join 25 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 25)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 25)).inv_mem (sylow_mem_join 25 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 25)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 25)).inv_mem (sylow_mem_join 25 2)) (sylow_mem_join 25 1)))))

private def ob25Power2 : QuotientMatrix := quotientDecode #v[443, 3443, 327, 3459, 1642, 1499, 1108, 1476, 2940, 353, 1054, 2036]

private theorem ob25_power2 : value (obstruction25 ^ 2) = ob25Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob25_value) (by rw [pow_one]; exact ob25_value)
  intro i
  fin_cases i <;> rfl

private def ob25Power3 : QuotientMatrix := quotientDecode #v[2645, 2837, 822, 637, 2213, 129, 1359, 3567, 673, 3671, 1510, 19]

private theorem ob25_power3 : value (obstruction25 ^ 3) = ob25Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob25_value) ob25_power2
  intro i
  fin_cases i <;> rfl

private def ob25Power4 : QuotientMatrix := quotientDecode #v[3138, 955, 679, 410, 1024, 2515, 1895, 4021, 1736, 2888, 963, 3429]

private theorem ob25_power4 : value (obstruction25 ^ 4) = ob25Power4 := by
  apply power_step _ 2 2 _ _ _ ob25_power2 ob25_power2
  intro i
  fin_cases i <;> rfl

private def ob25Power8 : QuotientMatrix := quotientDecode #v[2682, 389, 112, 3932, 963, 2182, 3497, 4005, 451, 1560, 2731, 2111]

private theorem ob25_power8 : value (obstruction25 ^ 8) = ob25Power8 := by
  apply power_step _ 4 4 _ _ _ ob25_power4 ob25_power4
  intro i
  fin_cases i <;> rfl

private def ob25Power16 : QuotientMatrix := quotientDecode #v[1554, 1132, 1772, 1033, 3624, 1647, 338, 2150, 2096, 44, 3495, 1961]

private theorem ob25_power16 : value (obstruction25 ^ 16) = ob25Power16 := by
  apply power_step _ 8 8 _ _ _ ob25_power8 ob25_power8
  intro i
  fin_cases i <;> rfl

private def ob25Power5 : QuotientMatrix := quotientDecode #v[1111, 2943, 1432, 3067, 1815, 1151, 2874, 3281, 197, 3386, 1821, 2722]

private theorem ob25_power5 : value (obstruction25 ^ 5) = ob25Power5 := by
  apply power_step _ 2 3 _ _ _ ob25_power2 ob25_power3
  intro i
  fin_cases i <;> rfl

private def ob25Power9 : QuotientMatrix := quotientDecode #v[3578, 1685, 3876, 2951, 1821, 1459, 3863, 3638, 1591, 1948, 1340, 1008]

private theorem ob25_power9 : value (obstruction25 ^ 9) = ob25Power9 := by
  apply power_step _ 4 5 _ _ _ ob25_power4 ob25_power5
  intro i
  fin_cases i <;> rfl

private def ob25Power17 : QuotientMatrix := quotientDecode #v[1223, 2783, 3513, 3022, 3045, 1143, 3331, 3644, 3193, 3642, 3841, 3730]

private theorem ob25_power17 : value (obstruction25 ^ 17) = ob25Power17 := by
  apply power_step _ 8 9 _ _ _ ob25_power8 ob25_power9
  intro i
  fin_cases i <;> rfl

private def ob25Power33 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob25_power33 : value (obstruction25 ^ 33) = ob25Power33 := by
  apply power_step _ 16 17 _ _ _ ob25_power16 ob25_power17
  intro i
  fin_cases i <;> rfl

private theorem obstruction25_small_power : (obstruction25 ^ 3) ^ 11 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction25 ^ 33) = 1
  rw [ob25_power33]
  exact decode_identity

private theorem obstruction25_nonidentity : obstruction25 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob25_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[2645, 2837, 822, 637, 2213, 129, 1359, 3567, 673, 3671, 1510, 19]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative25 :
    representative 25 ∈ involutionMatrixLineStabilizer ∨
    representative 25 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 25), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction25 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 25)).pow_mem obstruction25_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 11 (by decide +kernel)
    obstruction25_small_power obstruction25_nonidentity

private theorem r26_value : value (representative 26) = wordMatrix177 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix177_expansion.symm

private def obstruction26 : quotientSubgroup := (representative 26) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob26M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob26_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob26M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob26M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob26_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob26M3 = ob26M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob26M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob26_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob26M2 = ob26M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob26M0 : QuotientMatrix := quotientDecode #v[2350, 979, 1182, 3630, 75, 2871, 3166, 2084, 1448, 3597, 2367, 3416]

private theorem ob26_mul0 : quotientDecode #v[535, 3324, 158, 3428, 2484, 134, 2395, 945, 3746, 2297, 2213, 2729] * ob26M1 = ob26M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob26_value : value (obstruction26) = ob26M0 := by
  simp only [obstruction26, r26_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[535, 3324, 158, 3428, 2484, 134, 2395, 945, 3746, 2297, 2213, 2729] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob26_mul3, ob26_mul2, ob26_mul1, ob26_mul0]

private theorem obstruction26_mem : obstruction26 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 26)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 26)).mul_mem (representative_mem_join 26) ((baseSubgroup ⊔ Subgroup.zpowers (representative 26)).mul_mem (sylow_mem_join 26 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 26)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 26)).inv_mem (sylow_mem_join 26 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 26)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 26)).inv_mem (sylow_mem_join 26 2)) (sylow_mem_join 26 1)))))

private def ob26Power2 : QuotientMatrix := quotientDecode #v[2724, 1385, 2099, 2110, 2189, 994, 273, 753, 426, 2548, 961, 1012]

private theorem ob26_power2 : value (obstruction26 ^ 2) = ob26Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob26_value) (by rw [pow_one]; exact ob26_value)
  intro i
  fin_cases i <;> rfl

private def ob26Power3 : QuotientMatrix := quotientDecode #v[1240, 3326, 3289, 3911, 1762, 1851, 3277, 2085, 2886, 872, 1777, 61]

private theorem ob26_power3 : value (obstruction26 ^ 3) = ob26Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob26_value) ob26_power2
  intro i
  fin_cases i <;> rfl

private def ob26Power5 : QuotientMatrix := quotientDecode #v[146, 3550, 2498, 3716, 3934, 1795, 2428, 641, 2017, 659, 2078, 454]

private theorem ob26_power5 : value (obstruction26 ^ 5) = ob26Power5 := by
  apply power_step _ 2 3 _ _ _ ob26_power2 ob26_power3
  intro i
  fin_cases i <;> rfl

private def ob26Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob26_power10 : value (obstruction26 ^ 10) = ob26Power10 := by
  apply power_step _ 5 5 _ _ _ ob26_power5 ob26_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction26_small_power : (obstruction26 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction26 ^ 10) = 1
  rw [ob26_power10]
  exact decode_identity

private theorem obstruction26_nonidentity : obstruction26 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob26_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[2724, 1385, 2099, 2110, 2189, 994, 273, 753, 426, 2548, 961, 1012]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative26 :
    representative 26 ∈ involutionMatrixLineStabilizer ∨
    representative 26 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 26), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction26 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 26)).pow_mem obstruction26_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction26_small_power obstruction26_nonidentity

private theorem r27_value : value (representative 27) = wordMatrix181 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix181_expansion.symm

private def obstruction27 : quotientSubgroup := (representative 27) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob27M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob27_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob27M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob27M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob27_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob27M2 = ob27M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob27M0 : QuotientMatrix := quotientDecode #v[3486, 3883, 3134, 3427, 2590, 2327, 109, 1373, 26, 118, 2998, 2822]

private theorem ob27_mul0 : quotientDecode #v[1465, 3225, 1121, 108, 2772, 1319, 2944, 26, 967, 727, 1291, 2267] * ob27M1 = ob27M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob27_value : value (obstruction27) = ob27M0 := by
  simp only [obstruction27, r27_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[1465, 3225, 1121, 108, 2772, 1319, 2944, 26, 967, 727, 1291, 2267] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob27_mul2, ob27_mul1, ob27_mul0]

private theorem obstruction27_mem : obstruction27 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 27)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 27)).mul_mem (representative_mem_join 27) ((baseSubgroup ⊔ Subgroup.zpowers (representative 27)).mul_mem (sylow_mem_join 27 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 27)).mul_mem (sylow_mem_join 27 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 27)).inv_mem (sylow_mem_join 27 2)))))

private def ob27Power2 : QuotientMatrix := quotientDecode #v[415, 1565, 3535, 2917, 3864, 3977, 1465, 3356, 2134, 113, 3627, 2175]

private theorem ob27_power2 : value (obstruction27 ^ 2) = ob27Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob27_value) (by rw [pow_one]; exact ob27_value)
  intro i
  fin_cases i <;> rfl

private def ob27Power3 : QuotientMatrix := quotientDecode #v[3249, 3357, 1650, 944, 1953, 1404, 3333, 3049, 608, 3834, 1543, 2954]

private theorem ob27_power3 : value (obstruction27 ^ 3) = ob27Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob27_value) ob27_power2
  intro i
  fin_cases i <;> rfl

private def ob27Power4 : QuotientMatrix := quotientDecode #v[2938, 1655, 1935, 1592, 2574, 2453, 266, 1968, 2316, 1207, 1355, 3199]

private theorem ob27_power4 : value (obstruction27 ^ 4) = ob27Power4 := by
  apply power_step _ 2 2 _ _ _ ob27_power2 ob27_power2
  intro i
  fin_cases i <;> rfl

private def ob27Power7 : QuotientMatrix := quotientDecode #v[1637, 251, 1306, 2448, 3503, 3937, 3277, 937, 3112, 2285, 2942, 1595]

private theorem ob27_power7 : value (obstruction27 ^ 7) = ob27Power7 := by
  apply power_step _ 3 4 _ _ _ ob27_power3 ob27_power4
  intro i
  fin_cases i <;> rfl

private def ob27Power8 : QuotientMatrix := quotientDecode #v[794, 2543, 1018, 1119, 3848, 1080, 2371, 3291, 1220, 3042, 1656, 1823]

private theorem ob27_power8 : value (obstruction27 ^ 8) = ob27Power8 := by
  apply power_step _ 4 4 _ _ _ ob27_power4 ob27_power4
  intro i
  fin_cases i <;> rfl

private def ob27Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob27_power15 : value (obstruction27 ^ 15) = ob27Power15 := by
  apply power_step _ 7 8 _ _ _ ob27_power7 ob27_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction27_small_power : (obstruction27 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction27 ^ 15) = 1
  rw [ob27_power15]
  exact decode_identity

private theorem obstruction27_nonidentity : obstruction27 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob27_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 4) h
  have hn : (quotientDecode #v[3249, 3357, 1650, 944, 1953, 1404, 3333, 3049, 608, 3834, 1543, 2954]) 0 4 ≠ (1 : QuotientMatrix) 0 4 := by decide +kernel
  exact hn hc

theorem alternative27 :
    representative 27 ∈ involutionMatrixLineStabilizer ∨
    representative 27 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 27), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction27 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 27)).pow_mem obstruction27_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction27_small_power obstruction27_nonidentity

private theorem r28_value : value (representative 28) = wordMatrix185 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix185_expansion.symm

private def obstruction28 : quotientSubgroup := (representative 28) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 3) * ((sylowGenerator 1)))))

private def ob28M3 : QuotientMatrix := quotientDecode #v[1315, 3788, 3161, 658, 1953, 612, 2750, 3689, 2461, 795, 1024, 3312]

private theorem ob28_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob28M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob28M2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem ob28_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob28M3 = ob28M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob28M1 : QuotientMatrix := quotientDecode #v[2704, 1044, 1492, 2567, 2887, 649, 4053, 1033, 1232, 4003, 1047, 251]

private theorem ob28_mul1 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob28M2 = ob28M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob28M0 : QuotientMatrix := quotientDecode #v[1379, 3111, 2329, 3510, 3891, 3001, 1684, 1117, 180, 397, 2858, 726]

private theorem ob28_mul0 : quotientDecode #v[1800, 1971, 4076, 2107, 2242, 3166, 1205, 2880, 782, 1421, 670, 498] * ob28M1 = ob28M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob28_value : value (obstruction28) = ob28M0 := by
  simp only [obstruction28, r28_value, s1_inverse_value, s2_inverse_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[1800, 1971, 4076, 2107, 2242, 3166, 1205, 2880, 782, 1421, 670, 498] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob28_mul3, ob28_mul2, ob28_mul1, ob28_mul0]

private theorem obstruction28_mem : obstruction28 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 28)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 28)).mul_mem (representative_mem_join 28) ((baseSubgroup ⊔ Subgroup.zpowers (representative 28)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 28)).inv_mem (sylow_mem_join 28 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 28)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 28)).inv_mem (sylow_mem_join 28 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 28)).mul_mem (sylow_mem_join 28 3) (sylow_mem_join 28 1)))))

private def ob28Power2 : QuotientMatrix := quotientDecode #v[4087, 536, 1412, 3233, 1291, 3053, 2256, 833, 2510, 1317, 2503, 2377]

private theorem ob28_power2 : value (obstruction28 ^ 2) = ob28Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob28_value) (by rw [pow_one]; exact ob28_value)
  intro i
  fin_cases i <;> rfl

private def ob28Power3 : QuotientMatrix := quotientDecode #v[3803, 776, 1754, 891, 3948, 2899, 3884, 718, 2083, 3165, 246, 3107]

private theorem ob28_power3 : value (obstruction28 ^ 3) = ob28Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob28_value) ob28_power2
  intro i
  fin_cases i <;> rfl

private def ob28Power4 : QuotientMatrix := quotientDecode #v[377, 3215, 1740, 2005, 327, 780, 2003, 3020, 43, 407, 893, 2817]

private theorem ob28_power4 : value (obstruction28 ^ 4) = ob28Power4 := by
  apply power_step _ 2 2 _ _ _ ob28_power2 ob28_power2
  intro i
  fin_cases i <;> rfl

private def ob28Power7 : QuotientMatrix := quotientDecode #v[3728, 1641, 1256, 3591, 3078, 479, 3029, 30, 1531, 3720, 1047, 1670]

private theorem ob28_power7 : value (obstruction28 ^ 7) = ob28Power7 := by
  apply power_step _ 3 4 _ _ _ ob28_power3 ob28_power4
  intro i
  fin_cases i <;> rfl

private def ob28Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob28_power14 : value (obstruction28 ^ 14) = ob28Power14 := by
  apply power_step _ 7 7 _ _ _ ob28_power7 ob28_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction28_small_power : (obstruction28 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction28 ^ 14) = 1
  rw [ob28_power14]
  exact decode_identity

private theorem obstruction28_nonidentity : obstruction28 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob28_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[4087, 536, 1412, 3233, 1291, 3053, 2256, 833, 2510, 1317, 2503, 2377]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative28 :
    representative 28 ∈ involutionMatrixLineStabilizer ∨
    representative 28 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 28), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction28 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 28)).pow_mem obstruction28_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction28_small_power obstruction28_nonidentity

private theorem r29_value : value (representative 29) = wordMatrix189 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix189_expansion.symm

private def obstruction29 : quotientSubgroup := (representative 29) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob29M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob29_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob29M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob29M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob29_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob29M2 = ob29M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob29M0 : QuotientMatrix := quotientDecode #v[1452, 3486, 3003, 186, 1120, 1281, 1326, 1938, 3814, 3261, 3865, 1272]

private theorem ob29_mul0 : quotientDecode #v[3215, 1465, 1755, 92, 3143, 3268, 3866, 685, 1729, 3428, 732, 3093] * ob29M1 = ob29M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob29_value : value (obstruction29) = ob29M0 := by
  simp only [obstruction29, r29_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[3215, 1465, 1755, 92, 3143, 3268, 3866, 685, 1729, 3428, 732, 3093] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob29_mul2, ob29_mul1, ob29_mul0]

private theorem obstruction29_mem : obstruction29 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 29)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 29)).mul_mem (representative_mem_join 29) ((baseSubgroup ⊔ Subgroup.zpowers (representative 29)).mul_mem (sylow_mem_join 29 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 29)).mul_mem (sylow_mem_join 29 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 29)).inv_mem (sylow_mem_join 29 2)))))

private def ob29Power2 : QuotientMatrix := quotientDecode #v[2157, 106, 2264, 3031, 3894, 1107, 609, 814, 1732, 959, 2252, 3198]

private theorem ob29_power2 : value (obstruction29 ^ 2) = ob29Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob29_value) (by rw [pow_one]; exact ob29_value)
  intro i
  fin_cases i <;> rfl

private def ob29Power3 : QuotientMatrix := quotientDecode #v[2682, 3339, 670, 1014, 3838, 1637, 2366, 453, 2723, 1947, 3397, 2353]

private theorem ob29_power3 : value (obstruction29 ^ 3) = ob29Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob29_value) ob29_power2
  intro i
  fin_cases i <;> rfl

private def ob29Power4 : QuotientMatrix := quotientDecode #v[302, 3471, 2512, 1955, 542, 3484, 3552, 589, 740, 1592, 3646, 3795]

private theorem ob29_power4 : value (obstruction29 ^ 4) = ob29Power4 := by
  apply power_step _ 2 2 _ _ _ ob29_power2 ob29_power2
  intro i
  fin_cases i <;> rfl

private def ob29Power7 : QuotientMatrix := quotientDecode #v[165, 2315, 1431, 172, 1286, 132, 73, 1463, 2971, 435, 1815, 667]

private theorem ob29_power7 : value (obstruction29 ^ 7) = ob29Power7 := by
  apply power_step _ 3 4 _ _ _ ob29_power3 ob29_power4
  intro i
  fin_cases i <;> rfl

private def ob29Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob29_power14 : value (obstruction29 ^ 14) = ob29Power14 := by
  apply power_step _ 7 7 _ _ _ ob29_power7 ob29_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction29_small_power : (obstruction29 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction29 ^ 14) = 1
  rw [ob29_power14]
  exact decode_identity

private theorem obstruction29_nonidentity : obstruction29 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob29_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[2157, 106, 2264, 3031, 3894, 1107, 609, 814, 1732, 959, 2252, 3198]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative29 :
    representative 29 ∈ involutionMatrixLineStabilizer ∨
    representative 29 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 29), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction29 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 29)).pow_mem obstruction29_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction29_small_power obstruction29_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
