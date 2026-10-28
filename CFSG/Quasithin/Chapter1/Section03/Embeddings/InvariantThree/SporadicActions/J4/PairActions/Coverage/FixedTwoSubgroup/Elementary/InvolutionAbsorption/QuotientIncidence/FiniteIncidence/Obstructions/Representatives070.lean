module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second
import Mathlib.Tactic.FinCases

/-!
# The representative alternatives at indices 70 through 79

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

private theorem r70_value : value (representative 70) = wordMatrix345 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix345_expansion.symm

private def obstruction70 : quotientSubgroup := (representative 70) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob70M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob70_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob70M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob70M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob70_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob70M3 = ob70M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob70M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob70_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob70M2 = ob70M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob70M0 : QuotientMatrix := quotientDecode #v[703, 2127, 3868, 2497, 910, 3506, 139, 1163, 3599, 3980, 158, 89]

private theorem ob70_mul0 : quotientDecode #v[454, 2046, 2844, 2581, 4056, 104, 1663, 616, 2584, 3872, 1161, 2912] * ob70M1 = ob70M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob70_value : value (obstruction70) = ob70M0 := by
  simp only [obstruction70, r70_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[454, 2046, 2844, 2581, 4056, 104, 1663, 616, 2584, 3872, 1161, 2912] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob70_mul3, ob70_mul2, ob70_mul1, ob70_mul0]

private theorem obstruction70_mem : obstruction70 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 70)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 70)).mul_mem (representative_mem_join 70) ((baseSubgroup ⊔ Subgroup.zpowers (representative 70)).mul_mem (sylow_mem_join 70 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 70)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 70)).inv_mem (sylow_mem_join 70 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 70)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 70)).inv_mem (sylow_mem_join 70 2)) (sylow_mem_join 70 1)))))

private def ob70Power2 : QuotientMatrix := quotientDecode #v[2326, 3327, 1047, 2281, 2970, 3120, 1978, 1828, 870, 786, 2455, 2171]

private theorem ob70_power2 : value (obstruction70 ^ 2) = ob70Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob70_value) (by rw [pow_one]; exact ob70_value)
  intro i
  fin_cases i <;> rfl

private def ob70Power3 : QuotientMatrix := quotientDecode #v[2699, 1750, 1788, 661, 1873, 3835, 2596, 947, 3049, 2626, 3263, 3551]

private theorem ob70_power3 : value (obstruction70 ^ 3) = ob70Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob70_value) ob70_power2
  intro i
  fin_cases i <;> rfl

private def ob70Power4 : QuotientMatrix := quotientDecode #v[2159, 4047, 1011, 1322, 167, 1606, 3451, 452, 790, 1809, 1629, 1387]

private theorem ob70_power4 : value (obstruction70 ^ 4) = ob70Power4 := by
  apply power_step _ 2 2 _ _ _ ob70_power2 ob70_power2
  intro i
  fin_cases i <;> rfl

private def ob70Power7 : QuotientMatrix := quotientDecode #v[308, 360, 3531, 3566, 2025, 3315, 1999, 1154, 1744, 206, 1386, 3393]

private theorem ob70_power7 : value (obstruction70 ^ 7) = ob70Power7 := by
  apply power_step _ 3 4 _ _ _ ob70_power3 ob70_power4
  intro i
  fin_cases i <;> rfl

private def ob70Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob70_power14 : value (obstruction70 ^ 14) = ob70Power14 := by
  apply power_step _ 7 7 _ _ _ ob70_power7 ob70_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction70_small_power : (obstruction70 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction70 ^ 14) = 1
  rw [ob70_power14]
  exact decode_identity

private theorem obstruction70_nonidentity : obstruction70 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob70_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[2326, 3327, 1047, 2281, 2970, 3120, 1978, 1828, 870, 786, 2455, 2171]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative70 :
    representative 70 ∈ involutionMatrixLineStabilizer ∨
    representative 70 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 70), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction70 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 70)).pow_mem obstruction70_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction70_small_power obstruction70_nonidentity

private theorem r71_value : value (representative 71) = wordMatrix349 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix349_expansion.symm

private def obstruction71 : quotientSubgroup := (representative 71) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob71M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob71_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob71M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob71M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob71_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob71M3 = ob71M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob71M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob71_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob71M2 = ob71M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob71M0 : QuotientMatrix := quotientDecode #v[698, 2050, 4091, 1544, 4025, 2347, 2382, 1061, 727, 382, 1295, 232]

private theorem ob71_mul0 : quotientDecode #v[773, 1263, 2318, 3124, 45, 212, 1070, 2863, 3567, 4078, 1906, 2080] * ob71M1 = ob71M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob71_value : value (obstruction71) = ob71M0 := by
  simp only [obstruction71, r71_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[773, 1263, 2318, 3124, 45, 212, 1070, 2863, 3567, 4078, 1906, 2080] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob71_mul3, ob71_mul2, ob71_mul1, ob71_mul0]

private theorem obstruction71_mem : obstruction71 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 71)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 71)).mul_mem (representative_mem_join 71) ((baseSubgroup ⊔ Subgroup.zpowers (representative 71)).mul_mem (sylow_mem_join 71 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 71)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 71)).inv_mem (sylow_mem_join 71 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 71)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 71)).inv_mem (sylow_mem_join 71 2)) (sylow_mem_join 71 1)))))

private def ob71Power2 : QuotientMatrix := quotientDecode #v[3523, 2282, 263, 633, 75, 1956, 2688, 357, 1775, 3322, 1171, 584]

private theorem ob71_power2 : value (obstruction71 ^ 2) = ob71Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob71_value) (by rw [pow_one]; exact ob71_value)
  intro i
  fin_cases i <;> rfl

private def ob71Power3 : QuotientMatrix := quotientDecode #v[227, 2722, 1940, 2576, 1534, 1107, 1459, 4083, 890, 20, 1067, 3640]

private theorem ob71_power3 : value (obstruction71 ^ 3) = ob71Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob71_value) ob71_power2
  intro i
  fin_cases i <;> rfl

private def ob71Power4 : QuotientMatrix := quotientDecode #v[3832, 1178, 705, 3631, 3536, 2368, 4055, 1807, 639, 66, 148, 1027]

private theorem ob71_power4 : value (obstruction71 ^ 4) = ob71Power4 := by
  apply power_step _ 2 2 _ _ _ ob71_power2 ob71_power2
  intro i
  fin_cases i <;> rfl

private def ob71Power7 : QuotientMatrix := quotientDecode #v[3066, 3732, 2743, 2449, 1751, 2289, 2838, 128, 975, 3857, 3481, 3690]

private theorem ob71_power7 : value (obstruction71 ^ 7) = ob71Power7 := by
  apply power_step _ 3 4 _ _ _ ob71_power3 ob71_power4
  intro i
  fin_cases i <;> rfl

private def ob71Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob71_power14 : value (obstruction71 ^ 14) = ob71Power14 := by
  apply power_step _ 7 7 _ _ _ ob71_power7 ob71_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction71_small_power : (obstruction71 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction71 ^ 14) = 1
  rw [ob71_power14]
  exact decode_identity

private theorem obstruction71_nonidentity : obstruction71 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob71_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[3523, 2282, 263, 633, 75, 1956, 2688, 357, 1775, 3322, 1171, 584]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative71 :
    representative 71 ∈ involutionMatrixLineStabilizer ∨
    representative 71 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 71), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction71 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 71)).pow_mem obstruction71_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction71_small_power obstruction71_nonidentity

private theorem r72_value : value (representative 72) = wordMatrix354 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix354_expansion.symm

private def obstruction72 : quotientSubgroup := (representative 72) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob72M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob72_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob72M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob72M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob72_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob72M3 = ob72M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob72M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob72_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob72M2 = ob72M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob72M0 : QuotientMatrix := quotientDecode #v[302, 572, 3424, 3414, 1160, 3551, 2724, 932, 3226, 2651, 4085, 3831]

private theorem ob72_mul0 : quotientDecode #v[1049, 3497, 3447, 2588, 2574, 3714, 1419, 2770, 3796, 3516, 2491, 525] * ob72M1 = ob72M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob72_value : value (obstruction72) = ob72M0 := by
  simp only [obstruction72, r72_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[1049, 3497, 3447, 2588, 2574, 3714, 1419, 2770, 3796, 3516, 2491, 525] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob72_mul3, ob72_mul2, ob72_mul1, ob72_mul0]

private theorem obstruction72_mem : obstruction72 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 72)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 72)).mul_mem (representative_mem_join 72) ((baseSubgroup ⊔ Subgroup.zpowers (representative 72)).mul_mem (sylow_mem_join 72 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 72)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 72)).inv_mem (sylow_mem_join 72 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 72)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 72)).inv_mem (sylow_mem_join 72 2)) (sylow_mem_join 72 1)))))

private def ob72Power2 : QuotientMatrix := quotientDecode #v[847, 826, 2787, 3304, 263, 820, 1975, 1498, 2372, 1220, 3034, 1404]

private theorem ob72_power2 : value (obstruction72 ^ 2) = ob72Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob72_value) (by rw [pow_one]; exact ob72_value)
  intro i
  fin_cases i <;> rfl

private def ob72Power3 : QuotientMatrix := quotientDecode #v[3905, 252, 865, 2187, 744, 758, 3509, 397, 1449, 2965, 2772, 170]

private theorem ob72_power3 : value (obstruction72 ^ 3) = ob72Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob72_value) ob72_power2
  intro i
  fin_cases i <;> rfl

private def ob72Power4 : QuotientMatrix := quotientDecode #v[3145, 97, 148, 791, 978, 1360, 2853, 3622, 364, 852, 1092, 273]

private theorem ob72_power4 : value (obstruction72 ^ 4) = ob72Power4 := by
  apply power_step _ 2 2 _ _ _ ob72_power2 ob72_power2
  intro i
  fin_cases i <;> rfl

private def ob72Power7 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob72_power7 : value (obstruction72 ^ 7) = ob72Power7 := by
  apply power_step _ 3 4 _ _ _ ob72_power3 ob72_power4
  intro i
  fin_cases i <;> rfl

private theorem obstruction72_small_power : (obstruction72 ^ 1) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction72 ^ 7) = 1
  rw [ob72_power7]
  exact decode_identity

private theorem obstruction72_nonidentity : obstruction72 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob72_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[302, 572, 3424, 3414, 1160, 3551, 2724, 932, 3226, 2651, 4085, 3831]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative72 :
    representative 72 ∈ involutionMatrixLineStabilizer ∨
    representative 72 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 72), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction72 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 72)).pow_mem obstruction72_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction72_small_power obstruction72_nonidentity

private theorem r73_value : value (representative 73) = wordMatrix356 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix356_expansion.symm

private def obstruction73 : quotientSubgroup := (representative 73) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob73M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob73_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob73M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob73M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob73_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob73M3 = ob73M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob73M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob73_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob73M2 = ob73M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob73M0 : QuotientMatrix := quotientDecode #v[3884, 479, 125, 451, 1140, 2866, 2018, 3356, 2826, 1176, 1295, 3533]

private theorem ob73_mul0 : quotientDecode #v[1746, 3227, 3807, 3834, 2655, 581, 4002, 2351, 1435, 2619, 1906, 3158] * ob73M1 = ob73M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob73_value : value (obstruction73) = ob73M0 := by
  simp only [obstruction73, r73_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[1746, 3227, 3807, 3834, 2655, 581, 4002, 2351, 1435, 2619, 1906, 3158] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob73_mul3, ob73_mul2, ob73_mul1, ob73_mul0]

private theorem obstruction73_mem : obstruction73 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 73)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 73)).mul_mem (representative_mem_join 73) ((baseSubgroup ⊔ Subgroup.zpowers (representative 73)).mul_mem (sylow_mem_join 73 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 73)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 73)).inv_mem (sylow_mem_join 73 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 73)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 73)).inv_mem (sylow_mem_join 73 2)) (sylow_mem_join 73 1)))))

private def ob73Power2 : QuotientMatrix := quotientDecode #v[3548, 2765, 1590, 3847, 3542, 3270, 2702, 1538, 579, 3492, 328, 1956]

private theorem ob73_power2 : value (obstruction73 ^ 2) = ob73Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob73_value) (by rw [pow_one]; exact ob73_value)
  intro i
  fin_cases i <;> rfl

private def ob73Power3 : QuotientMatrix := quotientDecode #v[3324, 3385, 3955, 2526, 3296, 926, 1064, 72, 3465, 1435, 3371, 3278]

private theorem ob73_power3 : value (obstruction73 ^ 3) = ob73Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob73_value) ob73_power2
  intro i
  fin_cases i <;> rfl

private def ob73Power5 : QuotientMatrix := quotientDecode #v[577, 1892, 1412, 1857, 1702, 1999, 649, 1417, 118, 201, 127, 2460]

private theorem ob73_power5 : value (obstruction73 ^ 5) = ob73Power5 := by
  apply power_step _ 2 3 _ _ _ ob73_power2 ob73_power3
  intro i
  fin_cases i <;> rfl

private def ob73Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob73_power10 : value (obstruction73 ^ 10) = ob73Power10 := by
  apply power_step _ 5 5 _ _ _ ob73_power5 ob73_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction73_small_power : (obstruction73 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction73 ^ 10) = 1
  rw [ob73_power10]
  exact decode_identity

private theorem obstruction73_nonidentity : obstruction73 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob73_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3548, 2765, 1590, 3847, 3542, 3270, 2702, 1538, 579, 3492, 328, 1956]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative73 :
    representative 73 ∈ involutionMatrixLineStabilizer ∨
    representative 73 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 73), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction73 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 73)).pow_mem obstruction73_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction73_small_power obstruction73_nonidentity

private theorem r74_value : value (representative 74) = wordMatrix360 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix360_expansion.symm

private def obstruction74 : quotientSubgroup := (representative 74) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob74M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob74_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob74M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob74M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob74_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob74M2 = ob74M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob74M0 : QuotientMatrix := quotientDecode #v[1065, 545, 2379, 766, 1405, 424, 3701, 326, 1809, 1436, 1912, 2734]

private theorem ob74_mul0 : quotientDecode #v[773, 50, 2553, 1513, 927, 4063, 399, 3418, 2984, 321, 1903, 1796] * ob74M1 = ob74M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob74_value : value (obstruction74) = ob74M0 := by
  simp only [obstruction74, r74_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[773, 50, 2553, 1513, 927, 4063, 399, 3418, 2984, 321, 1903, 1796] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob74_mul2, ob74_mul1, ob74_mul0]

private theorem obstruction74_mem : obstruction74 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 74)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 74)).mul_mem (representative_mem_join 74) ((baseSubgroup ⊔ Subgroup.zpowers (representative 74)).mul_mem (sylow_mem_join 74 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 74)).mul_mem (sylow_mem_join 74 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 74)).inv_mem (sylow_mem_join 74 2)))))

private def ob74Power2 : QuotientMatrix := quotientDecode #v[7, 29, 1852, 2030, 1365, 1281, 3976, 526, 1185, 4071, 3499, 1608]

private theorem ob74_power2 : value (obstruction74 ^ 2) = ob74Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob74_value) (by rw [pow_one]; exact ob74_value)
  intro i
  fin_cases i <;> rfl

private def ob74Power3 : QuotientMatrix := quotientDecode #v[3907, 2785, 2709, 762, 1539, 1088, 3299, 3080, 959, 3715, 3807, 3695]

private theorem ob74_power3 : value (obstruction74 ^ 3) = ob74Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob74_value) ob74_power2
  intro i
  fin_cases i <;> rfl

private def ob74Power4 : QuotientMatrix := quotientDecode #v[1830, 1408, 1643, 3749, 1260, 2317, 1349, 3880, 2723, 3844, 4025, 2602]

private theorem ob74_power4 : value (obstruction74 ^ 4) = ob74Power4 := by
  apply power_step _ 2 2 _ _ _ ob74_power2 ob74_power2
  intro i
  fin_cases i <;> rfl

private def ob74Power7 : QuotientMatrix := quotientDecode #v[2007, 360, 4007, 941, 539, 2812, 1109, 2870, 3334, 1817, 3710, 3255]

private theorem ob74_power7 : value (obstruction74 ^ 7) = ob74Power7 := by
  apply power_step _ 3 4 _ _ _ ob74_power3 ob74_power4
  intro i
  fin_cases i <;> rfl

private def ob74Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob74_power14 : value (obstruction74 ^ 14) = ob74Power14 := by
  apply power_step _ 7 7 _ _ _ ob74_power7 ob74_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction74_small_power : (obstruction74 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction74 ^ 14) = 1
  rw [ob74_power14]
  exact decode_identity

private theorem obstruction74_nonidentity : obstruction74 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob74_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[7, 29, 1852, 2030, 1365, 1281, 3976, 526, 1185, 4071, 3499, 1608]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative74 :
    representative 74 ∈ involutionMatrixLineStabilizer ∨
    representative 74 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 74), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction74 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 74)).pow_mem obstruction74_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction74_small_power obstruction74_nonidentity

private theorem r75_value : value (representative 75) = wordMatrix364 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix364_expansion.symm

private def obstruction75 : quotientSubgroup := (representative 75) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob75M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob75_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob75M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob75M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob75_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob75M3 = ob75M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob75M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob75_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob75M2 = ob75M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob75M0 : QuotientMatrix := quotientDecode #v[37, 2967, 1534, 2870, 1125, 2373, 3093, 435, 956, 1507, 2374, 1353]

private theorem ob75_mul0 : quotientDecode #v[3896, 2420, 4080, 2561, 237, 1624, 239, 2294, 247, 1814, 3646, 1557] * ob75M1 = ob75M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob75_value : value (obstruction75) = ob75M0 := by
  simp only [obstruction75, r75_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3896, 2420, 4080, 2561, 237, 1624, 239, 2294, 247, 1814, 3646, 1557] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob75_mul3, ob75_mul2, ob75_mul1, ob75_mul0]

private theorem obstruction75_mem : obstruction75 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 75)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 75)).mul_mem (representative_mem_join 75) ((baseSubgroup ⊔ Subgroup.zpowers (representative 75)).mul_mem (sylow_mem_join 75 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 75)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 75)).inv_mem (sylow_mem_join 75 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 75)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 75)).inv_mem (sylow_mem_join 75 2)) (sylow_mem_join 75 1)))))

private def ob75Power2 : QuotientMatrix := quotientDecode #v[3230, 2188, 3875, 95, 2509, 3899, 3505, 1181, 1028, 1451, 1161, 3580]

private theorem ob75_power2 : value (obstruction75 ^ 2) = ob75Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob75_value) (by rw [pow_one]; exact ob75_value)
  intro i
  fin_cases i <;> rfl

private def ob75Power3 : QuotientMatrix := quotientDecode #v[3206, 2610, 2215, 3338, 1470, 2036, 773, 637, 3256, 648, 998, 509]

private theorem ob75_power3 : value (obstruction75 ^ 3) = ob75Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob75_value) ob75_power2
  intro i
  fin_cases i <;> rfl

private def ob75Power4 : QuotientMatrix := quotientDecode #v[981, 1565, 1011, 3858, 822, 2657, 900, 2619, 2986, 3942, 3285, 3543]

private theorem ob75_power4 : value (obstruction75 ^ 4) = ob75Power4 := by
  apply power_step _ 2 2 _ _ _ ob75_power2 ob75_power2
  intro i
  fin_cases i <;> rfl

private def ob75Power7 : QuotientMatrix := quotientDecode #v[3799, 3579, 2998, 935, 3823, 2818, 1258, 2689, 3452, 2639, 764, 1142]

private theorem ob75_power7 : value (obstruction75 ^ 7) = ob75Power7 := by
  apply power_step _ 3 4 _ _ _ ob75_power3 ob75_power4
  intro i
  fin_cases i <;> rfl

private def ob75Power8 : QuotientMatrix := quotientDecode #v[3683, 4017, 492, 229, 2165, 2177, 3332, 316, 78, 2501, 2989, 1562]

private theorem ob75_power8 : value (obstruction75 ^ 8) = ob75Power8 := by
  apply power_step _ 4 4 _ _ _ ob75_power4 ob75_power4
  intro i
  fin_cases i <;> rfl

private def ob75Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob75_power15 : value (obstruction75 ^ 15) = ob75Power15 := by
  apply power_step _ 7 8 _ _ _ ob75_power7 ob75_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction75_small_power : (obstruction75 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction75 ^ 15) = 1
  rw [ob75_power15]
  exact decode_identity

private theorem obstruction75_nonidentity : obstruction75 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob75_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3206, 2610, 2215, 3338, 1470, 2036, 773, 637, 3256, 648, 998, 509]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative75 :
    representative 75 ∈ involutionMatrixLineStabilizer ∨
    representative 75 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 75), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction75 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 75)).pow_mem obstruction75_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction75_small_power obstruction75_nonidentity

private theorem r76_value : value (representative 76) = wordMatrix369 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix369_expansion.symm

private def obstruction76 : quotientSubgroup := (representative 76) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob76M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob76_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob76M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob76M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob76_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob76M3 = ob76M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob76M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob76_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob76M2 = ob76M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob76M0 : QuotientMatrix := quotientDecode #v[2056, 3282, 328, 980, 4027, 816, 339, 2793, 2297, 533, 879, 834]

private theorem ob76_mul0 : quotientDecode #v[3102, 3846, 2181, 3294, 716, 1706, 2758, 1690, 1180, 197, 1903, 583] * ob76M1 = ob76M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob76_value : value (obstruction76) = ob76M0 := by
  simp only [obstruction76, r76_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3102, 3846, 2181, 3294, 716, 1706, 2758, 1690, 1180, 197, 1903, 583] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob76_mul3, ob76_mul2, ob76_mul1, ob76_mul0]

private theorem obstruction76_mem : obstruction76 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 76)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 76)).mul_mem (representative_mem_join 76) ((baseSubgroup ⊔ Subgroup.zpowers (representative 76)).mul_mem (sylow_mem_join 76 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 76)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 76)).inv_mem (sylow_mem_join 76 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 76)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 76)).inv_mem (sylow_mem_join 76 2)) (sylow_mem_join 76 1)))))

private def ob76Power2 : QuotientMatrix := quotientDecode #v[150, 2302, 2686, 4005, 2989, 1639, 715, 513, 4015, 1262, 3785, 1901]

private theorem ob76_power2 : value (obstruction76 ^ 2) = ob76Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob76_value) (by rw [pow_one]; exact ob76_value)
  intro i
  fin_cases i <;> rfl

private def ob76Power3 : QuotientMatrix := quotientDecode #v[2248, 2621, 705, 2648, 2787, 1675, 3745, 2589, 1374, 1451, 606, 372]

private theorem ob76_power3 : value (obstruction76 ^ 3) = ob76Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob76_value) ob76_power2
  intro i
  fin_cases i <;> rfl

private def ob76Power4 : QuotientMatrix := quotientDecode #v[2860, 1864, 423, 3179, 3335, 3229, 1001, 1144, 2864, 1345, 691, 1129]

private theorem ob76_power4 : value (obstruction76 ^ 4) = ob76Power4 := by
  apply power_step _ 2 2 _ _ _ ob76_power2 ob76_power2
  intro i
  fin_cases i <;> rfl

private def ob76Power7 : QuotientMatrix := quotientDecode #v[3987, 1618, 2556, 941, 1600, 901, 82, 2767, 3561, 361, 299, 2276]

private theorem ob76_power7 : value (obstruction76 ^ 7) = ob76Power7 := by
  apply power_step _ 3 4 _ _ _ ob76_power3 ob76_power4
  intro i
  fin_cases i <;> rfl

private def ob76Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob76_power14 : value (obstruction76 ^ 14) = ob76Power14 := by
  apply power_step _ 7 7 _ _ _ ob76_power7 ob76_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction76_small_power : (obstruction76 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction76 ^ 14) = 1
  rw [ob76_power14]
  exact decode_identity

private theorem obstruction76_nonidentity : obstruction76 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob76_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[150, 2302, 2686, 4005, 2989, 1639, 715, 513, 4015, 1262, 3785, 1901]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative76 :
    representative 76 ∈ involutionMatrixLineStabilizer ∨
    representative 76 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 76), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction76 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 76)).pow_mem obstruction76_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction76_small_power obstruction76_nonidentity

private theorem r77_value : value (representative 77) = wordMatrix371 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix371_expansion.symm

private def obstruction77 : quotientSubgroup := (representative 77) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob77M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob77_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob77M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob77M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob77_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob77M2 = ob77M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob77M0 : QuotientMatrix := quotientDecode #v[3969, 3667, 1751, 272, 3894, 2420, 3230, 1870, 658, 4018, 3244, 355]

private theorem ob77_mul0 : quotientDecode #v[654, 1734, 1772, 3080, 258, 1132, 2042, 3693, 1273, 1627, 2495, 776] * ob77M1 = ob77M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob77_value : value (obstruction77) = ob77M0 := by
  simp only [obstruction77, r77_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[654, 1734, 1772, 3080, 258, 1132, 2042, 3693, 1273, 1627, 2495, 776] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob77_mul2, ob77_mul1, ob77_mul0]

private theorem obstruction77_mem : obstruction77 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 77)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 77)).mul_mem (representative_mem_join 77) ((baseSubgroup ⊔ Subgroup.zpowers (representative 77)).mul_mem (sylow_mem_join 77 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 77)).mul_mem (sylow_mem_join 77 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 77)).inv_mem (sylow_mem_join 77 2)))))

private def ob77Power2 : QuotientMatrix := quotientDecode #v[2080, 7, 253, 3492, 3625, 4090, 3107, 1158, 2457, 4016, 1074, 1706]

private theorem ob77_power2 : value (obstruction77 ^ 2) = ob77Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob77_value) (by rw [pow_one]; exact ob77_value)
  intro i
  fin_cases i <;> rfl

private def ob77Power3 : QuotientMatrix := quotientDecode #v[2071, 1797, 1492, 1968, 1432, 574, 1385, 870, 1304, 483, 1213, 615]

private theorem ob77_power3 : value (obstruction77 ^ 3) = ob77Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob77_value) ob77_power2
  intro i
  fin_cases i <;> rfl

private def ob77Power5 : QuotientMatrix := quotientDecode #v[89, 2758, 3034, 1870, 2720, 829, 3062, 1290, 3622, 1761, 1054, 1203]

private theorem ob77_power5 : value (obstruction77 ^ 5) = ob77Power5 := by
  apply power_step _ 2 3 _ _ _ ob77_power2 ob77_power3
  intro i
  fin_cases i <;> rfl

private def ob77Power6 : QuotientMatrix := quotientDecode #v[3385, 3461, 2022, 1158, 235, 804, 2389, 381, 909, 3643, 2574, 3186]

private theorem ob77_power6 : value (obstruction77 ^ 6) = ob77Power6 := by
  apply power_step _ 3 3 _ _ _ ob77_power3 ob77_power3
  intro i
  fin_cases i <;> rfl

private def ob77Power11 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob77_power11 : value (obstruction77 ^ 11) = ob77Power11 := by
  apply power_step _ 5 6 _ _ _ ob77_power5 ob77_power6
  intro i
  fin_cases i <;> rfl

private theorem obstruction77_small_power : (obstruction77 ^ 1) ^ 11 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction77 ^ 11) = 1
  rw [ob77_power11]
  exact decode_identity

private theorem obstruction77_nonidentity : obstruction77 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob77_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 7) h
  have hn : (quotientDecode #v[3969, 3667, 1751, 272, 3894, 2420, 3230, 1870, 658, 4018, 3244, 355]) 0 7 ≠ (1 : QuotientMatrix) 0 7 := by decide +kernel
  exact hn hc

theorem alternative77 :
    representative 77 ∈ involutionMatrixLineStabilizer ∨
    representative 77 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 77), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction77 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 77)).pow_mem obstruction77_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 11 (by decide +kernel)
    obstruction77_small_power obstruction77_nonidentity

private theorem r78_value : value (representative 78) = wordMatrix376 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix376_expansion.symm

private def obstruction78 : quotientSubgroup := (representative 78) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob78M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob78_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob78M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob78M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob78_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob78M3 = ob78M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob78M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob78_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob78M2 = ob78M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob78M0 : QuotientMatrix := quotientDecode #v[1776, 3504, 4091, 2309, 3208, 1549, 546, 1061, 1619, 385, 1183, 3907]

private theorem ob78_mul0 : quotientDecode #v[1057, 649, 2318, 3482, 3072, 3831, 3369, 2863, 1461, 2009, 2585, 2777] * ob78M1 = ob78M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob78_value : value (obstruction78) = ob78M0 := by
  simp only [obstruction78, r78_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[1057, 649, 2318, 3482, 3072, 3831, 3369, 2863, 1461, 2009, 2585, 2777] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob78_mul3, ob78_mul2, ob78_mul1, ob78_mul0]

private theorem obstruction78_mem : obstruction78 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 78)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 78)).mul_mem (representative_mem_join 78) ((baseSubgroup ⊔ Subgroup.zpowers (representative 78)).mul_mem (sylow_mem_join 78 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 78)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 78)).inv_mem (sylow_mem_join 78 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 78)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 78)).inv_mem (sylow_mem_join 78 2)) (sylow_mem_join 78 1)))))

private def ob78Power2 : QuotientMatrix := quotientDecode #v[2460, 815, 713, 27, 1788, 1296, 2620, 2969, 244, 1158, 396, 1388]

private theorem ob78_power2 : value (obstruction78 ^ 2) = ob78Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob78_value) (by rw [pow_one]; exact ob78_value)
  intro i
  fin_cases i <;> rfl

private def ob78Power3 : QuotientMatrix := quotientDecode #v[1859, 3169, 2163, 3789, 3938, 3652, 697, 4041, 889, 753, 1160, 29]

private theorem ob78_power3 : value (obstruction78 ^ 3) = ob78Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob78_value) ob78_power2
  intro i
  fin_cases i <;> rfl

private def ob78Power4 : QuotientMatrix := quotientDecode #v[2607, 2307, 3236, 3156, 1425, 1924, 212, 1532, 128, 3059, 2495, 3206]

private theorem ob78_power4 : value (obstruction78 ^ 4) = ob78Power4 := by
  apply power_step _ 2 2 _ _ _ ob78_power2 ob78_power2
  intro i
  fin_cases i <;> rfl

private def ob78Power7 : QuotientMatrix := quotientDecode #v[308, 2118, 3435, 317, 25, 698, 2657, 3353, 4041, 1761, 23, 3918]

private theorem ob78_power7 : value (obstruction78 ^ 7) = ob78Power7 := by
  apply power_step _ 3 4 _ _ _ ob78_power3 ob78_power4
  intro i
  fin_cases i <;> rfl

private def ob78Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob78_power14 : value (obstruction78 ^ 14) = ob78Power14 := by
  apply power_step _ 7 7 _ _ _ ob78_power7 ob78_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction78_small_power : (obstruction78 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction78 ^ 14) = 1
  rw [ob78_power14]
  exact decode_identity

private theorem obstruction78_nonidentity : obstruction78 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob78_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[2460, 815, 713, 27, 1788, 1296, 2620, 2969, 244, 1158, 396, 1388]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative78 :
    representative 78 ∈ involutionMatrixLineStabilizer ∨
    representative 78 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 78), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction78 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 78)).pow_mem obstruction78_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction78_small_power obstruction78_nonidentity

private theorem r79_value : value (representative 79) = wordMatrix380 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix380_expansion.symm

private def obstruction79 : quotientSubgroup := (representative 79) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 3) * ((sylowGenerator 1)))))

private def ob79M3 : QuotientMatrix := quotientDecode #v[1315, 3788, 3161, 658, 1953, 612, 2750, 3689, 2461, 795, 1024, 3312]

private theorem ob79_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob79M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob79M2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem ob79_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob79M3 = ob79M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob79M1 : QuotientMatrix := quotientDecode #v[2704, 1044, 1492, 2567, 2887, 649, 4053, 1033, 1232, 4003, 1047, 251]

private theorem ob79_mul1 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob79M2 = ob79M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob79M0 : QuotientMatrix := quotientDecode #v[224, 2179, 235, 1594, 1305, 3845, 517, 2633, 2296, 2522, 309, 2420]

private theorem ob79_mul0 : quotientDecode #v[2254, 2678, 732, 3570, 1425, 1367, 231, 385, 616, 1061, 1626, 3426] * ob79M1 = ob79M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob79_value : value (obstruction79) = ob79M0 := by
  simp only [obstruction79, r79_value, s1_inverse_value, s2_inverse_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[2254, 2678, 732, 3570, 1425, 1367, 231, 385, 616, 1061, 1626, 3426] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob79_mul3, ob79_mul2, ob79_mul1, ob79_mul0]

private theorem obstruction79_mem : obstruction79 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 79)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 79)).mul_mem (representative_mem_join 79) ((baseSubgroup ⊔ Subgroup.zpowers (representative 79)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 79)).inv_mem (sylow_mem_join 79 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 79)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 79)).inv_mem (sylow_mem_join 79 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 79)).mul_mem (sylow_mem_join 79 3) (sylow_mem_join 79 1)))))

private def ob79Power2 : QuotientMatrix := quotientDecode #v[1865, 2910, 2320, 3146, 2574, 2408, 2513, 1137, 3358, 608, 751, 2430]

private theorem ob79_power2 : value (obstruction79 ^ 2) = ob79Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob79_value) (by rw [pow_one]; exact ob79_value)
  intro i
  fin_cases i <;> rfl

private def ob79Power3 : QuotientMatrix := quotientDecode #v[1224, 280, 1173, 1277, 3836, 2742, 3129, 2508, 3058, 1242, 33, 1991]

private theorem ob79_power3 : value (obstruction79 ^ 3) = ob79Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob79_value) ob79_power2
  intro i
  fin_cases i <;> rfl

private def ob79Power5 : QuotientMatrix := quotientDecode #v[773, 2906, 713, 3642, 621, 3655, 1012, 3226, 920, 597, 3617, 1334]

private theorem ob79_power5 : value (obstruction79 ^ 5) = ob79Power5 := by
  apply power_step _ 2 3 _ _ _ ob79_power2 ob79_power3
  intro i
  fin_cases i <;> rfl

private def ob79Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob79_power10 : value (obstruction79 ^ 10) = ob79Power10 := by
  apply power_step _ 5 5 _ _ _ ob79_power5 ob79_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction79_small_power : (obstruction79 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction79 ^ 10) = 1
  rw [ob79_power10]
  exact decode_identity

private theorem obstruction79_nonidentity : obstruction79 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob79_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 3) h
  have hn : (quotientDecode #v[1865, 2910, 2320, 3146, 2574, 2408, 2513, 1137, 3358, 608, 751, 2430]) 0 3 ≠ (1 : QuotientMatrix) 0 3 := by decide +kernel
  exact hn hc

theorem alternative79 :
    representative 79 ∈ involutionMatrixLineStabilizer ∨
    representative 79 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 79), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction79 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 79)).pow_mem obstruction79_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction79_small_power obstruction79_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
