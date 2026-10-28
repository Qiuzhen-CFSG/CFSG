module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second
import Mathlib.Tactic.FinCases

/-!
# The representative alternatives at indices 50 through 59

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

private theorem r50_value : value (representative 50) = wordMatrix268 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix268_expansion.symm

private def obstruction50 : quotientSubgroup := (representative 50) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob50M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob50_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob50M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob50M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob50_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob50M2 = ob50M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob50M0 : QuotientMatrix := quotientDecode #v[2726, 3842, 3691, 2662, 3394, 87, 101, 501, 781, 673, 2163, 969]

private theorem ob50_mul0 : quotientDecode #v[2307, 2955, 1295, 712, 2425, 3010, 1415, 2449, 2228, 44, 2163, 1080] * ob50M1 = ob50M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob50_value : value (obstruction50) = ob50M0 := by
  simp only [obstruction50, r50_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[2307, 2955, 1295, 712, 2425, 3010, 1415, 2449, 2228, 44, 2163, 1080] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob50_mul2, ob50_mul1, ob50_mul0]

private theorem obstruction50_mem : obstruction50 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 50)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 50)).mul_mem (representative_mem_join 50) ((baseSubgroup ⊔ Subgroup.zpowers (representative 50)).mul_mem (sylow_mem_join 50 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 50)).mul_mem (sylow_mem_join 50 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 50)).inv_mem (sylow_mem_join 50 2)))))

private def ob50Power2 : QuotientMatrix := quotientDecode #v[419, 1300, 1771, 51, 2000, 1768, 1279, 2885, 3847, 2469, 2845, 252]

private theorem ob50_power2 : value (obstruction50 ^ 2) = ob50Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob50_value) (by rw [pow_one]; exact ob50_value)
  intro i
  fin_cases i <;> rfl

private def ob50Power3 : QuotientMatrix := quotientDecode #v[1803, 2135, 1239, 2225, 1293, 371, 1375, 1741, 473, 1451, 396, 2184]

private theorem ob50_power3 : value (obstruction50 ^ 3) = ob50Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob50_value) ob50_power2
  intro i
  fin_cases i <;> rfl

private def ob50Power5 : QuotientMatrix := quotientDecode #v[2363, 399, 299, 2850, 865, 3703, 1370, 2681, 1789, 3379, 666, 2954]

private theorem ob50_power5 : value (obstruction50 ^ 5) = ob50Power5 := by
  apply power_step _ 2 3 _ _ _ ob50_power2 ob50_power3
  intro i
  fin_cases i <;> rfl

private def ob50Power10 : QuotientMatrix := quotientDecode #v[1015, 3641, 2844, 4028, 2520, 1520, 2289, 3308, 3758, 2639, 3718, 144]

private theorem ob50_power10 : value (obstruction50 ^ 10) = ob50Power10 := by
  apply power_step _ 5 5 _ _ _ ob50_power5 ob50_power5
  intro i
  fin_cases i <;> rfl

private def ob50Power6 : QuotientMatrix := quotientDecode #v[531, 849, 3224, 3376, 2872, 4004, 829, 3288, 2300, 6, 2930, 1780]

private theorem ob50_power6 : value (obstruction50 ^ 6) = ob50Power6 := by
  apply power_step _ 3 3 _ _ _ ob50_power3 ob50_power3
  intro i
  fin_cases i <;> rfl

private def ob50Power11 : QuotientMatrix := quotientDecode #v[1766, 1230, 2858, 763, 1648, 2043, 1514, 3696, 950, 164, 2439, 3255]

private theorem ob50_power11 : value (obstruction50 ^ 11) = ob50Power11 := by
  apply power_step _ 5 6 _ _ _ ob50_power5 ob50_power6
  intro i
  fin_cases i <;> rfl

private def ob50Power21 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob50_power21 : value (obstruction50 ^ 21) = ob50Power21 := by
  apply power_step _ 10 11 _ _ _ ob50_power10 ob50_power11
  intro i
  fin_cases i <;> rfl

private theorem obstruction50_small_power : (obstruction50 ^ 3) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction50 ^ 21) = 1
  rw [ob50_power21]
  exact decode_identity

private theorem obstruction50_nonidentity : obstruction50 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob50_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[1803, 2135, 1239, 2225, 1293, 371, 1375, 1741, 473, 1451, 396, 2184]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative50 :
    representative 50 ∈ involutionMatrixLineStabilizer ∨
    representative 50 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 50), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction50 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 50)).pow_mem obstruction50_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction50_small_power obstruction50_nonidentity

private theorem r51_value : value (representative 51) = wordMatrix271 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix271_expansion.symm

private def obstruction51 : quotientSubgroup := (representative 51) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob51M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob51_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob51M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob51M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob51_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob51M3 = ob51M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob51M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob51_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob51M2 = ob51M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob51M0 : QuotientMatrix := quotientDecode #v[3148, 1804, 3397, 1374, 1183, 1264, 2274, 753, 3099, 4003, 2814, 4088]

private theorem ob51_mul0 : quotientDecode #v[2959, 3367, 591, 1538, 2585, 1554, 1759, 2737, 90, 2281, 1677, 360] * ob51M1 = ob51M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob51_value : value (obstruction51) = ob51M0 := by
  simp only [obstruction51, r51_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2959, 3367, 591, 1538, 2585, 1554, 1759, 2737, 90, 2281, 1677, 360] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob51_mul3, ob51_mul2, ob51_mul1, ob51_mul0]

private theorem obstruction51_mem : obstruction51 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 51)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 51)).mul_mem (representative_mem_join 51) ((baseSubgroup ⊔ Subgroup.zpowers (representative 51)).mul_mem (sylow_mem_join 51 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 51)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 51)).inv_mem (sylow_mem_join 51 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 51)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 51)).inv_mem (sylow_mem_join 51 2)) (sylow_mem_join 51 1)))))

private def ob51Power2 : QuotientMatrix := quotientDecode #v[1535, 349, 246, 1423, 4043, 130, 1559, 2451, 3975, 3071, 1328, 2460]

private theorem ob51_power2 : value (obstruction51 ^ 2) = ob51Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob51_value) (by rw [pow_one]; exact ob51_value)
  intro i
  fin_cases i <;> rfl

private def ob51Power3 : QuotientMatrix := quotientDecode #v[4034, 1073, 53, 1871, 691, 1533, 1991, 3789, 586, 1383, 1674, 3478]

private theorem ob51_power3 : value (obstruction51 ^ 3) = ob51Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob51_value) ob51_power2
  intro i
  fin_cases i <;> rfl

private def ob51Power4 : QuotientMatrix := quotientDecode #v[2977, 1757, 358, 767, 1661, 2254, 1360, 1249, 1299, 3314, 1534, 1338]

private theorem ob51_power4 : value (obstruction51 ^ 4) = ob51Power4 := by
  apply power_step _ 2 2 _ _ _ ob51_power2 ob51_power2
  intro i
  fin_cases i <;> rfl

private def ob51Power7 : QuotientMatrix := quotientDecode #v[3657, 236, 1140, 1962, 3036, 2007, 436, 1471, 3456, 361, 2511, 240]

private theorem ob51_power7 : value (obstruction51 ^ 7) = ob51Power7 := by
  apply power_step _ 3 4 _ _ _ ob51_power3 ob51_power4
  intro i
  fin_cases i <;> rfl

private def ob51Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob51_power14 : value (obstruction51 ^ 14) = ob51Power14 := by
  apply power_step _ 7 7 _ _ _ ob51_power7 ob51_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction51_small_power : (obstruction51 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction51 ^ 14) = 1
  rw [ob51_power14]
  exact decode_identity

private theorem obstruction51_nonidentity : obstruction51 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob51_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[1535, 349, 246, 1423, 4043, 130, 1559, 2451, 3975, 3071, 1328, 2460]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative51 :
    representative 51 ∈ involutionMatrixLineStabilizer ∨
    representative 51 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 51), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction51 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 51)).pow_mem obstruction51_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction51_small_power obstruction51_nonidentity

private theorem r52_value : value (representative 52) = wordMatrix275 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix275_expansion.symm

private def obstruction52 : quotientSubgroup := (representative 52) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob52M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob52_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob52M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob52M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob52_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob52M3 = ob52M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob52M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob52_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob52M2 = ob52M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob52M0 : QuotientMatrix := quotientDecode #v[1174, 4057, 2314, 2257, 2215, 4077, 56, 2013, 193, 533, 3929, 801]

private theorem ob52_mul0 : quotientDecode #v[2702, 1556, 1960, 887, 4062, 926, 2014, 2142, 1356, 197, 541, 3096] * ob52M1 = ob52M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob52_value : value (obstruction52) = ob52M0 := by
  simp only [obstruction52, r52_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2702, 1556, 1960, 887, 4062, 926, 2014, 2142, 1356, 197, 541, 3096] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob52_mul3, ob52_mul2, ob52_mul1, ob52_mul0]

private theorem obstruction52_mem : obstruction52 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 52)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 52)).mul_mem (representative_mem_join 52) ((baseSubgroup ⊔ Subgroup.zpowers (representative 52)).mul_mem (sylow_mem_join 52 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 52)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 52)).inv_mem (sylow_mem_join 52 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 52)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 52)).inv_mem (sylow_mem_join 52 2)) (sylow_mem_join 52 1)))))

private def ob52Power2 : QuotientMatrix := quotientDecode #v[1776, 3497, 1256, 2293, 2388, 1001, 3995, 1922, 883, 1838, 2676, 2479]

private theorem ob52_power2 : value (obstruction52 ^ 2) = ob52Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob52_value) (by rw [pow_one]; exact ob52_value)
  intro i
  fin_cases i <;> rfl

private def ob52Power3 : QuotientMatrix := quotientDecode #v[3555, 2254, 3968, 3602, 629, 1691, 584, 1417, 3817, 3170, 3916, 324]

private theorem ob52_power3 : value (obstruction52 ^ 3) = ob52Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob52_value) ob52_power2
  intro i
  fin_cases i <;> rfl

private def ob52Power5 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob52_power5 : value (obstruction52 ^ 5) = ob52Power5 := by
  apply power_step _ 2 3 _ _ _ ob52_power2 ob52_power3
  intro i
  fin_cases i <;> rfl

private theorem obstruction52_small_power : (obstruction52 ^ 1) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction52 ^ 5) = 1
  rw [ob52_power5]
  exact decode_identity

private theorem obstruction52_nonidentity : obstruction52 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob52_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1174, 4057, 2314, 2257, 2215, 4077, 56, 2013, 193, 533, 3929, 801]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative52 :
    representative 52 ∈ involutionMatrixLineStabilizer ∨
    representative 52 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 52), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction52 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 52)).pow_mem obstruction52_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction52_small_power obstruction52_nonidentity

private theorem r53_value : value (representative 53) = wordMatrix278 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix278_expansion.symm

private def obstruction53 : quotientSubgroup := (representative 53) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 3) * ((sylowGenerator 1)))))

private def ob53M3 : QuotientMatrix := quotientDecode #v[1315, 3788, 3161, 658, 1953, 612, 2750, 3689, 2461, 795, 1024, 3312]

private theorem ob53_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob53M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob53M2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem ob53_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob53M3 = ob53M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob53M1 : QuotientMatrix := quotientDecode #v[2704, 1044, 1492, 2567, 2887, 649, 4053, 1033, 1232, 4003, 1047, 251]

private theorem ob53_mul1 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob53M2 = ob53M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob53M0 : QuotientMatrix := quotientDecode #v[3907, 441, 1239, 26, 2236, 3902, 2463, 88, 2922, 3932, 822, 4054]

private theorem ob53_mul0 : quotientDecode #v[2766, 1693, 3019, 2633, 884, 668, 4030, 2841, 3403, 1225, 1777, 1090] * ob53M1 = ob53M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob53_value : value (obstruction53) = ob53M0 := by
  simp only [obstruction53, r53_value, s1_inverse_value, s2_inverse_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[2766, 1693, 3019, 2633, 884, 668, 4030, 2841, 3403, 1225, 1777, 1090] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob53_mul3, ob53_mul2, ob53_mul1, ob53_mul0]

private theorem obstruction53_mem : obstruction53 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 53)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 53)).mul_mem (representative_mem_join 53) ((baseSubgroup ⊔ Subgroup.zpowers (representative 53)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 53)).inv_mem (sylow_mem_join 53 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 53)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 53)).inv_mem (sylow_mem_join 53 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 53)).mul_mem (sylow_mem_join 53 3) (sylow_mem_join 53 1)))))

private def ob53Power2 : QuotientMatrix := quotientDecode #v[4019, 1001, 2144, 2335, 3265, 2592, 1647, 313, 3298, 3384, 1754, 3267]

private theorem ob53_power2 : value (obstruction53 ^ 2) = ob53Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob53_value) (by rw [pow_one]; exact ob53_value)
  intro i
  fin_cases i <;> rfl

private def ob53Power3 : QuotientMatrix := quotientDecode #v[502, 3478, 2423, 1591, 2660, 4020, 252, 945, 2976, 18, 3250, 3037]

private theorem ob53_power3 : value (obstruction53 ^ 3) = ob53Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob53_value) ob53_power2
  intro i
  fin_cases i <;> rfl

private def ob53Power5 : QuotientMatrix := quotientDecode #v[1756, 138, 1173, 2361, 1492, 1147, 200, 2481, 1536, 3880, 3624, 2114]

private theorem ob53_power5 : value (obstruction53 ^ 5) = ob53Power5 := by
  apply power_step _ 2 3 _ _ _ ob53_power2 ob53_power3
  intro i
  fin_cases i <;> rfl

private def ob53Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob53_power10 : value (obstruction53 ^ 10) = ob53Power10 := by
  apply power_step _ 5 5 _ _ _ ob53_power5 ob53_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction53_small_power : (obstruction53 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction53 ^ 10) = 1
  rw [ob53_power10]
  exact decode_identity

private theorem obstruction53_nonidentity : obstruction53 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob53_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[4019, 1001, 2144, 2335, 3265, 2592, 1647, 313, 3298, 3384, 1754, 3267]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative53 :
    representative 53 ∈ involutionMatrixLineStabilizer ∨
    representative 53 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 53), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction53 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 53)).pow_mem obstruction53_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction53_small_power obstruction53_nonidentity

private theorem r54_value : value (representative 54) = wordMatrix282 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix282_expansion.symm

private def obstruction54 : quotientSubgroup := (representative 54) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob54M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob54_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob54M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob54M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob54_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob54M3 = ob54M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob54M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob54_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob54M2 = ob54M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob54M0 : QuotientMatrix := quotientDecode #v[305, 841, 1127, 721, 1919, 1116, 2650, 2599, 506, 2536, 3564, 1122]

private theorem ob54_mul0 : quotientDecode #v[3614, 49, 524, 1866, 845, 3508, 1851, 2532, 931, 1913, 2858, 207] * ob54M1 = ob54M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob54_value : value (obstruction54) = ob54M0 := by
  simp only [obstruction54, r54_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3614, 49, 524, 1866, 845, 3508, 1851, 2532, 931, 1913, 2858, 207] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob54_mul3, ob54_mul2, ob54_mul1, ob54_mul0]

private theorem obstruction54_mem : obstruction54 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 54)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 54)).mul_mem (representative_mem_join 54) ((baseSubgroup ⊔ Subgroup.zpowers (representative 54)).mul_mem (sylow_mem_join 54 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 54)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 54)).inv_mem (sylow_mem_join 54 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 54)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 54)).inv_mem (sylow_mem_join 54 2)) (sylow_mem_join 54 1)))))

private def ob54Power2 : QuotientMatrix := quotientDecode #v[1000, 424, 1525, 4059, 2121, 1663, 311, 4041, 828, 872, 2787, 163]

private theorem ob54_power2 : value (obstruction54 ^ 2) = ob54Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob54_value) (by rw [pow_one]; exact ob54_value)
  intro i
  fin_cases i <;> rfl

private def ob54Power3 : QuotientMatrix := quotientDecode #v[3810, 3408, 2590, 1591, 3544, 2483, 1222, 513, 3463, 1221, 3027, 3075]

private theorem ob54_power3 : value (obstruction54 ^ 3) = ob54Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob54_value) ob54_power2
  intro i
  fin_cases i <;> rfl

private def ob54Power5 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob54_power5 : value (obstruction54 ^ 5) = ob54Power5 := by
  apply power_step _ 2 3 _ _ _ ob54_power2 ob54_power3
  intro i
  fin_cases i <;> rfl

private theorem obstruction54_small_power : (obstruction54 ^ 1) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction54 ^ 5) = 1
  rw [ob54_power5]
  exact decode_identity

private theorem obstruction54_nonidentity : obstruction54 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob54_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 4) h
  have hn : (quotientDecode #v[305, 841, 1127, 721, 1919, 1116, 2650, 2599, 506, 2536, 3564, 1122]) 0 4 ≠ (1 : QuotientMatrix) 0 4 := by decide +kernel
  exact hn hc

theorem alternative54 :
    representative 54 ∈ involutionMatrixLineStabilizer ∨
    representative 54 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 54), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction54 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 54)).pow_mem obstruction54_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction54_small_power obstruction54_nonidentity

private theorem r55_value : value (representative 55) = wordMatrix284 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix284_expansion.symm

private def obstruction55 : quotientSubgroup := (representative 55) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob55M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob55_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob55M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob55M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob55_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob55M3 = ob55M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob55M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob55_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob55M2 = ob55M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob55M0 : QuotientMatrix := quotientDecode #v[1950, 1350, 3694, 3776, 3542, 1265, 2045, 39, 1410, 2057, 3212, 2079]

private theorem ob55_mul0 : quotientDecode #v[3066, 3111, 1702, 4065, 3605, 3221, 1445, 3545, 2984, 1689, 1092, 3081] * ob55M1 = ob55M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob55_value : value (obstruction55) = ob55M0 := by
  simp only [obstruction55, r55_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3066, 3111, 1702, 4065, 3605, 3221, 1445, 3545, 2984, 1689, 1092, 3081] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob55_mul3, ob55_mul2, ob55_mul1, ob55_mul0]

private theorem obstruction55_mem : obstruction55 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 55)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 55)).mul_mem (representative_mem_join 55) ((baseSubgroup ⊔ Subgroup.zpowers (representative 55)).mul_mem (sylow_mem_join 55 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 55)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 55)).inv_mem (sylow_mem_join 55 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 55)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 55)).inv_mem (sylow_mem_join 55 2)) (sylow_mem_join 55 1)))))

private def ob55Power2 : QuotientMatrix := quotientDecode #v[2334, 1499, 2686, 2880, 53, 1519, 2250, 2119, 3183, 321, 1050, 1983]

private theorem ob55_power2 : value (obstruction55 ^ 2) = ob55Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob55_value) (by rw [pow_one]; exact ob55_value)
  intro i
  fin_cases i <;> rfl

private def ob55Power3 : QuotientMatrix := quotientDecode #v[1443, 3866, 2852, 617, 215, 2131, 1091, 852, 1513, 1505, 2780, 2673]

private theorem ob55_power3 : value (obstruction55 ^ 3) = ob55Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob55_value) ob55_power2
  intro i
  fin_cases i <;> rfl

private def ob55Power4 : QuotientMatrix := quotientDecode #v[3840, 3912, 3851, 603, 1722, 236, 2473, 2510, 891, 3515, 2740, 2386]

private theorem ob55_power4 : value (obstruction55 ^ 4) = ob55Power4 := by
  apply power_step _ 2 2 _ _ _ ob55_power2 ob55_power2
  intro i
  fin_cases i <;> rfl

private def ob55Power7 : QuotientMatrix := quotientDecode #v[165, 1679, 2165, 2469, 2462, 1545, 853, 3800, 1055, 1604, 3940, 1046]

private theorem ob55_power7 : value (obstruction55 ^ 7) = ob55Power7 := by
  apply power_step _ 3 4 _ _ _ ob55_power3 ob55_power4
  intro i
  fin_cases i <;> rfl

private def ob55Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob55_power14 : value (obstruction55 ^ 14) = ob55Power14 := by
  apply power_step _ 7 7 _ _ _ ob55_power7 ob55_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction55_small_power : (obstruction55 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction55 ^ 14) = 1
  rw [ob55_power14]
  exact decode_identity

private theorem obstruction55_nonidentity : obstruction55 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob55_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[2334, 1499, 2686, 2880, 53, 1519, 2250, 2119, 3183, 321, 1050, 1983]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative55 :
    representative 55 ∈ involutionMatrixLineStabilizer ∨
    representative 55 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 55), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction55 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 55)).pow_mem obstruction55_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction55_small_power obstruction55_nonidentity

private theorem r56_value : value (representative 56) = wordMatrix288 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix288_expansion.symm

private def obstruction56 : quotientSubgroup := (representative 56) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob56M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob56_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob56M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob56M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob56_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob56M3 = ob56M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob56M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob56_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob56M2 = ob56M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob56M0 : QuotientMatrix := quotientDecode #v[1646, 1796, 1626, 1157, 1050, 1625, 1924, 2109, 2984, 3776, 3192, 77]

private theorem ob56_mul0 : quotientDecode #v[168, 1847, 1314, 733, 3283, 3396, 830, 787, 3720, 4065, 3589, 785] * ob56M1 = ob56M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob56_value : value (obstruction56) = ob56M0 := by
  simp only [obstruction56, r56_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[168, 1847, 1314, 733, 3283, 3396, 830, 787, 3720, 4065, 3589, 785] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob56_mul3, ob56_mul2, ob56_mul1, ob56_mul0]

private theorem obstruction56_mem : obstruction56 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 56)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 56)).mul_mem (representative_mem_join 56) ((baseSubgroup ⊔ Subgroup.zpowers (representative 56)).mul_mem (sylow_mem_join 56 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 56)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 56)).inv_mem (sylow_mem_join 56 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 56)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 56)).inv_mem (sylow_mem_join 56 2)) (sylow_mem_join 56 1)))))

private def ob56Power2 : QuotientMatrix := quotientDecode #v[1726, 3914, 679, 1137, 3043, 973, 1911, 1727, 4036, 3404, 3447, 821]

private theorem ob56_power2 : value (obstruction56 ^ 2) = ob56Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob56_value) (by rw [pow_one]; exact ob56_value)
  intro i
  fin_cases i <;> rfl

private def ob56Power3 : QuotientMatrix := quotientDecode #v[3357, 3416, 1940, 4049, 3503, 3680, 3047, 2931, 190, 710, 1386, 1823]

private theorem ob56_power3 : value (obstruction56 ^ 3) = ob56Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob56_value) ob56_power2
  intro i
  fin_cases i <;> rfl

private def ob56Power5 : QuotientMatrix := quotientDecode #v[2573, 2403, 4, 95, 3030, 1972, 2283, 1808, 1805, 361, 3378, 2878]

private theorem ob56_power5 : value (obstruction56 ^ 5) = ob56Power5 := by
  apply power_step _ 2 3 _ _ _ ob56_power2 ob56_power3
  intro i
  fin_cases i <;> rfl

private def ob56Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob56_power10 : value (obstruction56 ^ 10) = ob56Power10 := by
  apply power_step _ 5 5 _ _ _ ob56_power5 ob56_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction56_small_power : (obstruction56 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction56 ^ 10) = 1
  rw [ob56_power10]
  exact decode_identity

private theorem obstruction56_nonidentity : obstruction56 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob56_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1726, 3914, 679, 1137, 3043, 973, 1911, 1727, 4036, 3404, 3447, 821]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative56 :
    representative 56 ∈ involutionMatrixLineStabilizer ∨
    representative 56 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 56), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction56 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 56)).pow_mem obstruction56_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction56_small_power obstruction56_nonidentity

private theorem r57_value : value (representative 57) = wordMatrix292 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix292_expansion.symm

private def obstruction57 : quotientSubgroup := (representative 57) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob57M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob57_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob57M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob57M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob57_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob57M3 = ob57M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob57M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob57_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob57M2 = ob57M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob57M0 : QuotientMatrix := quotientDecode #v[3037, 3837, 1722, 1890, 176, 2410, 3903, 2424, 2658, 2084, 3922, 3601]

private theorem ob57_mul0 : quotientDecode #v[2631, 2812, 1810, 2987, 2503, 401, 3713, 837, 229, 945, 107, 2712] * ob57M1 = ob57M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob57_value : value (obstruction57) = ob57M0 := by
  simp only [obstruction57, r57_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2631, 2812, 1810, 2987, 2503, 401, 3713, 837, 229, 945, 107, 2712] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob57_mul3, ob57_mul2, ob57_mul1, ob57_mul0]

private theorem obstruction57_mem : obstruction57 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 57)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 57)).mul_mem (representative_mem_join 57) ((baseSubgroup ⊔ Subgroup.zpowers (representative 57)).mul_mem (sylow_mem_join 57 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 57)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 57)).inv_mem (sylow_mem_join 57 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 57)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 57)).inv_mem (sylow_mem_join 57 2)) (sylow_mem_join 57 1)))))

private def ob57Power2 : QuotientMatrix := quotientDecode #v[165, 3327, 3659, 1468, 162, 3001, 3623, 1524, 3741, 449, 631, 522]

private theorem ob57_power2 : value (obstruction57 ^ 2) = ob57Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob57_value) (by rw [pow_one]; exact ob57_value)
  intro i
  fin_cases i <;> rfl

private def ob57Power3 : QuotientMatrix := quotientDecode #v[3445, 2598, 1050, 1098, 3823, 74, 919, 3095, 2730, 2040, 3419, 443]

private theorem ob57_power3 : value (obstruction57 ^ 3) = ob57Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob57_value) ob57_power2
  intro i
  fin_cases i <;> rfl

private def ob57Power4 : QuotientMatrix := quotientDecode #v[163, 1816, 1661, 2546, 690, 1696, 2068, 617, 4024, 1515, 1772, 2178]

private theorem ob57_power4 : value (obstruction57 ^ 4) = ob57Power4 := by
  apply power_step _ 2 2 _ _ _ ob57_power2 ob57_power2
  intro i
  fin_cases i <;> rfl

private def ob57Power8 : QuotientMatrix := quotientDecode #v[882, 2047, 45, 3661, 1160, 1998, 3149, 526, 2996, 3008, 85, 3571]

private theorem ob57_power8 : value (obstruction57 ^ 8) = ob57Power8 := by
  apply power_step _ 4 4 _ _ _ ob57_power4 ob57_power4
  intro i
  fin_cases i <;> rfl

private def ob57Power16 : QuotientMatrix := quotientDecode #v[2176, 1993, 2780, 1849, 3094, 2045, 3321, 607, 3298, 964, 2970, 3994]

private theorem ob57_power16 : value (obstruction57 ^ 16) = ob57Power16 := by
  apply power_step _ 8 8 _ _ _ ob57_power8 ob57_power8
  intro i
  fin_cases i <;> rfl

private def ob57Power5 : QuotientMatrix := quotientDecode #v[1330, 2758, 2966, 1299, 1659, 1892, 2075, 718, 1221, 2143, 2435, 2452]

private theorem ob57_power5 : value (obstruction57 ^ 5) = ob57Power5 := by
  apply power_step _ 2 3 _ _ _ ob57_power2 ob57_power3
  intro i
  fin_cases i <;> rfl

private def ob57Power9 : QuotientMatrix := quotientDecode #v[2654, 1649, 879, 3165, 328, 1142, 1145, 1793, 2639, 2576, 744, 412]

private theorem ob57_power9 : value (obstruction57 ^ 9) = ob57Power9 := by
  apply power_step _ 4 5 _ _ _ ob57_power4 ob57_power5
  intro i
  fin_cases i <;> rfl

private def ob57Power17 : QuotientMatrix := quotientDecode #v[1897, 2028, 282, 2161, 2484, 2188, 609, 851, 147, 699, 3072, 850]

private theorem ob57_power17 : value (obstruction57 ^ 17) = ob57Power17 := by
  apply power_step _ 8 9 _ _ _ ob57_power8 ob57_power9
  intro i
  fin_cases i <;> rfl

private def ob57Power33 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob57_power33 : value (obstruction57 ^ 33) = ob57Power33 := by
  apply power_step _ 16 17 _ _ _ ob57_power16 ob57_power17
  intro i
  fin_cases i <;> rfl

private theorem obstruction57_small_power : (obstruction57 ^ 3) ^ 11 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction57 ^ 33) = 1
  rw [ob57_power33]
  exact decode_identity

private theorem obstruction57_nonidentity : obstruction57 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob57_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[3445, 2598, 1050, 1098, 3823, 74, 919, 3095, 2730, 2040, 3419, 443]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative57 :
    representative 57 ∈ involutionMatrixLineStabilizer ∨
    representative 57 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 57), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction57 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 57)).pow_mem obstruction57_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 11 (by decide +kernel)
    obstruction57_small_power obstruction57_nonidentity

private theorem r58_value : value (representative 58) = wordMatrix295 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix295_expansion.symm

private def obstruction58 : quotientSubgroup := (representative 58) * ((sylowGenerator 2) * ((sylowGenerator 0) * ((sylowGenerator 3) * ((sylowGenerator 2)))))

private def ob58M3 : QuotientMatrix := quotientDecode #v[110, 2621, 2181, 1716, 705, 2797, 2784, 316, 669, 394, 1047, 251]

private theorem ob58_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] = ob58M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob58M2 : QuotientMatrix := quotientDecode #v[2269, 2621, 3069, 1262, 2314, 3413, 3416, 1668, 1317, 4003, 1047, 899]

private theorem ob58_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * ob58M3 = ob58M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob58M1 : QuotientMatrix := quotientDecode #v[2640, 424, 3503, 1007, 1600, 1639, 581, 3843, 2940, 506, 1047, 489]

private theorem ob58_mul1 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * ob58M2 = ob58M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob58M0 : QuotientMatrix := quotientDecode #v[3248, 3618, 1239, 1384, 3147, 99, 1714, 2836, 3765, 3663, 1969, 2020]

private theorem ob58_mul0 : quotientDecode #v[3896, 553, 2374, 2387, 2988, 3189, 3387, 1152, 2346, 1006, 3045, 3562] * ob58M1 = ob58M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob58_value : value (obstruction58) = ob58M0 := by
  simp only [obstruction58, r58_value, s2_value, s0_value, s3_value, map_mul]
  change quotientDecode #v[3896, 553, 2374, 2387, 2988, 3189, 3387, 1152, 2346, 1006, 3045, 3562] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184])))) = _
  rw [ob58_mul3, ob58_mul2, ob58_mul1, ob58_mul0]

private theorem obstruction58_mem : obstruction58 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 58)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 58)).mul_mem (representative_mem_join 58) ((baseSubgroup ⊔ Subgroup.zpowers (representative 58)).mul_mem (sylow_mem_join 58 2) ((baseSubgroup ⊔ Subgroup.zpowers (representative 58)).mul_mem (sylow_mem_join 58 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 58)).mul_mem (sylow_mem_join 58 3) (sylow_mem_join 58 2)))))

private def ob58Power2 : QuotientMatrix := quotientDecode #v[1897, 91, 25, 2749, 285, 1091, 224, 3970, 321, 2949, 3271, 3673]

private theorem ob58_power2 : value (obstruction58 ^ 2) = ob58Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob58_value) (by rw [pow_one]; exact ob58_value)
  intro i
  fin_cases i <;> rfl

private def ob58Power3 : QuotientMatrix := quotientDecode #v[2114, 3331, 1427, 920, 4081, 913, 3525, 1433, 1207, 1133, 2998, 3387]

private theorem ob58_power3 : value (obstruction58 ^ 3) = ob58Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob58_value) ob58_power2
  intro i
  fin_cases i <;> rfl

private def ob58Power4 : QuotientMatrix := quotientDecode #v[3956, 3186, 3273, 717, 3473, 2837, 2849, 1923, 1736, 3183, 2775, 1330]

private theorem ob58_power4 : value (obstruction58 ^ 4) = ob58Power4 := by
  apply power_step _ 2 2 _ _ _ ob58_power2 ob58_power2
  intro i
  fin_cases i <;> rfl

private def ob58Power7 : QuotientMatrix := quotientDecode #v[609, 2603, 1291, 632, 16, 4033, 1586, 2996, 1055, 2963, 3625, 3682]

private theorem ob58_power7 : value (obstruction58 ^ 7) = ob58Power7 := by
  apply power_step _ 3 4 _ _ _ ob58_power3 ob58_power4
  intro i
  fin_cases i <;> rfl

private def ob58Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob58_power14 : value (obstruction58 ^ 14) = ob58Power14 := by
  apply power_step _ 7 7 _ _ _ ob58_power7 ob58_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction58_small_power : (obstruction58 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction58 ^ 14) = 1
  rw [ob58_power14]
  exact decode_identity

private theorem obstruction58_nonidentity : obstruction58 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob58_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 3) h
  have hn : (quotientDecode #v[1897, 91, 25, 2749, 285, 1091, 224, 3970, 321, 2949, 3271, 3673]) 0 3 ≠ (1 : QuotientMatrix) 0 3 := by decide +kernel
  exact hn hc

theorem alternative58 :
    representative 58 ∈ involutionMatrixLineStabilizer ∨
    representative 58 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 58), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction58 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 58)).pow_mem obstruction58_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction58_small_power obstruction58_nonidentity

private theorem r59_value : value (representative 59) = wordMatrix300 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix300_expansion.symm

private def obstruction59 : quotientSubgroup := (representative 59) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob59M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob59_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob59M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob59M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob59_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob59M3 = ob59M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob59M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob59_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob59M2 = ob59M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob59M0 : QuotientMatrix := quotientDecode #v[2184, 207, 2215, 3707, 2553, 3276, 1742, 3214, 587, 2480, 151, 3854]

private theorem ob59_mul0 : quotientDecode #v[2071, 1529, 4062, 1104, 3531, 3974, 2394, 1701, 2951, 1694, 1054, 2504] * ob59M1 = ob59M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob59_value : value (obstruction59) = ob59M0 := by
  simp only [obstruction59, r59_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2071, 1529, 4062, 1104, 3531, 3974, 2394, 1701, 2951, 1694, 1054, 2504] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob59_mul3, ob59_mul2, ob59_mul1, ob59_mul0]

private theorem obstruction59_mem : obstruction59 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 59)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 59)).mul_mem (representative_mem_join 59) ((baseSubgroup ⊔ Subgroup.zpowers (representative 59)).mul_mem (sylow_mem_join 59 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 59)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 59)).inv_mem (sylow_mem_join 59 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 59)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 59)).inv_mem (sylow_mem_join 59 2)) (sylow_mem_join 59 1)))))

private def ob59Power2 : QuotientMatrix := quotientDecode #v[3579, 1243, 4012, 1006, 1219, 773, 1396, 1284, 2370, 1278, 1431, 625]

private theorem ob59_power2 : value (obstruction59 ^ 2) = ob59Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob59_value) (by rw [pow_one]; exact ob59_value)
  intro i
  fin_cases i <;> rfl

private def ob59Power3 : QuotientMatrix := quotientDecode #v[1179, 1298, 764, 2916, 656, 3028, 2432, 2683, 2884, 2545, 1867, 707]

private theorem ob59_power3 : value (obstruction59 ^ 3) = ob59Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob59_value) ob59_power2
  intro i
  fin_cases i <;> rfl

private def ob59Power5 : QuotientMatrix := quotientDecode #v[3742, 3277, 3850, 1552, 1337, 1234, 3639, 3827, 1301, 382, 1937, 3502]

private theorem ob59_power5 : value (obstruction59 ^ 5) = ob59Power5 := by
  apply power_step _ 2 3 _ _ _ ob59_power2 ob59_power3
  intro i
  fin_cases i <;> rfl

private def ob59Power10 : QuotientMatrix := quotientDecode #v[1372, 3455, 1161, 982, 3041, 3745, 2035, 2109, 1577, 3870, 1710, 220]

private theorem ob59_power10 : value (obstruction59 ^ 10) = ob59Power10 := by
  apply power_step _ 5 5 _ _ _ ob59_power5 ob59_power5
  intro i
  fin_cases i <;> rfl

private def ob59Power6 : QuotientMatrix := quotientDecode #v[1357, 2957, 2774, 222, 282, 993, 1020, 283, 2826, 1955, 1683, 2947]

private theorem ob59_power6 : value (obstruction59 ^ 6) = ob59Power6 := by
  apply power_step _ 3 3 _ _ _ ob59_power3 ob59_power3
  intro i
  fin_cases i <;> rfl

private def ob59Power11 : QuotientMatrix := quotientDecode #v[2871, 178, 2794, 42, 2801, 3811, 3166, 1135, 792, 2952, 3958, 1381]

private theorem ob59_power11 : value (obstruction59 ^ 11) = ob59Power11 := by
  apply power_step _ 5 6 _ _ _ ob59_power5 ob59_power6
  intro i
  fin_cases i <;> rfl

private def ob59Power21 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob59_power21 : value (obstruction59 ^ 21) = ob59Power21 := by
  apply power_step _ 10 11 _ _ _ ob59_power10 ob59_power11
  intro i
  fin_cases i <;> rfl

private theorem obstruction59_small_power : (obstruction59 ^ 3) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction59 ^ 21) = 1
  rw [ob59_power21]
  exact decode_identity

private theorem obstruction59_nonidentity : obstruction59 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob59_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[1179, 1298, 764, 2916, 656, 3028, 2432, 2683, 2884, 2545, 1867, 707]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative59 :
    representative 59 ∈ involutionMatrixLineStabilizer ∨
    representative 59 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 59), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction59 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 59)).pow_mem obstruction59_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction59_small_power obstruction59_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
