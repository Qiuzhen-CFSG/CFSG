module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second
import Mathlib.Tactic.FinCases

/-!
# The representative alternatives at indices 80 through 89

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

private theorem r80_value : value (representative 80) = wordMatrix383 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix383_expansion.symm

private def obstruction80 : quotientSubgroup := (representative 80) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob80M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob80_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob80M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob80M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob80_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob80M3 = ob80M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob80M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob80_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob80M2 = ob80M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob80M0 : QuotientMatrix := quotientDecode #v[2878, 3425, 2887, 1703, 137, 3829, 439, 3966, 2272, 2671, 3236, 2809]

private theorem ob80_mul0 : quotientDecode #v[17, 2032, 1674, 4084, 1182, 236, 178, 4036, 1086, 2102, 943, 1711] * ob80M1 = ob80M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob80_value : value (obstruction80) = ob80M0 := by
  simp only [obstruction80, r80_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[17, 2032, 1674, 4084, 1182, 236, 178, 4036, 1086, 2102, 943, 1711] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob80_mul3, ob80_mul2, ob80_mul1, ob80_mul0]

private theorem obstruction80_mem : obstruction80 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 80)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 80)).mul_mem (representative_mem_join 80) ((baseSubgroup ⊔ Subgroup.zpowers (representative 80)).mul_mem (sylow_mem_join 80 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 80)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 80)).inv_mem (sylow_mem_join 80 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 80)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 80)).inv_mem (sylow_mem_join 80 2)) (sylow_mem_join 80 1)))))

private def ob80Power2 : QuotientMatrix := quotientDecode #v[1675, 2753, 1241, 2648, 743, 3326, 1274, 2968, 2757, 1131, 3217, 3514]

private theorem ob80_power2 : value (obstruction80 ^ 2) = ob80Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob80_value) (by rw [pow_one]; exact ob80_value)
  intro i
  fin_cases i <;> rfl

private def ob80Power3 : QuotientMatrix := quotientDecode #v[2381, 1377, 3965, 1807, 1867, 1641, 2007, 294, 3622, 798, 660, 1145]

private theorem ob80_power3 : value (obstruction80 ^ 3) = ob80Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob80_value) ob80_power2
  intro i
  fin_cases i <;> rfl

private def ob80Power5 : QuotientMatrix := quotientDecode #v[2959, 2267, 3436, 244, 215, 3117, 1833, 2083, 1958, 2057, 2509, 2721]

private theorem ob80_power5 : value (obstruction80 ^ 5) = ob80Power5 := by
  apply power_step _ 2 3 _ _ _ ob80_power2 ob80_power3
  intro i
  fin_cases i <;> rfl

private def ob80Power10 : QuotientMatrix := quotientDecode #v[993, 1756, 598, 3740, 485, 2390, 308, 1496, 2011, 474, 1050, 3369]

private theorem ob80_power10 : value (obstruction80 ^ 10) = ob80Power10 := by
  apply power_step _ 5 5 _ _ _ ob80_power5 ob80_power5
  intro i
  fin_cases i <;> rfl

private def ob80Power6 : QuotientMatrix := quotientDecode #v[3255, 1089, 3103, 3058, 856, 3702, 3399, 595, 2438, 1888, 2574, 2595]

private theorem ob80_power6 : value (obstruction80 ^ 6) = ob80Power6 := by
  apply power_step _ 3 3 _ _ _ ob80_power3 ob80_power3
  intro i
  fin_cases i <;> rfl

private def ob80Power11 : QuotientMatrix := quotientDecode #v[2445, 1387, 3447, 3621, 2213, 1281, 3547, 3235, 147, 3430, 2027, 3537]

private theorem ob80_power11 : value (obstruction80 ^ 11) = ob80Power11 := by
  apply power_step _ 5 6 _ _ _ ob80_power5 ob80_power6
  intro i
  fin_cases i <;> rfl

private def ob80Power21 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob80_power21 : value (obstruction80 ^ 21) = ob80Power21 := by
  apply power_step _ 10 11 _ _ _ ob80_power10 ob80_power11
  intro i
  fin_cases i <;> rfl

private theorem obstruction80_small_power : (obstruction80 ^ 3) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction80 ^ 21) = 1
  rw [ob80_power21]
  exact decode_identity

private theorem obstruction80_nonidentity : obstruction80 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob80_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[2381, 1377, 3965, 1807, 1867, 1641, 2007, 294, 3622, 798, 660, 1145]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative80 :
    representative 80 ∈ involutionMatrixLineStabilizer ∨
    representative 80 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 80), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction80 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 80)).pow_mem obstruction80_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction80_small_power obstruction80_nonidentity

private theorem r81_value : value (representative 81) = wordMatrix387 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix387_expansion.symm

private def obstruction81 : quotientSubgroup := (representative 81) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob81M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob81_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob81M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob81M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob81_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob81M3 = ob81M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob81M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob81_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob81M2 = ob81M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob81M0 : QuotientMatrix := quotientDecode #v[3081, 3772, 3992, 532, 2961, 2199, 2738, 1473, 2098, 1938, 716, 1987]

private theorem ob81_mul0 : quotientDecode #v[654, 3001, 1873, 2626, 977, 528, 3867, 2060, 2337, 2478, 4012, 2270] * ob81M1 = ob81M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob81_value : value (obstruction81) = ob81M0 := by
  simp only [obstruction81, r81_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[654, 3001, 1873, 2626, 977, 528, 3867, 2060, 2337, 2478, 4012, 2270] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob81_mul3, ob81_mul2, ob81_mul1, ob81_mul0]

private theorem obstruction81_mem : obstruction81 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 81)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 81)).mul_mem (representative_mem_join 81) ((baseSubgroup ⊔ Subgroup.zpowers (representative 81)).mul_mem (sylow_mem_join 81 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 81)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 81)).inv_mem (sylow_mem_join 81 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 81)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 81)).inv_mem (sylow_mem_join 81 2)) (sylow_mem_join 81 1)))))

private def ob81Power2 : QuotientMatrix := quotientDecode #v[2834, 2518, 1771, 923, 2618, 1214, 2090, 2436, 2681, 3456, 1389, 170]

private theorem ob81_power2 : value (obstruction81 ^ 2) = ob81Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob81_value) (by rw [pow_one]; exact ob81_value)
  intro i
  fin_cases i <;> rfl

private def ob81Power3 : QuotientMatrix := quotientDecode #v[3406, 2615, 539, 337, 4095, 1851, 1020, 1448, 2040, 2300, 2398, 510]

private theorem ob81_power3 : value (obstruction81 ^ 3) = ob81Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob81_value) ob81_power2
  intro i
  fin_cases i <;> rfl

private def ob81Power4 : QuotientMatrix := quotientDecode #v[1215, 3706, 3234, 1304, 2531, 3787, 3673, 1468, 781, 1594, 3554, 1911]

private theorem ob81_power4 : value (obstruction81 ^ 4) = ob81Power4 := by
  apply power_step _ 2 2 _ _ _ ob81_power2 ob81_power2
  intro i
  fin_cases i <;> rfl

private def ob81Power7 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob81_power7 : value (obstruction81 ^ 7) = ob81Power7 := by
  apply power_step _ 3 4 _ _ _ ob81_power3 ob81_power4
  intro i
  fin_cases i <;> rfl

private theorem obstruction81_small_power : (obstruction81 ^ 1) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction81 ^ 7) = 1
  rw [ob81_power7]
  exact decode_identity

private theorem obstruction81_nonidentity : obstruction81 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob81_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 3) h
  have hn : (quotientDecode #v[3081, 3772, 3992, 532, 2961, 2199, 2738, 1473, 2098, 1938, 716, 1987]) 0 3 ≠ (1 : QuotientMatrix) 0 3 := by decide +kernel
  exact hn hc

theorem alternative81 :
    representative 81 ∈ involutionMatrixLineStabilizer ∨
    representative 81 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 81), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction81 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 81)).pow_mem obstruction81_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction81_small_power obstruction81_nonidentity

private theorem r82_value : value (representative 82) = wordMatrix392 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix392_expansion.symm

private def obstruction82 : quotientSubgroup := (representative 82) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob82M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob82_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob82M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob82M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob82_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob82M2 = ob82M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob82M0 : QuotientMatrix := quotientDecode #v[3748, 3140, 3164, 250, 3072, 2210, 1122, 117, 3156, 1489, 1127, 3411]

private theorem ob82_mul0 : quotientDecode #v[3743, 4086, 4026, 2953, 868, 1891, 4044, 3020, 445, 2372, 539, 3490] * ob82M1 = ob82M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob82_value : value (obstruction82) = ob82M0 := by
  simp only [obstruction82, r82_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[3743, 4086, 4026, 2953, 868, 1891, 4044, 3020, 445, 2372, 539, 3490] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob82_mul2, ob82_mul1, ob82_mul0]

private theorem obstruction82_mem : obstruction82 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 82)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 82)).mul_mem (representative_mem_join 82) ((baseSubgroup ⊔ Subgroup.zpowers (representative 82)).mul_mem (sylow_mem_join 82 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 82)).mul_mem (sylow_mem_join 82 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 82)).inv_mem (sylow_mem_join 82 2)))))

private def ob82Power2 : QuotientMatrix := quotientDecode #v[2158, 266, 3568, 3083, 2356, 2496, 1251, 568, 3338, 3712, 1563, 4066]

private theorem ob82_power2 : value (obstruction82 ^ 2) = ob82Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob82_value) (by rw [pow_one]; exact ob82_value)
  intro i
  fin_cases i <;> rfl

private def ob82Power3 : QuotientMatrix := quotientDecode #v[369, 234, 1493, 2862, 2553, 1296, 2610, 393, 2526, 3216, 4012, 64]

private theorem ob82_power3 : value (obstruction82 ^ 3) = ob82Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob82_value) ob82_power2
  intro i
  fin_cases i <;> rfl

private def ob82Power4 : QuotientMatrix := quotientDecode #v[560, 11, 732, 3222, 4076, 1075, 100, 639, 2546, 1345, 1216, 1122]

private theorem ob82_power4 : value (obstruction82 ^ 4) = ob82Power4 := by
  apply power_step _ 2 2 _ _ _ ob82_power2 ob82_power2
  intro i
  fin_cases i <;> rfl

private def ob82Power7 : QuotientMatrix := quotientDecode #v[121, 2741, 41, 675, 2802, 734, 2807, 1323, 3622, 3377, 1047, 100]

private theorem ob82_power7 : value (obstruction82 ^ 7) = ob82Power7 := by
  apply power_step _ 3 4 _ _ _ ob82_power3 ob82_power4
  intro i
  fin_cases i <;> rfl

private def ob82Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob82_power14 : value (obstruction82 ^ 14) = ob82Power14 := by
  apply power_step _ 7 7 _ _ _ ob82_power7 ob82_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction82_small_power : (obstruction82 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction82 ^ 14) = 1
  rw [ob82_power14]
  exact decode_identity

private theorem obstruction82_nonidentity : obstruction82 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob82_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[2158, 266, 3568, 3083, 2356, 2496, 1251, 568, 3338, 3712, 1563, 4066]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative82 :
    representative 82 ∈ involutionMatrixLineStabilizer ∨
    representative 82 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 82), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction82 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 82)).pow_mem obstruction82_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction82_small_power obstruction82_nonidentity

private theorem r83_value : value (representative 83) = wordMatrix396 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix396_expansion.symm

private def obstruction83 : quotientSubgroup := (representative 83) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob83M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob83_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob83M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob83M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob83_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob83M2 = ob83M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob83M0 : QuotientMatrix := quotientDecode #v[3213, 1203, 1543, 2305, 1629, 2603, 175, 2275, 1242, 3635, 666, 2947]

private theorem ob83_mul0 : quotientDecode #v[170, 220, 876, 4000, 2942, 2765, 960, 1574, 3099, 3734, 2814, 1298] * ob83M1 = ob83M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob83_value : value (obstruction83) = ob83M0 := by
  simp only [obstruction83, r83_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[170, 220, 876, 4000, 2942, 2765, 960, 1574, 3099, 3734, 2814, 1298] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob83_mul2, ob83_mul1, ob83_mul0]

private theorem obstruction83_mem : obstruction83 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 83)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 83)).mul_mem (representative_mem_join 83) ((baseSubgroup ⊔ Subgroup.zpowers (representative 83)).mul_mem (sylow_mem_join 83 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 83)).mul_mem (sylow_mem_join 83 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 83)).inv_mem (sylow_mem_join 83 2)))))

private def ob83Power2 : QuotientMatrix := quotientDecode #v[625, 3633, 656, 980, 2512, 3748, 1520, 474, 313, 866, 3391, 439]

private theorem ob83_power2 : value (obstruction83 ^ 2) = ob83Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob83_value) (by rw [pow_one]; exact ob83_value)
  intro i
  fin_cases i <;> rfl

private def ob83Power3 : QuotientMatrix := quotientDecode #v[3687, 2001, 141, 767, 328, 997, 634, 1913, 3360, 1246, 1677, 3702]

private theorem ob83_power3 : value (obstruction83 ^ 3) = ob83Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob83_value) ob83_power2
  intro i
  fin_cases i <;> rfl

private def ob83Power4 : QuotientMatrix := quotientDecode #v[919, 2799, 2920, 3377, 3444, 516, 3928, 294, 2024, 1854, 1985, 2375]

private theorem ob83_power4 : value (obstruction83 ^ 4) = ob83Power4 := by
  apply power_step _ 2 2 _ _ _ ob83_power2 ob83_power2
  intro i
  fin_cases i <;> rfl

private def ob83Power7 : QuotientMatrix := quotientDecode #v[1780, 1930, 1256, 2321, 1409, 1107, 200, 2457, 2922, 2173, 1047, 2071]

private theorem ob83_power7 : value (obstruction83 ^ 7) = ob83Power7 := by
  apply power_step _ 3 4 _ _ _ ob83_power3 ob83_power4
  intro i
  fin_cases i <;> rfl

private def ob83Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob83_power14 : value (obstruction83 ^ 14) = ob83Power14 := by
  apply power_step _ 7 7 _ _ _ ob83_power7 ob83_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction83_small_power : (obstruction83 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction83 ^ 14) = 1
  rw [ob83_power14]
  exact decode_identity

private theorem obstruction83_nonidentity : obstruction83 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob83_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 4) h
  have hn : (quotientDecode #v[625, 3633, 656, 980, 2512, 3748, 1520, 474, 313, 866, 3391, 439]) 0 4 ≠ (1 : QuotientMatrix) 0 4 := by decide +kernel
  exact hn hc

theorem alternative83 :
    representative 83 ∈ involutionMatrixLineStabilizer ∨
    representative 83 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 83), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction83 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 83)).pow_mem obstruction83_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction83_small_power obstruction83_nonidentity

private theorem r84_value : value (representative 84) = wordMatrix400 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix400_expansion.symm

private def obstruction84 : quotientSubgroup := (representative 84) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 3) * ((sylowGenerator 1)))))

private def ob84M3 : QuotientMatrix := quotientDecode #v[1315, 3788, 3161, 658, 1953, 612, 2750, 3689, 2461, 795, 1024, 3312]

private theorem ob84_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob84M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob84M2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem ob84_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob84M3 = ob84M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob84M1 : QuotientMatrix := quotientDecode #v[2704, 1044, 1492, 2567, 2887, 649, 4053, 1033, 1232, 4003, 1047, 251]

private theorem ob84_mul1 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob84M2 = ob84M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob84M0 : QuotientMatrix := quotientDecode #v[3895, 1091, 2686, 287, 2425, 3748, 1415, 2324, 2041, 2659, 3838, 3365]

private theorem ob84_mul0 : quotientDecode #v[1547, 4032, 1683, 458, 1852, 1798, 271, 1458, 2550, 1553, 666, 1787] * ob84M1 = ob84M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob84_value : value (obstruction84) = ob84M0 := by
  simp only [obstruction84, r84_value, s1_inverse_value, s2_inverse_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[1547, 4032, 1683, 458, 1852, 1798, 271, 1458, 2550, 1553, 666, 1787] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob84_mul3, ob84_mul2, ob84_mul1, ob84_mul0]

private theorem obstruction84_mem : obstruction84 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 84)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 84)).mul_mem (representative_mem_join 84) ((baseSubgroup ⊔ Subgroup.zpowers (representative 84)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 84)).inv_mem (sylow_mem_join 84 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 84)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 84)).inv_mem (sylow_mem_join 84 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 84)).mul_mem (sylow_mem_join 84 3) (sylow_mem_join 84 1)))))

private def ob84Power2 : QuotientMatrix := quotientDecode #v[2198, 13, 2622, 3733, 1710, 1142, 281, 2523, 1538, 1809, 3540, 4047]

private theorem ob84_power2 : value (obstruction84 ^ 2) = ob84Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob84_value) (by rw [pow_one]; exact ob84_value)
  intro i
  fin_cases i <;> rfl

private def ob84Power3 : QuotientMatrix := quotientDecode #v[885, 1110, 4025, 3228, 3087, 665, 168, 1373, 222, 1322, 2998, 711]

private theorem ob84_power3 : value (obstruction84 ^ 3) = ob84Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob84_value) ob84_power2
  intro i
  fin_cases i <;> rfl

private def ob84Power4 : QuotientMatrix := quotientDecode #v[2697, 3133, 3744, 2263, 974, 1062, 1711, 431, 2760, 767, 75, 2042]

private theorem ob84_power4 : value (obstruction84 ^ 4) = ob84Power4 := by
  apply power_step _ 2 2 _ _ _ ob84_power2 ob84_power2
  intro i
  fin_cases i <;> rfl

private def ob84Power8 : QuotientMatrix := quotientDecode #v[1780, 3239, 199, 2848, 1405, 1776, 2046, 3970, 2770, 724, 2252, 3198]

private theorem ob84_power8 : value (obstruction84 ^ 8) = ob84Power8 := by
  apply power_step _ 4 4 _ _ _ ob84_power4 ob84_power4
  intro i
  fin_cases i <;> rfl

private def ob84Power16 : QuotientMatrix := quotientDecode #v[302, 1876, 744, 648, 2942, 489, 3195, 3985, 3852, 3858, 4069, 1921]

private theorem ob84_power16 : value (obstruction84 ^ 16) = ob84Power16 := by
  apply power_step _ 8 8 _ _ _ ob84_power8 ob84_power8
  intro i
  fin_cases i <;> rfl

private def ob84Power5 : QuotientMatrix := quotientDecode #v[122, 80, 3592, 2501, 3627, 3687, 824, 92, 2762, 312, 4076, 3446]

private theorem ob84_power5 : value (obstruction84 ^ 5) = ob84Power5 := by
  apply power_step _ 2 3 _ _ _ ob84_power2 ob84_power3
  intro i
  fin_cases i <;> rfl

private def ob84Power9 : QuotientMatrix := quotientDecode #v[1453, 1377, 3481, 3611, 3851, 4051, 1800, 790, 1775, 1527, 2775, 3747]

private theorem ob84_power9 : value (obstruction84 ^ 9) = ob84Power9 := by
  apply power_step _ 4 5 _ _ _ ob84_power4 ob84_power5
  intro i
  fin_cases i <;> rfl

private def ob84Power17 : QuotientMatrix := quotientDecode #v[1663, 1508, 2379, 616, 3527, 3046, 3050, 283, 1312, 891, 2367, 1351]

private theorem ob84_power17 : value (obstruction84 ^ 17) = ob84Power17 := by
  apply power_step _ 8 9 _ _ _ ob84_power8 ob84_power9
  intro i
  fin_cases i <;> rfl

private def ob84Power33 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob84_power33 : value (obstruction84 ^ 33) = ob84Power33 := by
  apply power_step _ 16 17 _ _ _ ob84_power16 ob84_power17
  intro i
  fin_cases i <;> rfl

private theorem obstruction84_small_power : (obstruction84 ^ 3) ^ 11 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction84 ^ 33) = 1
  rw [ob84_power33]
  exact decode_identity

private theorem obstruction84_nonidentity : obstruction84 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob84_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[885, 1110, 4025, 3228, 3087, 665, 168, 1373, 222, 1322, 2998, 711]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative84 :
    representative 84 ∈ involutionMatrixLineStabilizer ∨
    representative 84 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 84), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction84 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 84)).pow_mem obstruction84_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 11 (by decide +kernel)
    obstruction84_small_power obstruction84_nonidentity

private theorem r85_value : value (representative 85) = wordMatrix405 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix405_expansion.symm

private def obstruction85 : quotientSubgroup := (representative 85) * ((sylowGenerator 0) * ((sylowGenerator 3) * ((sylowGenerator 2) * ((sylowGenerator 0)))))

private def ob85M3 : QuotientMatrix := quotientDecode #v[2375, 3320, 253, 580, 1365, 2414, 897, 2472, 1582, 1228, 1024, 609]

private theorem ob85_mul3 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] = ob85M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob85M2 : QuotientMatrix := quotientDecode #v[1571, 3474, 910, 3165, 2088, 3477, 3194, 1958, 586, 191, 1047, 2578]

private theorem ob85_mul2 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob85M3 = ob85M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob85M1 : QuotientMatrix := quotientDecode #v[3728, 3474, 246, 3591, 995, 2605, 3010, 30, 1522, 3734, 1047, 2410]

private theorem ob85_mul1 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * ob85M2 = ob85M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob85M0 : QuotientMatrix := quotientDecode #v[3407, 2923, 2400, 320, 55, 2675, 2735, 2760, 3953, 1236, 3250, 2475]

private theorem ob85_mul0 : quotientDecode #v[2750, 406, 3424, 951, 328, 3957, 2894, 2370, 3184, 3644, 3391, 2380] * ob85M1 = ob85M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob85_value : value (obstruction85) = ob85M0 := by
  simp only [obstruction85, r85_value, s0_value, s3_value, s2_value, map_mul]
  change quotientDecode #v[2750, 406, 3424, 951, 328, 3957, 2894, 2370, 3184, 3644, 3391, 2380] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960])))) = _
  rw [ob85_mul3, ob85_mul2, ob85_mul1, ob85_mul0]

private theorem obstruction85_mem : obstruction85 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 85)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 85)).mul_mem (representative_mem_join 85) ((baseSubgroup ⊔ Subgroup.zpowers (representative 85)).mul_mem (sylow_mem_join 85 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 85)).mul_mem (sylow_mem_join 85 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 85)).mul_mem (sylow_mem_join 85 2) (sylow_mem_join 85 0)))))

private def ob85Power2 : QuotientMatrix := quotientDecode #v[3779, 1462, 1542, 1502, 1280, 2992, 960, 3160, 792, 1410, 3838, 261]

private theorem ob85_power2 : value (obstruction85 ^ 2) = ob85Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob85_value) (by rw [pow_one]; exact ob85_value)
  intro i
  fin_cases i <;> rfl

private def ob85Power3 : QuotientMatrix := quotientDecode #v[1934, 324, 2669, 216, 963, 642, 3010, 3777, 2770, 608, 2213, 2910]

private theorem ob85_power3 : value (obstruction85 ^ 3) = ob85Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob85_value) ob85_power2
  intro i
  fin_cases i <;> rfl

private def ob85Power4 : QuotientMatrix := quotientDecode #v[3732, 3262, 2252, 272, 3558, 1399, 2306, 3301, 1604, 1032, 3391, 3037]

private theorem ob85_power4 : value (obstruction85 ^ 4) = ob85Power4 := by
  apply power_step _ 2 2 _ _ _ ob85_power2 ob85_power2
  intro i
  fin_cases i <;> rfl

private def ob85Power7 : QuotientMatrix := quotientDecode #v[1780, 1930, 1256, 2321, 1409, 1107, 200, 2457, 2922, 2173, 1047, 2071]

private theorem ob85_power7 : value (obstruction85 ^ 7) = ob85Power7 := by
  apply power_step _ 3 4 _ _ _ ob85_power3 ob85_power4
  intro i
  fin_cases i <;> rfl

private def ob85Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob85_power14 : value (obstruction85 ^ 14) = ob85Power14 := by
  apply power_step _ 7 7 _ _ _ ob85_power7 ob85_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction85_small_power : (obstruction85 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction85 ^ 14) = 1
  rw [ob85_power14]
  exact decode_identity

private theorem obstruction85_nonidentity : obstruction85 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob85_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[3779, 1462, 1542, 1502, 1280, 2992, 960, 3160, 792, 1410, 3838, 261]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative85 :
    representative 85 ∈ involutionMatrixLineStabilizer ∨
    representative 85 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 85), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction85 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 85)).pow_mem obstruction85_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction85_small_power obstruction85_nonidentity

private theorem r86_value : value (representative 86) = wordMatrix409 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix409_expansion.symm

private def obstruction86 : quotientSubgroup := (representative 86) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob86M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob86_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob86M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob86M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob86_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob86M3 = ob86M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob86M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob86_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob86M2 = ob86M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob86M0 : QuotientMatrix := quotientDecode #v[894, 2018, 938, 1523, 2130, 2607, 1946, 43, 718, 3608, 1985, 2211]

private theorem ob86_mul0 : quotientDecode #v[3549, 4002, 2663, 1827, 3864, 1012, 958, 3981, 3405, 2575, 2623, 1946] * ob86M1 = ob86M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob86_value : value (obstruction86) = ob86M0 := by
  simp only [obstruction86, r86_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3549, 4002, 2663, 1827, 3864, 1012, 958, 3981, 3405, 2575, 2623, 1946] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob86_mul3, ob86_mul2, ob86_mul1, ob86_mul0]

private theorem obstruction86_mem : obstruction86 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 86)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 86)).mul_mem (representative_mem_join 86) ((baseSubgroup ⊔ Subgroup.zpowers (representative 86)).mul_mem (sylow_mem_join 86 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 86)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 86)).inv_mem (sylow_mem_join 86 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 86)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 86)).inv_mem (sylow_mem_join 86 2)) (sylow_mem_join 86 1)))))

private def ob86Power2 : QuotientMatrix := quotientDecode #v[2186, 363, 1219, 1119, 137, 3665, 383, 2880, 2066, 3291, 4056, 1595]

private theorem ob86_power2 : value (obstruction86 ^ 2) = ob86Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob86_value) (by rw [pow_one]; exact ob86_value)
  intro i
  fin_cases i <;> rfl

private def ob86Power3 : QuotientMatrix := quotientDecode #v[2713, 3604, 1260, 2764, 1702, 3532, 1516, 1007, 1811, 494, 2468, 2763]

private theorem ob86_power3 : value (obstruction86 ^ 3) = ob86Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob86_value) ob86_power2
  intro i
  fin_cases i <;> rfl

private def ob86Power4 : QuotientMatrix := quotientDecode #v[2127, 2690, 3078, 1875, 1941, 3140, 3784, 909, 2009, 3819, 963, 101]

private theorem ob86_power4 : value (obstruction86 ^ 4) = ob86Power4 := by
  apply power_step _ 2 2 _ _ _ ob86_power2 ob86_power2
  intro i
  fin_cases i <;> rfl

private def ob86Power8 : QuotientMatrix := quotientDecode #v[1845, 1921, 1314, 353, 2720, 360, 1883, 2469, 3901, 2514, 1722, 1733]

private theorem ob86_power8 : value (obstruction86 ^ 8) = ob86Power8 := by
  apply power_step _ 4 4 _ _ _ ob86_power4 ob86_power4
  intro i
  fin_cases i <;> rfl

private def ob86Power16 : QuotientMatrix := quotientDecode #v[2442, 3781, 3950, 3643, 2010, 2159, 3195, 802, 3630, 2599, 3045, 897]

private theorem ob86_power16 : value (obstruction86 ^ 16) = ob86Power16 := by
  apply power_step _ 8 8 _ _ _ ob86_power8 ob86_power8
  intro i
  fin_cases i <;> rfl

private def ob86Power5 : QuotientMatrix := quotientDecode #v[3580, 370, 2858, 67, 954, 2898, 824, 2522, 633, 3467, 4091, 3425]

private theorem ob86_power5 : value (obstruction86 ^ 5) = ob86Power5 := by
  apply power_step _ 2 3 _ _ _ ob86_power2 ob86_power3
  intro i
  fin_cases i <;> rfl

private def ob86Power9 : QuotientMatrix := quotientDecode #v[2494, 2114, 2242, 3077, 3263, 2696, 1456, 189, 1262, 620, 2462, 3772]

private theorem ob86_power9 : value (obstruction86 ^ 9) = ob86Power9 := by
  apply power_step _ 4 5 _ _ _ ob86_power4 ob86_power5
  intro i
  fin_cases i <;> rfl

private def ob86Power17 : QuotientMatrix := quotientDecode #v[2135, 1567, 4026, 616, 1765, 2003, 3050, 283, 2798, 2978, 2367, 3971]

private theorem ob86_power17 : value (obstruction86 ^ 17) = ob86Power17 := by
  apply power_step _ 8 9 _ _ _ ob86_power8 ob86_power9
  intro i
  fin_cases i <;> rfl

private def ob86Power33 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob86_power33 : value (obstruction86 ^ 33) = ob86Power33 := by
  apply power_step _ 16 17 _ _ _ ob86_power16 ob86_power17
  intro i
  fin_cases i <;> rfl

private theorem obstruction86_small_power : (obstruction86 ^ 3) ^ 11 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction86 ^ 33) = 1
  rw [ob86_power33]
  exact decode_identity

private theorem obstruction86_nonidentity : obstruction86 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob86_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 3) h
  have hn : (quotientDecode #v[2713, 3604, 1260, 2764, 1702, 3532, 1516, 1007, 1811, 494, 2468, 2763]) 0 3 ≠ (1 : QuotientMatrix) 0 3 := by decide +kernel
  exact hn hc

theorem alternative86 :
    representative 86 ∈ involutionMatrixLineStabilizer ∨
    representative 86 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 86), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction86 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 86)).pow_mem obstruction86_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 11 (by decide +kernel)
    obstruction86_small_power obstruction86_nonidentity

private theorem r87_value : value (representative 87) = wordMatrix414 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix414_expansion.symm

private def obstruction87 : quotientSubgroup := (representative 87) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob87M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob87_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob87M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob87M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob87_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob87M2 = ob87M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob87M0 : QuotientMatrix := quotientDecode #v[999, 3935, 681, 1654, 3536, 270, 1696, 4084, 1524, 2848, 3250, 635]

private theorem ob87_mul0 : quotientDecode #v[3446, 3525, 3627, 4071, 1191, 2184, 3755, 2370, 1814, 3986, 3391, 2080] * ob87M1 = ob87M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob87_value : value (obstruction87) = ob87M0 := by
  simp only [obstruction87, r87_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[3446, 3525, 3627, 4071, 1191, 2184, 3755, 2370, 1814, 3986, 3391, 2080] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob87_mul2, ob87_mul1, ob87_mul0]

private theorem obstruction87_mem : obstruction87 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 87)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 87)).mul_mem (representative_mem_join 87) ((baseSubgroup ⊔ Subgroup.zpowers (representative 87)).mul_mem (sylow_mem_join 87 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 87)).mul_mem (sylow_mem_join 87 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 87)).inv_mem (sylow_mem_join 87 2)))))

private def ob87Power2 : QuotientMatrix := quotientDecode #v[2207, 778, 75, 26, 4025, 3700, 2408, 1854, 3685, 3489, 700, 2960]

private theorem ob87_power2 : value (obstruction87 ^ 2) = ob87Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob87_value) (by rw [pow_one]; exact ob87_value)
  intro i
  fin_cases i <;> rfl

private def ob87Power3 : QuotientMatrix := quotientDecode #v[2104, 2045, 3182, 1273, 1702, 3390, 1623, 1336, 777, 1568, 3285, 3723]

private theorem ob87_power3 : value (obstruction87 ^ 3) = ob87Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob87_value) ob87_power2
  intro i
  fin_cases i <;> rfl

private def ob87Power4 : QuotientMatrix := quotientDecode #v[2259, 212, 743, 3241, 1182, 3171, 755, 1006, 2885, 1692, 2819, 211]

private theorem ob87_power4 : value (obstruction87 ^ 4) = ob87Power4 := by
  apply power_step _ 2 2 _ _ _ ob87_power2 ob87_power2
  intro i
  fin_cases i <;> rfl

private def ob87Power7 : QuotientMatrix := quotientDecode #v[1159, 2471, 3034, 1689, 33, 1778, 274, 1042, 2467, 508, 1127, 2572]

private theorem ob87_power7 : value (obstruction87 ^ 7) = ob87Power7 := by
  apply power_step _ 3 4 _ _ _ ob87_power3 ob87_power4
  intro i
  fin_cases i <;> rfl

private def ob87Power8 : QuotientMatrix := quotientDecode #v[3415, 1892, 258, 39, 745, 3399, 1915, 3645, 1485, 1185, 1293, 3460]

private theorem ob87_power8 : value (obstruction87 ^ 8) = ob87Power8 := by
  apply power_step _ 4 4 _ _ _ ob87_power4 ob87_power4
  intro i
  fin_cases i <;> rfl

private def ob87Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob87_power15 : value (obstruction87 ^ 15) = ob87Power15 := by
  apply power_step _ 7 8 _ _ _ ob87_power7 ob87_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction87_small_power : (obstruction87 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction87 ^ 15) = 1
  rw [ob87_power15]
  exact decode_identity

private theorem obstruction87_nonidentity : obstruction87 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob87_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[2104, 2045, 3182, 1273, 1702, 3390, 1623, 1336, 777, 1568, 3285, 3723]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative87 :
    representative 87 ∈ involutionMatrixLineStabilizer ∨
    representative 87 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 87), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction87 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 87)).pow_mem obstruction87_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction87_small_power obstruction87_nonidentity

private theorem r88_value : value (representative 88) = wordMatrix416 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix416_expansion.symm

private def obstruction88 : quotientSubgroup := (representative 88) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob88M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob88_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob88M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob88M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob88_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob88M3 = ob88M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob88M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob88_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob88M2 = ob88M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob88M0 : QuotientMatrix := quotientDecode #v[2904, 3736, 1633, 3880, 1120, 739, 3303, 3598, 71, 1526, 3940, 346]

private theorem ob88_mul0 : quotientDecode #v[3213, 3590, 2714, 3734, 558, 2149, 11, 159, 3040, 1504, 1792, 2641] * ob88M1 = ob88M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob88_value : value (obstruction88) = ob88M0 := by
  simp only [obstruction88, r88_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3213, 3590, 2714, 3734, 558, 2149, 11, 159, 3040, 1504, 1792, 2641] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob88_mul3, ob88_mul2, ob88_mul1, ob88_mul0]

private theorem obstruction88_mem : obstruction88 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 88)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 88)).mul_mem (representative_mem_join 88) ((baseSubgroup ⊔ Subgroup.zpowers (representative 88)).mul_mem (sylow_mem_join 88 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 88)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 88)).inv_mem (sylow_mem_join 88 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 88)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 88)).inv_mem (sylow_mem_join 88 2)) (sylow_mem_join 88 1)))))

private def ob88Power2 : QuotientMatrix := quotientDecode #v[836, 3726, 4046, 1604, 352, 60, 3477, 3097, 3910, 944, 1002, 2416]

private theorem ob88_power2 : value (obstruction88 ^ 2) = ob88Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob88_value) (by rw [pow_one]; exact ob88_value)
  intro i
  fin_cases i <;> rfl

private def ob88Power3 : QuotientMatrix := quotientDecode #v[3895, 535, 3767, 20, 3651, 4042, 2350, 3630, 3985, 3388, 1035, 2937]

private theorem ob88_power3 : value (obstruction88 ^ 3) = ob88Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob88_value) ob88_power2
  intro i
  fin_cases i <;> rfl

private def ob88Power5 : QuotientMatrix := quotientDecode #v[1332, 212, 1643, 3758, 2421, 3882, 270, 3602, 2129, 3338, 2148, 3151]

private theorem ob88_power5 : value (obstruction88 ^ 5) = ob88Power5 := by
  apply power_step _ 2 3 _ _ _ ob88_power2 ob88_power3
  intro i
  fin_cases i <;> rfl

private def ob88Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob88_power10 : value (obstruction88 ^ 10) = ob88Power10 := by
  apply power_step _ 5 5 _ _ _ ob88_power5 ob88_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction88_small_power : (obstruction88 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction88 ^ 10) = 1
  rw [ob88_power10]
  exact decode_identity

private theorem obstruction88_nonidentity : obstruction88 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob88_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[836, 3726, 4046, 1604, 352, 60, 3477, 3097, 3910, 944, 1002, 2416]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative88 :
    representative 88 ∈ involutionMatrixLineStabilizer ∨
    representative 88 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 88), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction88 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 88)).pow_mem obstruction88_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction88_small_power obstruction88_nonidentity

private theorem r89_value : value (representative 89) = wordMatrix418 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix418_expansion.symm

private def obstruction89 : quotientSubgroup := (representative 89) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob89M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob89_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob89M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob89M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob89_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob89M2 = ob89M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob89M0 : QuotientMatrix := quotientDecode #v[3369, 1730, 3894, 3520, 695, 3406, 972, 278, 1466, 2440, 854, 1993]

private theorem ob89_mul0 : quotientDecode #v[1589, 1392, 258, 2796, 2731, 57, 2543, 2244, 1544, 2857, 2614, 47] * ob89M1 = ob89M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob89_value : value (obstruction89) = ob89M0 := by
  simp only [obstruction89, r89_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[1589, 1392, 258, 2796, 2731, 57, 2543, 2244, 1544, 2857, 2614, 47] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob89_mul2, ob89_mul1, ob89_mul0]

private theorem obstruction89_mem : obstruction89 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 89)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 89)).mul_mem (representative_mem_join 89) ((baseSubgroup ⊔ Subgroup.zpowers (representative 89)).mul_mem (sylow_mem_join 89 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 89)).mul_mem (sylow_mem_join 89 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 89)).inv_mem (sylow_mem_join 89 2)))))

private def ob89Power2 : QuotientMatrix := quotientDecode #v[3202, 3782, 3744, 1023, 954, 1757, 3102, 3833, 769, 3749, 1213, 3415]

private theorem ob89_power2 : value (obstruction89 ^ 2) = ob89Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob89_value) (by rw [pow_one]; exact ob89_value)
  intro i
  fin_cases i <;> rfl

private def ob89Power3 : QuotientMatrix := quotientDecode #v[843, 1593, 335, 2060, 2527, 1388, 540, 221, 283, 848, 614, 1155]

private theorem ob89_power3 : value (obstruction89 ^ 3) = ob89Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob89_value) ob89_power2
  intro i
  fin_cases i <;> rfl

private def ob89Power5 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob89_power5 : value (obstruction89 ^ 5) = ob89Power5 := by
  apply power_step _ 2 3 _ _ _ ob89_power2 ob89_power3
  intro i
  fin_cases i <;> rfl

private theorem obstruction89_small_power : (obstruction89 ^ 1) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction89 ^ 5) = 1
  rw [ob89_power5]
  exact decode_identity

private theorem obstruction89_nonidentity : obstruction89 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob89_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 3) h
  have hn : (quotientDecode #v[3369, 1730, 3894, 3520, 695, 3406, 972, 278, 1466, 2440, 854, 1993]) 0 3 ≠ (1 : QuotientMatrix) 0 3 := by decide +kernel
  exact hn hc

theorem alternative89 :
    representative 89 ∈ involutionMatrixLineStabilizer ∨
    representative 89 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 89), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction89 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 89)).pow_mem obstruction89_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction89_small_power obstruction89_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
