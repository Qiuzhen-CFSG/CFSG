module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second
import Mathlib.Tactic.FinCases

/-!
# The representative alternatives at indices 60 through 69

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

private theorem r60_value : value (representative 60) = wordMatrix305 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix305_expansion.symm

private def obstruction60 : quotientSubgroup := (representative 60) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob60M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob60_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob60M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob60M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob60_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob60M3 = ob60M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob60M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob60_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob60M2 = ob60M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob60M0 : QuotientMatrix := quotientDecode #v[2825, 863, 3513, 1312, 3398, 965, 386, 1933, 3647, 3707, 1953, 2023]

private theorem ob60_mul0 : quotientDecode #v[3581, 2721, 542, 187, 2601, 1644, 4031, 937, 2006, 1104, 3078, 3425] * ob60M1 = ob60M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob60_value : value (obstruction60) = ob60M0 := by
  simp only [obstruction60, r60_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3581, 2721, 542, 187, 2601, 1644, 4031, 937, 2006, 1104, 3078, 3425] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob60_mul3, ob60_mul2, ob60_mul1, ob60_mul0]

private theorem obstruction60_mem : obstruction60 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 60)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 60)).mul_mem (representative_mem_join 60) ((baseSubgroup ⊔ Subgroup.zpowers (representative 60)).mul_mem (sylow_mem_join 60 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 60)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 60)).inv_mem (sylow_mem_join 60 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 60)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 60)).inv_mem (sylow_mem_join 60 2)) (sylow_mem_join 60 1)))))

private def ob60Power2 : QuotientMatrix := quotientDecode #v[2442, 3151, 2398, 2651, 285, 251, 2797, 1016, 113, 3146, 2212, 1984]

private theorem ob60_power2 : value (obstruction60 ^ 2) = ob60Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob60_value) (by rw [pow_one]; exact ob60_value)
  intro i
  fin_cases i <;> rfl

private def ob60Power3 : QuotientMatrix := quotientDecode #v[2090, 267, 3802, 2094, 233, 1530, 4038, 3560, 1032, 1979, 3606, 490]

private theorem ob60_power3 : value (obstruction60 ^ 3) = ob60Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob60_value) ob60_power2
  intro i
  fin_cases i <;> rfl

private def ob60Power4 : QuotientMatrix := quotientDecode #v[605, 841, 779, 4068, 3043, 1901, 2283, 3731, 641, 925, 3485, 3466]

private theorem ob60_power4 : value (obstruction60 ^ 4) = ob60Power4 := by
  apply power_step _ 2 2 _ _ _ ob60_power2 ob60_power2
  intro i
  fin_cases i <;> rfl

private def ob60Power8 : QuotientMatrix := quotientDecode #v[3623, 1102, 4076, 789, 3223, 3509, 623, 2030, 3923, 2782, 2388, 168]

private theorem ob60_power8 : value (obstruction60 ^ 8) = ob60Power8 := by
  apply power_step _ 4 4 _ _ _ ob60_power4 ob60_power4
  intro i
  fin_cases i <;> rfl

private def ob60Power16 : QuotientMatrix := quotientDecode #v[2834, 908, 2236, 2257, 1792, 424, 916, 3162, 2272, 3031, 3823, 2382]

private theorem ob60_power16 : value (obstruction60 ^ 16) = ob60Power16 := by
  apply power_step _ 8 8 _ _ _ ob60_power8 ob60_power8
  intro i
  fin_cases i <;> rfl

private def ob60Power5 : QuotientMatrix := quotientDecode #v[303, 4079, 3378, 2161, 2623, 1586, 3931, 3232, 767, 2335, 1826, 3979]

private theorem ob60_power5 : value (obstruction60 ^ 5) = ob60Power5 := by
  apply power_step _ 2 3 _ _ _ ob60_power2 ob60_power3
  intro i
  fin_cases i <;> rfl

private def ob60Power9 : QuotientMatrix := quotientDecode #v[2071, 3557, 3409, 2994, 3938, 455, 3315, 2537, 1168, 2323, 2213, 360]

private theorem ob60_power9 : value (obstruction60 ^ 9) = ob60Power9 := by
  apply power_step _ 4 5 _ _ _ ob60_power4 ob60_power5
  intro i
  fin_cases i <;> rfl

private def ob60Power17 : QuotientMatrix := quotientDecode #v[2490, 3920, 1648, 1959, 2021, 3927, 1846, 2813, 557, 2309, 2872, 924]

private theorem ob60_power17 : value (obstruction60 ^ 17) = ob60Power17 := by
  apply power_step _ 8 9 _ _ _ ob60_power8 ob60_power9
  intro i
  fin_cases i <;> rfl

private def ob60Power33 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob60_power33 : value (obstruction60 ^ 33) = ob60Power33 := by
  apply power_step _ 16 17 _ _ _ ob60_power16 ob60_power17
  intro i
  fin_cases i <;> rfl

private theorem obstruction60_small_power : (obstruction60 ^ 3) ^ 11 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction60 ^ 33) = 1
  rw [ob60_power33]
  exact decode_identity

private theorem obstruction60_nonidentity : obstruction60 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob60_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[2090, 267, 3802, 2094, 233, 1530, 4038, 3560, 1032, 1979, 3606, 490]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative60 :
    representative 60 ∈ involutionMatrixLineStabilizer ∨
    representative 60 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 60), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction60 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 60)).pow_mem obstruction60_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 11 (by decide +kernel)
    obstruction60_small_power obstruction60_nonidentity

private theorem r61_value : value (representative 61) = wordMatrix309 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix309_expansion.symm

private def obstruction61 : quotientSubgroup := (representative 61) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob61M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob61_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob61M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob61M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob61_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob61M2 = ob61M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob61M0 : QuotientMatrix := quotientDecode #v[1644, 3007, 3290, 1523, 3244, 2306, 1874, 2478, 712, 3077, 306, 1060]

private theorem ob61_mul0 : quotientDecode #v[3104, 412, 2920, 2378, 2495, 1723, 2406, 3168, 3307, 3763, 3078, 213] * ob61M1 = ob61M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob61_value : value (obstruction61) = ob61M0 := by
  simp only [obstruction61, r61_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[3104, 412, 2920, 2378, 2495, 1723, 2406, 3168, 3307, 3763, 3078, 213] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob61_mul2, ob61_mul1, ob61_mul0]

private theorem obstruction61_mem : obstruction61 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 61)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 61)).mul_mem (representative_mem_join 61) ((baseSubgroup ⊔ Subgroup.zpowers (representative 61)).mul_mem (sylow_mem_join 61 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 61)).mul_mem (sylow_mem_join 61 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 61)).inv_mem (sylow_mem_join 61 2)))))

private def ob61Power2 : QuotientMatrix := quotientDecode #v[2638, 531, 2314, 1403, 3219, 3411, 4030, 1238, 1802, 4000, 3289, 1258]

private theorem ob61_power2 : value (obstruction61 ^ 2) = ob61Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob61_value) (by rw [pow_one]; exact ob61_value)
  intro i
  fin_cases i <;> rfl

private def ob61Power3 : QuotientMatrix := quotientDecode #v[3557, 3450, 2208, 2342, 3527, 499, 1357, 1031, 435, 2935, 1241, 2176]

private theorem ob61_power3 : value (obstruction61 ^ 3) = ob61Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob61_value) ob61_power2
  intro i
  fin_cases i <;> rfl

private def ob61Power4 : QuotientMatrix := quotientDecode #v[2710, 2926, 1160, 2187, 2091, 1097, 3053, 59, 795, 2332, 253, 3466]

private theorem ob61_power4 : value (obstruction61 ^ 4) = ob61Power4 := by
  apply power_step _ 2 2 _ _ _ ob61_power2 ob61_power2
  intro i
  fin_cases i <;> rfl

private def ob61Power7 : QuotientMatrix := quotientDecode #v[4077, 2566, 2552, 1342, 202, 1367, 3742, 1421, 3770, 1394, 285, 3505]

private theorem ob61_power7 : value (obstruction61 ^ 7) = ob61Power7 := by
  apply power_step _ 3 4 _ _ _ ob61_power3 ob61_power4
  intro i
  fin_cases i <;> rfl

private def ob61Power8 : QuotientMatrix := quotientDecode #v[864, 3908, 2125, 1218, 176, 2317, 3719, 1297, 2911, 2745, 289, 3506]

private theorem ob61_power8 : value (obstruction61 ^ 8) = ob61Power8 := by
  apply power_step _ 4 4 _ _ _ ob61_power4 ob61_power4
  intro i
  fin_cases i <;> rfl

private def ob61Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob61_power15 : value (obstruction61 ^ 15) = ob61Power15 := by
  apply power_step _ 7 8 _ _ _ ob61_power7 ob61_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction61_small_power : (obstruction61 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction61 ^ 15) = 1
  rw [ob61_power15]
  exact decode_identity

private theorem obstruction61_nonidentity : obstruction61 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob61_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[3557, 3450, 2208, 2342, 3527, 499, 1357, 1031, 435, 2935, 1241, 2176]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative61 :
    representative 61 ∈ involutionMatrixLineStabilizer ∨
    representative 61 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 61), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction61 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 61)).pow_mem obstruction61_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction61_small_power obstruction61_nonidentity

private theorem r62_value : value (representative 62) = wordMatrix312 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix312_expansion.symm

private def obstruction62 : quotientSubgroup := (representative 62) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob62M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob62_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob62M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob62M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob62_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob62M2 = ob62M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob62M0 : QuotientMatrix := quotientDecode #v[3046, 2754, 492, 2850, 4060, 3460, 409, 658, 344, 2466, 1386, 2914]

private theorem ob62_mul0 : quotientDecode #v[149, 1556, 845, 3097, 1216, 1662, 2177, 1273, 2522, 1312, 904, 1996] * ob62M1 = ob62M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob62_value : value (obstruction62) = ob62M0 := by
  simp only [obstruction62, r62_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[149, 1556, 845, 3097, 1216, 1662, 2177, 1273, 2522, 1312, 904, 1996] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob62_mul2, ob62_mul1, ob62_mul0]

private theorem obstruction62_mem : obstruction62 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 62)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 62)).mul_mem (representative_mem_join 62) ((baseSubgroup ⊔ Subgroup.zpowers (representative 62)).mul_mem (sylow_mem_join 62 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 62)).mul_mem (sylow_mem_join 62 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 62)).inv_mem (sylow_mem_join 62 2)))))

private def ob62Power2 : QuotientMatrix := quotientDecode #v[1593, 2825, 1305, 1246, 235, 3118, 3282, 3630, 1087, 4078, 2511, 1351]

private theorem ob62_power2 : value (obstruction62 ^ 2) = ob62Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob62_value) (by rw [pow_one]; exact ob62_value)
  intro i
  fin_cases i <;> rfl

private def ob62Power3 : QuotientMatrix := quotientDecode #v[3668, 860, 2858, 2481, 1161, 896, 2077, 2594, 3288, 2161, 731, 1379]

private theorem ob62_power3 : value (obstruction62 ^ 3) = ob62Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob62_value) ob62_power2
  intro i
  fin_cases i <;> rfl

private def ob62Power4 : QuotientMatrix := quotientDecode #v[2051, 3185, 4092, 278, 1852, 2664, 1430, 1414, 2557, 837, 3955, 2315]

private theorem ob62_power4 : value (obstruction62 ^ 4) = ob62Power4 := by
  apply power_step _ 2 2 _ _ _ ob62_power2 ob62_power2
  intro i
  fin_cases i <;> rfl

private def ob62Power7 : QuotientMatrix := quotientDecode #v[2155, 1784, 1212, 39, 992, 3902, 2270, 3159, 66, 2506, 269, 3330]

private theorem ob62_power7 : value (obstruction62 ^ 7) = ob62Power7 := by
  apply power_step _ 3 4 _ _ _ ob62_power3 ob62_power4
  intro i
  fin_cases i <;> rfl

private def ob62Power8 : QuotientMatrix := quotientDecode #v[3449, 1721, 3950, 3404, 1653, 1190, 1977, 133, 2907, 2257, 112, 1426]

private theorem ob62_power8 : value (obstruction62 ^ 8) = ob62Power8 := by
  apply power_step _ 4 4 _ _ _ ob62_power4 ob62_power4
  intro i
  fin_cases i <;> rfl

private def ob62Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob62_power15 : value (obstruction62 ^ 15) = ob62Power15 := by
  apply power_step _ 7 8 _ _ _ ob62_power7 ob62_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction62_small_power : (obstruction62 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction62 ^ 15) = 1
  rw [ob62_power15]
  exact decode_identity

private theorem obstruction62_nonidentity : obstruction62 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob62_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3668, 860, 2858, 2481, 1161, 896, 2077, 2594, 3288, 2161, 731, 1379]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative62 :
    representative 62 ∈ involutionMatrixLineStabilizer ∨
    representative 62 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 62), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction62 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 62)).pow_mem obstruction62_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction62_small_power obstruction62_nonidentity

private theorem r63_value : value (representative 63) = wordMatrix315 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix315_expansion.symm

private def obstruction63 : quotientSubgroup := (representative 63) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob63M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob63_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob63M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob63M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob63_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob63M3 = ob63M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob63M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob63_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob63M2 = ob63M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob63M0 : QuotientMatrix := quotientDecode #v[668, 3355, 1050, 651, 1161, 1556, 3747, 2006, 387, 2760, 2686, 3282]

private theorem ob63_mul0 : quotientDecode #v[1115, 2317, 3283, 1100, 137, 3669, 446, 2600, 1336, 486, 644, 3846] * ob63M1 = ob63M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob63_value : value (obstruction63) = ob63M0 := by
  simp only [obstruction63, r63_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[1115, 2317, 3283, 1100, 137, 3669, 446, 2600, 1336, 486, 644, 3846] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob63_mul3, ob63_mul2, ob63_mul1, ob63_mul0]

private theorem obstruction63_mem : obstruction63 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 63)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 63)).mul_mem (representative_mem_join 63) ((baseSubgroup ⊔ Subgroup.zpowers (representative 63)).mul_mem (sylow_mem_join 63 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 63)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 63)).inv_mem (sylow_mem_join 63 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 63)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 63)).inv_mem (sylow_mem_join 63 2)) (sylow_mem_join 63 1)))))

private def ob63Power2 : QuotientMatrix := quotientDecode #v[3846, 3754, 359, 18, 3519, 37, 545, 1480, 2514, 3556, 430, 1611]

private theorem ob63_power2 : value (obstruction63 ^ 2) = ob63Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob63_value) (by rw [pow_one]; exact ob63_value)
  intro i
  fin_cases i <;> rfl

private def ob63Power3 : QuotientMatrix := quotientDecode #v[1254, 566, 681, 2450, 2930, 146, 3648, 3, 3510, 3156, 3019, 793]

private theorem ob63_power3 : value (obstruction63 ^ 3) = ob63Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob63_value) ob63_power2
  intro i
  fin_cases i <;> rfl

private def ob63Power5 : QuotientMatrix := quotientDecode #v[2479, 4019, 1821, 2372, 876, 1757, 2080, 428, 2472, 2332, 1066, 1693]

private theorem ob63_power5 : value (obstruction63 ^ 5) = ob63Power5 := by
  apply power_step _ 2 3 _ _ _ ob63_power2 ob63_power3
  intro i
  fin_cases i <;> rfl

private def ob63Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob63_power10 : value (obstruction63 ^ 10) = ob63Power10 := by
  apply power_step _ 5 5 _ _ _ ob63_power5 ob63_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction63_small_power : (obstruction63 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction63 ^ 10) = 1
  rw [ob63_power10]
  exact decode_identity

private theorem obstruction63_nonidentity : obstruction63 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob63_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3846, 3754, 359, 18, 3519, 37, 545, 1480, 2514, 3556, 430, 1611]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative63 :
    representative 63 ∈ involutionMatrixLineStabilizer ∨
    representative 63 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 63), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction63 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 63)).pow_mem obstruction63_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction63_small_power obstruction63_nonidentity

private theorem r64_value : value (representative 64) = wordMatrix320 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix320_expansion.symm

private def obstruction64 : quotientSubgroup := (representative 64) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob64M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob64_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob64M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob64M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob64_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob64M3 = ob64M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob64M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob64_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob64M2 = ob64M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob64M0 : QuotientMatrix := quotientDecode #v[443, 1876, 1293, 1238, 2961, 2752, 1571, 1356, 1917, 1038, 3838, 3713]

private theorem ob64_mul0 : quotientDecode #v[742, 3264, 1427, 332, 977, 3062, 953, 1238, 428, 1186, 666, 3748] * ob64M1 = ob64M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob64_value : value (obstruction64) = ob64M0 := by
  simp only [obstruction64, r64_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[742, 3264, 1427, 332, 977, 3062, 953, 1238, 428, 1186, 666, 3748] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob64_mul3, ob64_mul2, ob64_mul1, ob64_mul0]

private theorem obstruction64_mem : obstruction64 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 64)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 64)).mul_mem (representative_mem_join 64) ((baseSubgroup ⊔ Subgroup.zpowers (representative 64)).mul_mem (sylow_mem_join 64 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 64)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 64)).inv_mem (sylow_mem_join 64 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 64)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 64)).inv_mem (sylow_mem_join 64 2)) (sylow_mem_join 64 1)))))

private def ob64Power2 : QuotientMatrix := quotientDecode #v[345, 1330, 2531, 1113, 660, 2528, 1759, 3707, 2719, 2161, 192, 134]

private theorem ob64_power2 : value (obstruction64 ^ 2) = ob64Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob64_value) (by rw [pow_one]; exact ob64_value)
  intro i
  fin_cases i <;> rfl

private def ob64Power3 : QuotientMatrix := quotientDecode #v[4002, 3974, 1724, 1569, 4062, 83, 1338, 314, 870, 2120, 879, 1813]

private theorem ob64_power3 : value (obstruction64 ^ 3) = ob64Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob64_value) ob64_power2
  intro i
  fin_cases i <;> rfl

private def ob64Power5 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob64_power5 : value (obstruction64 ^ 5) = ob64Power5 := by
  apply power_step _ 2 3 _ _ _ ob64_power2 ob64_power3
  intro i
  fin_cases i <;> rfl

private theorem obstruction64_small_power : (obstruction64 ^ 1) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction64 ^ 5) = 1
  rw [ob64_power5]
  exact decode_identity

private theorem obstruction64_nonidentity : obstruction64 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob64_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[443, 1876, 1293, 1238, 2961, 2752, 1571, 1356, 1917, 1038, 3838, 3713]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative64 :
    representative 64 ∈ involutionMatrixLineStabilizer ∨
    representative 64 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 64), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction64 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 64)).pow_mem obstruction64_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction64_small_power obstruction64_nonidentity

theorem alternative65 :
    representative 65 ∈ involutionMatrixLineStabilizer ∨
    representative 65 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 65), x ^ 2304 ≠ 1 := by
  exact Or.inr (Or.inl r65_second)

private theorem r66_value : value (representative 66) = wordMatrix327 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix327_expansion.symm

private def obstruction66 : quotientSubgroup := (representative 66) * ((sylowGenerator 3) * ((sylowGenerator 0) * ((sylowGenerator 2) * ((sylowGenerator 0)))))

private def ob66M3 : QuotientMatrix := quotientDecode #v[2375, 3320, 253, 580, 1365, 2414, 897, 2472, 1582, 1228, 1024, 609]

private theorem ob66_mul3 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] = ob66M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob66M2 : QuotientMatrix := quotientDecode #v[2149, 3320, 3041, 491, 3947, 3892, 1499, 4082, 116, 2823, 1024, 2429]

private theorem ob66_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * ob66M3 = ob66M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob66M1 : QuotientMatrix := quotientDecode #v[3728, 502, 1659, 2567, 2314, 211, 4053, 1033, 872, 2060, 1047, 270]

private theorem ob66_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob66M2 = ob66M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob66M0 : QuotientMatrix := quotientDecode #v[3883, 1155, 2136, 2522, 2284, 2587, 236, 2903, 2342, 3721, 4043, 3242]

private theorem ob66_mul0 : quotientDecode #v[170, 2445, 70, 2467, 1642, 924, 390, 1866, 3677, 750, 1216, 343] * ob66M1 = ob66M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob66_value : value (obstruction66) = ob66M0 := by
  simp only [obstruction66, r66_value, s3_value, s0_value, s2_value, map_mul]
  change quotientDecode #v[170, 2445, 70, 2467, 1642, 924, 390, 1866, 3677, 750, 1216, 343] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960])))) = _
  rw [ob66_mul3, ob66_mul2, ob66_mul1, ob66_mul0]

private theorem obstruction66_mem : obstruction66 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 66)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 66)).mul_mem (representative_mem_join 66) ((baseSubgroup ⊔ Subgroup.zpowers (representative 66)).mul_mem (sylow_mem_join 66 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 66)).mul_mem (sylow_mem_join 66 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 66)).mul_mem (sylow_mem_join 66 2) (sylow_mem_join 66 0)))))

private def ob66Power2 : QuotientMatrix := quotientDecode #v[3239, 3892, 3440, 2946, 3208, 2237, 34, 245, 844, 78, 3335, 3956]

private theorem ob66_power2 : value (obstruction66 ^ 2) = ob66Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob66_value) (by rw [pow_one]; exact ob66_value)
  intro i
  fin_cases i <;> rfl

private def ob66Power3 : QuotientMatrix := quotientDecode #v[477, 3681, 2140, 1233, 492, 2979, 3736, 3647, 1729, 1517, 2487, 3725]

private theorem ob66_power3 : value (obstruction66 ^ 3) = ob66Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob66_value) ob66_power2
  intro i
  fin_cases i <;> rfl

private def ob66Power4 : QuotientMatrix := quotientDecode #v[1240, 2100, 1320, 951, 2308, 481, 1929, 1333, 1490, 2532, 4060, 2070]

private theorem ob66_power4 : value (obstruction66 ^ 4) = ob66Power4 := by
  apply power_step _ 2 2 _ _ _ ob66_power2 ob66_power2
  intro i
  fin_cases i <;> rfl

private def ob66Power7 : QuotientMatrix := quotientDecode #v[3117, 3230, 4, 188, 16, 3096, 424, 3256, 92, 2836, 2512, 2396]

private theorem ob66_power7 : value (obstruction66 ^ 7) = ob66Power7 := by
  apply power_step _ 3 4 _ _ _ ob66_power3 ob66_power4
  intro i
  fin_cases i <;> rfl

private def ob66Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob66_power14 : value (obstruction66 ^ 14) = ob66Power14 := by
  apply power_step _ 7 7 _ _ _ ob66_power7 ob66_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction66_small_power : (obstruction66 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction66 ^ 14) = 1
  rw [ob66_power14]
  exact decode_identity

private theorem obstruction66_nonidentity : obstruction66 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob66_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[3239, 3892, 3440, 2946, 3208, 2237, 34, 245, 844, 78, 3335, 3956]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative66 :
    representative 66 ∈ involutionMatrixLineStabilizer ∨
    representative 66 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 66), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction66 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 66)).pow_mem obstruction66_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction66_small_power obstruction66_nonidentity

private theorem r67_value : value (representative 67) = wordMatrix332 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix332_expansion.symm

private def obstruction67 : quotientSubgroup := (representative 67) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob67M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob67_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob67M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob67M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob67_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob67M2 = ob67M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob67M0 : QuotientMatrix := quotientDecode #v[818, 390, 1867, 956, 2787, 3056, 1073, 1666, 786, 508, 192, 3326]

private theorem ob67_mul0 : quotientDecode #v[1313, 1681, 954, 4084, 3841, 2578, 841, 3749, 1700, 3334, 3019, 4010] * ob67M1 = ob67M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob67_value : value (obstruction67) = ob67M0 := by
  simp only [obstruction67, r67_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[1313, 1681, 954, 4084, 3841, 2578, 841, 3749, 1700, 3334, 3019, 4010] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob67_mul2, ob67_mul1, ob67_mul0]

private theorem obstruction67_mem : obstruction67 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 67)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 67)).mul_mem (representative_mem_join 67) ((baseSubgroup ⊔ Subgroup.zpowers (representative 67)).mul_mem (sylow_mem_join 67 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 67)).mul_mem (sylow_mem_join 67 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 67)).inv_mem (sylow_mem_join 67 2)))))

private def ob67Power2 : QuotientMatrix := quotientDecode #v[635, 861, 1815, 392, 1781, 3504, 737, 1592, 2443, 1093, 691, 2799]

private theorem ob67_power2 : value (obstruction67 ^ 2) = ob67Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob67_value) (by rw [pow_one]; exact ob67_value)
  intro i
  fin_cases i <;> rfl

private def ob67Power3 : QuotientMatrix := quotientDecode #v[1494, 3065, 3378, 1580, 1765, 2237, 2957, 915, 2150, 136, 1241, 514]

private theorem ob67_power3 : value (obstruction67 ^ 3) = ob67Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob67_value) ob67_power2
  intro i
  fin_cases i <;> rfl

private def ob67Power4 : QuotientMatrix := quotientDecode #v[3407, 3390, 4025, 3643, 3078, 3242, 3927, 3131, 1522, 1342, 2078, 122]

private theorem ob67_power4 : value (obstruction67 ^ 4) = ob67Power4 := by
  apply power_step _ 2 2 _ _ _ ob67_power2 ob67_power2
  intro i
  fin_cases i <;> rfl

private def ob67Power7 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob67_power7 : value (obstruction67 ^ 7) = ob67Power7 := by
  apply power_step _ 3 4 _ _ _ ob67_power3 ob67_power4
  intro i
  fin_cases i <;> rfl

private theorem obstruction67_small_power : (obstruction67 ^ 1) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction67 ^ 7) = 1
  rw [ob67_power7]
  exact decode_identity

private theorem obstruction67_nonidentity : obstruction67 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob67_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[818, 390, 1867, 956, 2787, 3056, 1073, 1666, 786, 508, 192, 3326]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative67 :
    representative 67 ∈ involutionMatrixLineStabilizer ∨
    representative 67 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 67), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction67 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 67)).pow_mem obstruction67_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction67_small_power obstruction67_nonidentity

private theorem r68_value : value (representative 68) = wordMatrix337 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix337_expansion.symm

private def obstruction68 : quotientSubgroup := (representative 68) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob68M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob68_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob68M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob68M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob68_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob68M2 = ob68M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob68M0 : QuotientMatrix := quotientDecode #v[1730, 2292, 3103, 393, 75, 1874, 2090, 2228, 4024, 3833, 137, 2679]

private theorem ob68_mul0 : quotientDecode #v[1392, 1585, 3444, 1738, 3273, 2406, 2426, 3556, 3031, 2257, 1161, 1555] * ob68M1 = ob68M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob68_value : value (obstruction68) = ob68M0 := by
  simp only [obstruction68, r68_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[1392, 1585, 3444, 1738, 3273, 2406, 2426, 3556, 3031, 2257, 1161, 1555] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob68_mul2, ob68_mul1, ob68_mul0]

private theorem obstruction68_mem : obstruction68 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 68)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 68)).mul_mem (representative_mem_join 68) ((baseSubgroup ⊔ Subgroup.zpowers (representative 68)).mul_mem (sylow_mem_join 68 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 68)).mul_mem (sylow_mem_join 68 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 68)).inv_mem (sylow_mem_join 68 2)))))

private def ob68Power2 : QuotientMatrix := quotientDecode #v[1562, 495, 2325, 71, 1941, 349, 1112, 2501, 1435, 1227, 4095, 2452]

private theorem ob68_power2 : value (obstruction68 ^ 2) = ob68Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob68_value) (by rw [pow_one]; exact ob68_value)
  intro i
  fin_cases i <;> rfl

private def ob68Power3 : QuotientMatrix := quotientDecode #v[1862, 3028, 3929, 2563, 1002, 3213, 2401, 3980, 2161, 4008, 3992, 303]

private theorem ob68_power3 : value (obstruction68 ^ 3) = ob68Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob68_value) ob68_power2
  intro i
  fin_cases i <;> rfl

private def ob68Power4 : QuotientMatrix := quotientDecode #v[3337, 2044, 1173, 2744, 4080, 2334, 3189, 3741, 902, 1488, 713, 2890]

private theorem ob68_power4 : value (obstruction68 ^ 4) = ob68Power4 := by
  apply power_step _ 2 2 _ _ _ ob68_power2 ob68_power2
  intro i
  fin_cases i <;> rfl

private def ob68Power7 : QuotientMatrix := quotientDecode #v[2947, 1169, 3041, 1135, 228, 1082, 174, 3941, 3288, 750, 1024, 3648]

private theorem ob68_power7 : value (obstruction68 ^ 7) = ob68Power7 := by
  apply power_step _ 3 4 _ _ _ ob68_power3 ob68_power4
  intro i
  fin_cases i <;> rfl

private def ob68Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob68_power14 : value (obstruction68 ^ 14) = ob68Power14 := by
  apply power_step _ 7 7 _ _ _ ob68_power7 ob68_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction68_small_power : (obstruction68 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction68 ^ 14) = 1
  rw [ob68_power14]
  exact decode_identity

private theorem obstruction68_nonidentity : obstruction68 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob68_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1562, 495, 2325, 71, 1941, 349, 1112, 2501, 1435, 1227, 4095, 2452]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative68 :
    representative 68 ∈ involutionMatrixLineStabilizer ∨
    representative 68 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 68), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction68 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 68)).pow_mem obstruction68_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction68_small_power obstruction68_nonidentity

private theorem r69_value : value (representative 69) = wordMatrix341 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix341_expansion.symm

private def obstruction69 : quotientSubgroup := (representative 69) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob69M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob69_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob69M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob69M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob69_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob69M3 = ob69M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob69M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob69_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob69M2 = ob69M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob69M0 : QuotientMatrix := quotientDecode #v[3276, 1223, 664, 2137, 3313, 2219, 2991, 2982, 491, 1616, 1788, 2194]

private theorem ob69_mul0 : quotientDecode #v[3974, 3070, 3103, 3438, 2715, 3466, 3754, 3645, 2321, 3539, 1653, 211] * ob69M1 = ob69M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob69_value : value (obstruction69) = ob69M0 := by
  simp only [obstruction69, r69_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3974, 3070, 3103, 3438, 2715, 3466, 3754, 3645, 2321, 3539, 1653, 211] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob69_mul3, ob69_mul2, ob69_mul1, ob69_mul0]

private theorem obstruction69_mem : obstruction69 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 69)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 69)).mul_mem (representative_mem_join 69) ((baseSubgroup ⊔ Subgroup.zpowers (representative 69)).mul_mem (sylow_mem_join 69 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 69)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 69)).inv_mem (sylow_mem_join 69 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 69)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 69)).inv_mem (sylow_mem_join 69 2)) (sylow_mem_join 69 1)))))

private def ob69Power2 : QuotientMatrix := quotientDecode #v[1190, 3174, 2398, 2905, 1777, 3021, 3822, 2683, 2331, 2034, 3646, 2818]

private theorem ob69_power2 : value (obstruction69 ^ 2) = ob69Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob69_value) (by rw [pow_one]; exact ob69_value)
  intro i
  fin_cases i <;> rfl

private def ob69Power3 : QuotientMatrix := quotientDecode #v[942, 2869, 33, 3298, 2099, 2349, 3738, 357, 1498, 467, 610, 3054]

private theorem ob69_power3 : value (obstruction69 ^ 3) = ob69Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob69_value) ob69_power2
  intro i
  fin_cases i <;> rfl

private def ob69Power5 : QuotientMatrix := quotientDecode #v[318, 1327, 3947, 1538, 3838, 3957, 2427, 448, 638, 959, 3767, 1234]

private theorem ob69_power5 : value (obstruction69 ^ 5) = ob69Power5 := by
  apply power_step _ 2 3 _ _ _ ob69_power2 ob69_power3
  intro i
  fin_cases i <;> rfl

private def ob69Power10 : QuotientMatrix := quotientDecode #v[4019, 3780, 4025, 2087, 3244, 3329, 3151, 2757, 1801, 3314, 747, 3549]

private theorem ob69_power10 : value (obstruction69 ^ 10) = ob69Power10 := by
  apply power_step _ 5 5 _ _ _ ob69_power5 ob69_power5
  intro i
  fin_cases i <;> rfl

private def ob69Power6 : QuotientMatrix := quotientDecode #v[2999, 3446, 2691, 1131, 619, 2164, 1758, 482, 1955, 2701, 3409, 3779]

private theorem ob69_power6 : value (obstruction69 ^ 6) = ob69Power6 := by
  apply power_step _ 3 3 _ _ _ ob69_power3 ob69_power3
  intro i
  fin_cases i <;> rfl

private def ob69Power11 : QuotientMatrix := quotientDecode #v[3618, 2735, 700, 2730, 1954, 841, 1803, 159, 1490, 3834, 3744, 1392]

private theorem ob69_power11 : value (obstruction69 ^ 11) = ob69Power11 := by
  apply power_step _ 5 6 _ _ _ ob69_power5 ob69_power6
  intro i
  fin_cases i <;> rfl

private def ob69Power21 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob69_power21 : value (obstruction69 ^ 21) = ob69Power21 := by
  apply power_step _ 10 11 _ _ _ ob69_power10 ob69_power11
  intro i
  fin_cases i <;> rfl

private theorem obstruction69_small_power : (obstruction69 ^ 3) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction69 ^ 21) = 1
  rw [ob69_power21]
  exact decode_identity

private theorem obstruction69_nonidentity : obstruction69 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob69_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[942, 2869, 33, 3298, 2099, 2349, 3738, 357, 1498, 467, 610, 3054]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative69 :
    representative 69 ∈ involutionMatrixLineStabilizer ∨
    representative 69 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 69), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction69 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 69)).pow_mem obstruction69_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction69_small_power obstruction69_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
