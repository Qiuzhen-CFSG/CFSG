module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second
import Mathlib.Tactic.FinCases

/-!
# The representative alternatives at indices 90 through 99

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

private theorem r90_value : value (representative 90) = wordMatrix420 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix420_expansion.symm

private def obstruction90 : quotientSubgroup := (representative 90) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 3) * ((sylowGenerator 1)))))

private def ob90M3 : QuotientMatrix := quotientDecode #v[1315, 3788, 3161, 658, 1953, 612, 2750, 3689, 2461, 795, 1024, 3312]

private theorem ob90_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob90M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob90M2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem ob90_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob90M3 = ob90M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob90M1 : QuotientMatrix := quotientDecode #v[2704, 1044, 1492, 2567, 2887, 649, 4053, 1033, 1232, 4003, 1047, 251]

private theorem ob90_mul1 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob90M2 = ob90M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob90M0 : QuotientMatrix := quotientDecode #v[329, 1101, 3335, 1672, 3710, 2250, 3917, 4074, 3356, 2017, 299, 1872]

private theorem ob90_mul0 : quotientDecode #v[1167, 412, 3963, 3760, 644, 308, 1170, 2370, 4021, 3386, 730, 2682] * ob90M1 = ob90M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob90_value : value (obstruction90) = ob90M0 := by
  simp only [obstruction90, r90_value, s1_inverse_value, s2_inverse_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[1167, 412, 3963, 3760, 644, 308, 1170, 2370, 4021, 3386, 730, 2682] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob90_mul3, ob90_mul2, ob90_mul1, ob90_mul0]

private theorem obstruction90_mem : obstruction90 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 90)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 90)).mul_mem (representative_mem_join 90) ((baseSubgroup ⊔ Subgroup.zpowers (representative 90)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 90)).inv_mem (sylow_mem_join 90 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 90)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 90)).inv_mem (sylow_mem_join 90 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 90)).mul_mem (sylow_mem_join 90 3) (sylow_mem_join 90 1)))))

private def ob90Power2 : QuotientMatrix := quotientDecode #v[1424, 1184, 868, 4008, 1953, 1330, 2317, 1582, 3734, 754, 1626, 2789]

private theorem ob90_power2 : value (obstruction90 ^ 2) = ob90Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob90_value) (by rw [pow_one]; exact ob90_value)
  intro i
  fin_cases i <;> rfl

private def ob90Power3 : QuotientMatrix := quotientDecode #v[3491, 1547, 125, 3374, 3519, 3790, 138, 450, 2372, 1471, 1340, 1170]

private theorem ob90_power3 : value (obstruction90 ^ 3) = ob90Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob90_value) ob90_power2
  intro i
  fin_cases i <;> rfl

private def ob90Power4 : QuotientMatrix := quotientDecode #v[2371, 1350, 831, 3183, 3250, 3839, 3375, 2550, 2054, 3042, 268, 1266]

private theorem ob90_power4 : value (obstruction90 ^ 4) = ob90Power4 := by
  apply power_step _ 2 2 _ _ _ ob90_power2 ob90_power2
  intro i
  fin_cases i <;> rfl

private def ob90Power7 : QuotientMatrix := quotientDecode #v[1780, 2692, 2417, 2321, 1302, 211, 223, 2457, 740, 484, 1047, 270]

private theorem ob90_power7 : value (obstruction90 ^ 7) = ob90Power7 := by
  apply power_step _ 3 4 _ _ _ ob90_power3 ob90_power4
  intro i
  fin_cases i <;> rfl

private def ob90Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob90_power14 : value (obstruction90 ^ 14) = ob90Power14 := by
  apply power_step _ 7 7 _ _ _ ob90_power7 ob90_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction90_small_power : (obstruction90 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction90 ^ 14) = 1
  rw [ob90_power14]
  exact decode_identity

private theorem obstruction90_nonidentity : obstruction90 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob90_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1424, 1184, 868, 4008, 1953, 1330, 2317, 1582, 3734, 754, 1626, 2789]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative90 :
    representative 90 ∈ involutionMatrixLineStabilizer ∨
    representative 90 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 90), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction90 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 90)).pow_mem obstruction90_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction90_small_power obstruction90_nonidentity

private theorem r91_value : value (representative 91) = wordMatrix425 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix425_expansion.symm

private def obstruction91 : quotientSubgroup := (representative 91) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob91M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob91_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob91M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob91M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob91_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob91M3 = ob91M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob91M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob91_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob91M2 = ob91M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob91M0 : QuotientMatrix := quotientDecode #v[3390, 3407, 2140, 2526, 3030, 1095, 1978, 774, 595, 750, 4046, 62]

private theorem ob91_mul0 : quotientDecode #v[1589, 2750, 4013, 18, 2097, 4087, 3653, 449, 418, 182, 1539, 3451] * ob91M1 = ob91M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob91_value : value (obstruction91) = ob91M0 := by
  simp only [obstruction91, r91_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[1589, 2750, 4013, 18, 2097, 4087, 3653, 449, 418, 182, 1539, 3451] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob91_mul3, ob91_mul2, ob91_mul1, ob91_mul0]

private theorem obstruction91_mem : obstruction91 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 91)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 91)).mul_mem (representative_mem_join 91) ((baseSubgroup ⊔ Subgroup.zpowers (representative 91)).mul_mem (sylow_mem_join 91 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 91)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 91)).inv_mem (sylow_mem_join 91 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 91)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 91)).inv_mem (sylow_mem_join 91 2)) (sylow_mem_join 91 1)))))

private def ob91Power2 : QuotientMatrix := quotientDecode #v[3839, 3050, 3536, 458, 2810, 89, 1909, 1454, 3827, 3800, 1852, 860]

private theorem ob91_power2 : value (obstruction91 ^ 2) = ob91Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob91_value) (by rw [pow_one]; exact ob91_value)
  intro i
  fin_cases i <;> rfl

private def ob91Power3 : QuotientMatrix := quotientDecode #v[1984, 1257, 713, 638, 3436, 2188, 570, 1553, 1602, 2986, 352, 3411]

private theorem ob91_power3 : value (obstruction91 ^ 3) = ob91Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob91_value) ob91_power2
  intro i
  fin_cases i <;> rfl

private def ob91Power4 : QuotientMatrix := quotientDecode #v[3023, 3029, 690, 1544, 4060, 698, 2542, 3016, 2005, 851, 430, 446]

private theorem ob91_power4 : value (obstruction91 ^ 4) = ob91Power4 := by
  apply power_step _ 2 2 _ _ _ ob91_power2 ob91_power2
  intro i
  fin_cases i <;> rfl

private def ob91Power8 : QuotientMatrix := quotientDecode #v[958, 447, 3624, 1269, 3542, 2080, 2456, 278, 431, 686, 456, 3604]

private theorem ob91_power8 : value (obstruction91 ^ 8) = ob91Power8 := by
  apply power_step _ 4 4 _ _ _ ob91_power4 ob91_power4
  intro i
  fin_cases i <;> rfl

private def ob91Power16 : QuotientMatrix := quotientDecode #v[3203, 3475, 423, 294, 1212, 1588, 1934, 1006, 69, 250, 3540, 3724]

private theorem ob91_power16 : value (obstruction91 ^ 16) = ob91Power16 := by
  apply power_step _ 8 8 _ _ _ ob91_power8 ob91_power8
  intro i
  fin_cases i <;> rfl

private def ob91Power5 : QuotientMatrix := quotientDecode #v[1484, 2699, 822, 1278, 421, 2792, 3675, 3553, 1403, 3232, 2527, 521]

private theorem ob91_power5 : value (obstruction91 ^ 5) = ob91Power5 := by
  apply power_step _ 2 3 _ _ _ ob91_power2 ob91_power3
  intro i
  fin_cases i <;> rfl

private def ob91Power9 : QuotientMatrix := quotientDecode #v[231, 3895, 135, 385, 2010, 1145, 867, 3222, 1249, 2402, 3889, 3732]

private theorem ob91_power9 : value (obstruction91 ^ 9) = ob91Power9 := by
  apply power_step _ 4 5 _ _ _ ob91_power4 ob91_power5
  intro i
  fin_cases i <;> rfl

private def ob91Power17 : QuotientMatrix := quotientDecode #v[3207, 1282, 3391, 775, 731, 2797, 184, 3211, 728, 4028, 2709, 3994]

private theorem ob91_power17 : value (obstruction91 ^ 17) = ob91Power17 := by
  apply power_step _ 8 9 _ _ _ ob91_power8 ob91_power9
  intro i
  fin_cases i <;> rfl

private def ob91Power33 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob91_power33 : value (obstruction91 ^ 33) = ob91Power33 := by
  apply power_step _ 16 17 _ _ _ ob91_power16 ob91_power17
  intro i
  fin_cases i <;> rfl

private theorem obstruction91_small_power : (obstruction91 ^ 3) ^ 11 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction91 ^ 33) = 1
  rw [ob91_power33]
  exact decode_identity

private theorem obstruction91_nonidentity : obstruction91 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob91_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1984, 1257, 713, 638, 3436, 2188, 570, 1553, 1602, 2986, 352, 3411]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative91 :
    representative 91 ∈ involutionMatrixLineStabilizer ∨
    representative 91 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 91), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction91 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 91)).pow_mem obstruction91_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 11 (by decide +kernel)
    obstruction91_small_power obstruction91_nonidentity

private theorem r92_value : value (representative 92) = wordMatrix427 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix427_expansion.symm

private def obstruction92 : quotientSubgroup := (representative 92) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob92M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob92_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob92M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob92M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob92_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob92M3 = ob92M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob92M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob92_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob92M2 = ob92M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob92M0 : QuotientMatrix := quotientDecode #v[2513, 1965, 3564, 238, 107, 1588, 3245, 276, 2161, 2335, 3125, 3267]

private theorem ob92_mul0 : quotientDecode #v[2592, 3666, 2858, 645, 1103, 942, 824, 294, 2693, 1374, 3348, 1460] * ob92M1 = ob92M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob92_value : value (obstruction92) = ob92M0 := by
  simp only [obstruction92, r92_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2592, 3666, 2858, 645, 1103, 942, 824, 294, 2693, 1374, 3348, 1460] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob92_mul3, ob92_mul2, ob92_mul1, ob92_mul0]

private theorem obstruction92_mem : obstruction92 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 92)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 92)).mul_mem (representative_mem_join 92) ((baseSubgroup ⊔ Subgroup.zpowers (representative 92)).mul_mem (sylow_mem_join 92 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 92)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 92)).inv_mem (sylow_mem_join 92 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 92)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 92)).inv_mem (sylow_mem_join 92 2)) (sylow_mem_join 92 1)))))

private def ob92Power2 : QuotientMatrix := quotientDecode #v[177, 3752, 3592, 290, 1035, 3737, 773, 1526, 4064, 1959, 660, 819]

private theorem ob92_power2 : value (obstruction92 ^ 2) = ob92Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob92_value) (by rw [pow_one]; exact ob92_value)
  intro i
  fin_cases i <;> rfl

private def ob92Power3 : QuotientMatrix := quotientDecode #v[3738, 3623, 2311, 2536, 679, 425, 1363, 1507, 2581, 2539, 1420, 2381]

private theorem ob92_power3 : value (obstruction92 ^ 3) = ob92Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob92_value) ob92_power2
  intro i
  fin_cases i <;> rfl

private def ob92Power4 : QuotientMatrix := quotientDecode #v[4053, 3149, 1826, 4049, 3503, 1646, 1790, 437, 394, 429, 2130, 3276]

private theorem ob92_power4 : value (obstruction92 ^ 4) = ob92Power4 := by
  apply power_step _ 2 2 _ _ _ ob92_power2 ob92_power2
  intro i
  fin_cases i <;> rfl

private def ob92Power7 : QuotientMatrix := quotientDecode #v[2741, 2023, 2556, 946, 716, 1621, 273, 2917, 2105, 42, 158, 3230]

private theorem ob92_power7 : value (obstruction92 ^ 7) = ob92Power7 := by
  apply power_step _ 3 4 _ _ _ ob92_power3 ob92_power4
  intro i
  fin_cases i <;> rfl

private def ob92Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob92_power14 : value (obstruction92 ^ 14) = ob92Power14 := by
  apply power_step _ 7 7 _ _ _ ob92_power7 ob92_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction92_small_power : (obstruction92 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction92 ^ 14) = 1
  rw [ob92_power14]
  exact decode_identity

private theorem obstruction92_nonidentity : obstruction92 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob92_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 4) h
  have hn : (quotientDecode #v[177, 3752, 3592, 290, 1035, 3737, 773, 1526, 4064, 1959, 660, 819]) 0 4 ≠ (1 : QuotientMatrix) 0 4 := by decide +kernel
  exact hn hc

theorem alternative92 :
    representative 92 ∈ involutionMatrixLineStabilizer ∨
    representative 92 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 92), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction92 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 92)).pow_mem obstruction92_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction92_small_power obstruction92_nonidentity

private theorem r93_value : value (representative 93) = wordMatrix431 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix431_expansion.symm

private def obstruction93 : quotientSubgroup := (representative 93) * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob93M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob93_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob93M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob93M1 : QuotientMatrix := quotientDecode #v[308, 3667, 125, 1669, 3853, 3784, 3753, 2665, 1454, 3880, 1024, 2168]

private theorem ob93_mul1 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob93M2 = ob93M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob93M0 : QuotientMatrix := quotientDecode #v[2524, 871, 4081, 833, 1765, 2015, 701, 39, 791, 2978, 1525, 3563]

private theorem ob93_mul0 : quotientDecode #v[2128, 1533, 3934, 283, 1355, 3267, 863, 453, 2694, 2361, 1506, 1965] * ob93M1 = ob93M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob93_value : value (obstruction93) = ob93M0 := by
  simp only [obstruction93, r93_value, s2_inverse_value, s0_value, map_mul]
  change quotientDecode #v[2128, 1533, 3934, 283, 1355, 3267, 863, 453, 2694, 2361, 1506, 1965] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob93_mul2, ob93_mul1, ob93_mul0]

private theorem obstruction93_mem : obstruction93 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 93)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 93)).mul_mem (representative_mem_join 93) ((baseSubgroup ⊔ Subgroup.zpowers (representative 93)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 93)).inv_mem (sylow_mem_join 93 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 93)).mul_mem (sylow_mem_join 93 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 93)).inv_mem (sylow_mem_join 93 2)))))

private def ob93Power2 : QuotientMatrix := quotientDecode #v[1587, 2205, 2775, 980, 3391, 3892, 4051, 661, 2842, 449, 879, 1974]

private theorem ob93_power2 : value (obstruction93 ^ 2) = ob93Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob93_value) (by rw [pow_one]; exact ob93_value)
  intro i
  fin_cases i <;> rfl

private def ob93Power3 : QuotientMatrix := quotientDecode #v[1494, 3653, 1916, 827, 3128, 3680, 3695, 2893, 925, 2129, 3036, 203]

private theorem ob93_power3 : value (obstruction93 ^ 3) = ob93Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob93_value) ob93_power2
  intro i
  fin_cases i <;> rfl

private def ob93Power4 : QuotientMatrix := quotientDecode #v[3595, 1836, 631, 117, 2661, 1758, 213, 655, 2843, 111, 3473, 2912]

private theorem ob93_power4 : value (obstruction93 ^ 4) = ob93Power4 := by
  apply power_step _ 2 2 _ _ _ ob93_power2 ob93_power2
  intro i
  fin_cases i <;> rfl

private def ob93Power7 : QuotientMatrix := quotientDecode #v[3054, 2615, 2185, 3741, 2623, 149, 2992, 3272, 3991, 4059, 2601, 2824]

private theorem ob93_power7 : value (obstruction93 ^ 7) = ob93Power7 := by
  apply power_step _ 3 4 _ _ _ ob93_power3 ob93_power4
  intro i
  fin_cases i <;> rfl

private def ob93Power8 : QuotientMatrix := quotientDecode #v[4044, 569, 1873, 18, 376, 239, 1091, 2501, 803, 3374, 2827, 1567]

private theorem ob93_power8 : value (obstruction93 ^ 8) = ob93Power8 := by
  apply power_step _ 4 4 _ _ _ ob93_power4 ob93_power4
  intro i
  fin_cases i <;> rfl

private def ob93Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob93_power15 : value (obstruction93 ^ 15) = ob93Power15 := by
  apply power_step _ 7 8 _ _ _ ob93_power7 ob93_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction93_small_power : (obstruction93 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction93 ^ 15) = 1
  rw [ob93_power15]
  exact decode_identity

private theorem obstruction93_nonidentity : obstruction93 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob93_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1494, 3653, 1916, 827, 3128, 3680, 3695, 2893, 925, 2129, 3036, 203]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative93 :
    representative 93 ∈ involutionMatrixLineStabilizer ∨
    representative 93 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 93), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction93 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 93)).pow_mem obstruction93_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction93_small_power obstruction93_nonidentity

private theorem r94_value : value (representative 94) = wordMatrix434 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix434_expansion.symm

private def obstruction94 : quotientSubgroup := (representative 94) * ((sylowGenerator 2) * ((sylowGenerator 0) * ((sylowGenerator 3) * ((sylowGenerator 2)))))

private def ob94M3 : QuotientMatrix := quotientDecode #v[110, 2621, 2181, 1716, 705, 2797, 2784, 316, 669, 394, 1047, 251]

private theorem ob94_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] = ob94M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob94M2 : QuotientMatrix := quotientDecode #v[2269, 2621, 3069, 1262, 2314, 3413, 3416, 1668, 1317, 4003, 1047, 899]

private theorem ob94_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * ob94M3 = ob94M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob94M1 : QuotientMatrix := quotientDecode #v[2640, 424, 3503, 1007, 1600, 1639, 581, 3843, 2940, 506, 1047, 489]

private theorem ob94_mul1 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * ob94M2 = ob94M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob94M0 : QuotientMatrix := quotientDecode #v[1725, 399, 1283, 2485, 107, 177, 1223, 586, 3418, 4078, 1976, 1839]

private theorem ob94_mul0 : quotientDecode #v[3801, 50, 713, 1964, 2970, 1379, 3420, 930, 2338, 2643, 602, 2393] * ob94M1 = ob94M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob94_value : value (obstruction94) = ob94M0 := by
  simp only [obstruction94, r94_value, s2_value, s0_value, s3_value, map_mul]
  change quotientDecode #v[3801, 50, 713, 1964, 2970, 1379, 3420, 930, 2338, 2643, 602, 2393] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184])))) = _
  rw [ob94_mul3, ob94_mul2, ob94_mul1, ob94_mul0]

private theorem obstruction94_mem : obstruction94 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 94)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 94)).mul_mem (representative_mem_join 94) ((baseSubgroup ⊔ Subgroup.zpowers (representative 94)).mul_mem (sylow_mem_join 94 2) ((baseSubgroup ⊔ Subgroup.zpowers (representative 94)).mul_mem (sylow_mem_join 94 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 94)).mul_mem (sylow_mem_join 94 3) (sylow_mem_join 94 2)))))

private def ob94Power2 : QuotientMatrix := quotientDecode #v[205, 1172, 3536, 2907, 2801, 1069, 772, 787, 347, 2342, 3625, 3641]

private theorem ob94_power2 : value (obstruction94 ^ 2) = ob94Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob94_value) (by rw [pow_one]; exact ob94_value)
  intro i
  fin_cases i <;> rfl

private def ob94Power3 : QuotientMatrix := quotientDecode #v[3206, 154, 2859, 4016, 2091, 3330, 1975, 1517, 1905, 3656, 192, 171]

private theorem ob94_power3 : value (obstruction94 ^ 3) = ob94Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob94_value) ob94_power2
  intro i
  fin_cases i <;> rfl

private def ob94Power4 : QuotientMatrix := quotientDecode #v[1617, 2587, 2989, 179, 2329, 3138, 1453, 1749, 1964, 523, 1677, 3196]

private theorem ob94_power4 : value (obstruction94 ^ 4) = ob94Power4 := by
  apply power_step _ 2 2 _ _ _ ob94_power2 ob94_power2
  intro i
  fin_cases i <;> rfl

private def ob94Power7 : QuotientMatrix := quotientDecode #v[3474, 1380, 2400, 3288, 3271, 1862, 1859, 852, 1421, 3556, 888, 1646]

private theorem ob94_power7 : value (obstruction94 ^ 7) = ob94Power7 := by
  apply power_step _ 3 4 _ _ _ ob94_power3 ob94_power4
  intro i
  fin_cases i <;> rfl

private def ob94Power8 : QuotientMatrix := quotientDecode #v[3683, 2967, 3587, 4036, 1067, 1351, 1785, 795, 675, 3826, 3868, 281]

private theorem ob94_power8 : value (obstruction94 ^ 8) = ob94Power8 := by
  apply power_step _ 4 4 _ _ _ ob94_power4 ob94_power4
  intro i
  fin_cases i <;> rfl

private def ob94Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob94_power15 : value (obstruction94 ^ 15) = ob94Power15 := by
  apply power_step _ 7 8 _ _ _ ob94_power7 ob94_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction94_small_power : (obstruction94 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction94 ^ 15) = 1
  rw [ob94_power15]
  exact decode_identity

private theorem obstruction94_nonidentity : obstruction94 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob94_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3206, 154, 2859, 4016, 2091, 3330, 1975, 1517, 1905, 3656, 192, 171]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative94 :
    representative 94 ∈ involutionMatrixLineStabilizer ∨
    representative 94 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 94), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction94 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 94)).pow_mem obstruction94_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction94_small_power obstruction94_nonidentity

private theorem r95_value : value (representative 95) = wordMatrix437 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix437_expansion.symm

private def obstruction95 : quotientSubgroup := (representative 95) * ((sylowGenerator 3) * ((sylowGenerator 1) * ((sylowGenerator 3))))

private def ob95M2 : QuotientMatrix := quotientDecode #v[1315, 703, 679, 1669, 1324, 254, 3774, 2665, 1908, 3570, 1024, 1172]

private theorem ob95_mul2 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] = ob95M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob95M1 : QuotientMatrix := quotientDecode #v[2640, 3249, 33, 2031, 1751, 752, 1605, 2836, 754, 2147, 1047, 3303]

private theorem ob95_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob95M2 = ob95M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob95M0 : QuotientMatrix := quotientDecode #v[2889, 3238, 3164, 2450, 1216, 3225, 331, 2836, 835, 2486, 3250, 2020]

private theorem ob95_mul0 : quotientDecode #v[29, 21, 4027, 1782, 2374, 2489, 3357, 128, 947, 3489, 3954, 2199] * ob95M1 = ob95M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob95_value : value (obstruction95) = ob95M0 := by
  simp only [obstruction95, r95_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[29, 21, 4027, 1782, 2374, 2489, 3357, 128, 947, 3489, 3954, 2199] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100]))) = _
  rw [ob95_mul2, ob95_mul1, ob95_mul0]

private theorem obstruction95_mem : obstruction95 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 95)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 95)).mul_mem (representative_mem_join 95) ((baseSubgroup ⊔ Subgroup.zpowers (representative 95)).mul_mem (sylow_mem_join 95 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 95)).mul_mem (sylow_mem_join 95 1) (sylow_mem_join 95 3))))

private def ob95Power2 : QuotientMatrix := quotientDecode #v[3713, 3105, 2835, 2005, 1773, 1625, 3189, 1421, 3153, 1808, 1213, 3293]

private theorem ob95_power2 : value (obstruction95 ^ 2) = ob95Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob95_value) (by rw [pow_one]; exact ob95_value)
  intro i
  fin_cases i <;> rfl

private def ob95Power3 : QuotientMatrix := quotientDecode #v[701, 3206, 3646, 4045, 3397, 596, 1361, 2658, 1428, 647, 376, 2894]

private theorem ob95_power3 : value (obstruction95 ^ 3) = ob95Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob95_value) ob95_power2
  intro i
  fin_cases i <;> rfl

private def ob95Power4 : QuotientMatrix := quotientDecode #v[1148, 184, 977, 1403, 3659, 97, 307, 3878, 3193, 2321, 963, 1330]

private theorem ob95_power4 : value (obstruction95 ^ 4) = ob95Power4 := by
  apply power_step _ 2 2 _ _ _ ob95_power2 ob95_power2
  intro i
  fin_cases i <;> rfl

private def ob95Power7 : QuotientMatrix := quotientDecode #v[2763, 2750, 2008, 3930, 3094, 1464, 1214, 3529, 3334, 290, 1563, 1915]

private theorem ob95_power7 : value (obstruction95 ^ 7) = ob95Power7 := by
  apply power_step _ 3 4 _ _ _ ob95_power3 ob95_power4
  intro i
  fin_cases i <;> rfl

private def ob95Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob95_power14 : value (obstruction95 ^ 14) = ob95Power14 := by
  apply power_step _ 7 7 _ _ _ ob95_power7 ob95_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction95_small_power : (obstruction95 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction95 ^ 14) = 1
  rw [ob95_power14]
  exact decode_identity

private theorem obstruction95_nonidentity : obstruction95 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob95_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 7) h
  have hn : (quotientDecode #v[3713, 3105, 2835, 2005, 1773, 1625, 3189, 1421, 3153, 1808, 1213, 3293]) 0 7 ≠ (1 : QuotientMatrix) 0 7 := by decide +kernel
  exact hn hc

theorem alternative95 :
    representative 95 ∈ involutionMatrixLineStabilizer ∨
    representative 95 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 95), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction95 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 95)).pow_mem obstruction95_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction95_small_power obstruction95_nonidentity

private theorem r96_value : value (representative 96) = wordMatrix441 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix441_expansion.symm

private def obstruction96 : quotientSubgroup := (representative 96) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob96M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob96_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob96M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob96M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob96_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob96M3 = ob96M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob96M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob96_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob96M2 = ob96M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob96M0 : QuotientMatrix := quotientDecode #v[2048, 2734, 963, 2739, 1935, 2188, 2928, 1962, 1538, 3566, 2930, 4047]

private theorem ob96_mul0 : quotientDecode #v[1550, 3450, 3273, 1436, 328, 83, 2918, 3696, 1221, 2507, 2439, 3204] * ob96M1 = ob96M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob96_value : value (obstruction96) = ob96M0 := by
  simp only [obstruction96, r96_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[1550, 3450, 3273, 1436, 328, 83, 2918, 3696, 1221, 2507, 2439, 3204] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob96_mul3, ob96_mul2, ob96_mul1, ob96_mul0]

private theorem obstruction96_mem : obstruction96 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 96)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 96)).mul_mem (representative_mem_join 96) ((baseSubgroup ⊔ Subgroup.zpowers (representative 96)).mul_mem (sylow_mem_join 96 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 96)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 96)).inv_mem (sylow_mem_join 96 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 96)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 96)).inv_mem (sylow_mem_join 96 2)) (sylow_mem_join 96 1)))))

private def ob96Power2 : QuotientMatrix := quotientDecode #v[4047, 3801, 1432, 2086, 3306, 277, 80, 4005, 3122, 1335, 2814, 2133]

private theorem ob96_power2 : value (obstruction96 ^ 2) = ob96Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob96_value) (by rw [pow_one]; exact ob96_value)
  intro i
  fin_cases i <;> rfl

private def ob96Power3 : QuotientMatrix := quotientDecode #v[2133, 181, 2022, 3630, 246, 2638, 3327, 2996, 272, 798, 550, 2291]

private theorem ob96_power3 : value (obstruction96 ^ 3) = ob96Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob96_value) ob96_power2
  intro i
  fin_cases i <;> rfl

private def ob96Power4 : QuotientMatrix := quotientDecode #v[2291, 874, 3493, 513, 2740, 2703, 3258, 3913, 397, 4029, 3087, 3768]

private theorem ob96_power4 : value (obstruction96 ^ 4) = ob96Power4 := by
  apply power_step _ 2 2 _ _ _ ob96_power2 ob96_power2
  intro i
  fin_cases i <;> rfl

private def ob96Power8 : QuotientMatrix := quotientDecode #v[1769, 2414, 938, 1870, 978, 2673, 3246, 2767, 2451, 1186, 1674, 121]

private theorem ob96_power8 : value (obstruction96 ^ 8) = ob96Power8 := by
  apply power_step _ 4 4 _ _ _ ob96_power4 ob96_power4
  intro i
  fin_cases i <;> rfl

private def ob96Power16 : QuotientMatrix := quotientDecode #v[3999, 703, 943, 2719, 492, 1855, 3015, 2521, 3952, 3930, 1735, 1194]

private theorem ob96_power16 : value (obstruction96 ^ 16) = ob96Power16 := by
  apply power_step _ 8 8 _ _ _ ob96_power8 ob96_power8
  intro i
  fin_cases i <;> rfl

private def ob96Power5 : QuotientMatrix := quotientDecode #v[3768, 2061, 1626, 1518, 2379, 3669, 3081, 1682, 216, 1672, 3939, 2889]

private theorem ob96_power5 : value (obstruction96 ^ 5) = ob96Power5 := by
  apply power_step _ 2 3 _ _ _ ob96_power2 ob96_power3
  intro i
  fin_cases i <;> rfl

private def ob96Power9 : QuotientMatrix := quotientDecode #v[121, 2543, 1239, 2096, 2583, 3666, 2117, 1317, 2886, 3834, 299, 1728]

private theorem ob96_power9 : value (obstruction96 ^ 9) = ob96Power9 := by
  apply power_step _ 4 5 _ _ _ ob96_power4 ob96_power5
  intro i
  fin_cases i <;> rfl

private def ob96Power17 : QuotientMatrix := quotientDecode #v[1194, 3737, 3860, 2522, 2852, 1091, 2452, 43, 2850, 947, 2859, 1097]

private theorem ob96_power17 : value (obstruction96 ^ 17) = ob96Power17 := by
  apply power_step _ 8 9 _ _ _ ob96_power8 ob96_power9
  intro i
  fin_cases i <;> rfl

private def ob96Power33 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob96_power33 : value (obstruction96 ^ 33) = ob96Power33 := by
  apply power_step _ 16 17 _ _ _ ob96_power16 ob96_power17
  intro i
  fin_cases i <;> rfl

private theorem obstruction96_small_power : (obstruction96 ^ 3) ^ 11 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction96 ^ 33) = 1
  rw [ob96_power33]
  exact decode_identity

private theorem obstruction96_nonidentity : obstruction96 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob96_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[2133, 181, 2022, 3630, 246, 2638, 3327, 2996, 272, 798, 550, 2291]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative96 :
    representative 96 ∈ involutionMatrixLineStabilizer ∨
    representative 96 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 96), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction96 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 96)).pow_mem obstruction96_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 11 (by decide +kernel)
    obstruction96_small_power obstruction96_nonidentity

private theorem r97_value : value (representative 97) = wordMatrix445 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix445_expansion.symm

private theorem r97_inverse_value :
    value ((representative 97)⁻¹) = quotientDecode #v[3369, 205, 690, 2132, 2902, 583, 3831, 1958, 872, 3085, 1047, 1276] := by
  apply inverse_value _ _ _ r97_value
  intro i
  fin_cases i <;> rfl

theorem r97_line : representative 97 ∈ involutionMatrixLineStabilizer := by
  apply line_mem_of_inverse _ _ 1024 1047 23 r97_inverse_value
  · rfl
  · rfl
  · rfl
  · change {involutionMatrixVector 1024, involutionMatrixVector 1047,
      involutionMatrixVector 23} =
      {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]

theorem alternative97 :
    representative 97 ∈ involutionMatrixLineStabilizer ∨
    representative 97 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 97), x ^ 2304 ≠ 1 := by
  exact Or.inl r97_line

private theorem r98_value : value (representative 98) = wordMatrix450 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix450_expansion.symm

private theorem r98_inverse_value :
    value ((representative 98)⁻¹) = quotientDecode #v[3801, 1215, 1171, 2107, 2786, 3246, 3979, 1152, 407, 1811, 1024, 1049] := by
  apply inverse_value _ _ _ r98_value
  intro i
  fin_cases i <;> rfl

theorem r98_line : representative 98 ∈ involutionMatrixLineStabilizer := by
  apply line_mem_of_inverse _ _ 1047 1024 23 r98_inverse_value
  · rfl
  · rfl
  · rfl
  · change {involutionMatrixVector 1047, involutionMatrixVector 1024,
      involutionMatrixVector 23} =
      {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]

theorem alternative98 :
    representative 98 ∈ involutionMatrixLineStabilizer ∨
    representative 98 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 98), x ^ 2304 ≠ 1 := by
  exact Or.inl r98_line

private theorem r99_value : value (representative 99) = wordMatrix453 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix453_expansion.symm

private theorem r99_inverse_value :
    value ((representative 99)⁻¹) = quotientDecode #v[1950, 21, 1409, 2567, 541, 715, 1831, 3058, 1400, 3305, 1024, 1287] := by
  apply inverse_value _ _ _ r99_value
  intro i
  fin_cases i <;> rfl

theorem r99_line : representative 99 ∈ involutionMatrixLineStabilizer := by
  apply line_mem_of_inverse _ _ 23 1024 1047 r99_inverse_value
  · rfl
  · rfl
  · rfl
  · change {involutionMatrixVector 23, involutionMatrixVector 1024,
      involutionMatrixVector 1047} =
      {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]

theorem alternative99 :
    representative 99 ∈ involutionMatrixLineStabilizer ∨
    representative 99 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 99), x ^ 2304 ≠ 1 := by
  exact Or.inl r99_line


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
