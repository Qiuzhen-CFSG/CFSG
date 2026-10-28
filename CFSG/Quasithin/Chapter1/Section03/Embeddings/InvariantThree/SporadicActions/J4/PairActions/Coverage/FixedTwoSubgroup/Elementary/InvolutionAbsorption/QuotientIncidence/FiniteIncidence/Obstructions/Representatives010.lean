module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second
import Mathlib.Tactic.FinCases

/-!
# The representative alternatives at indices 10 through 19

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

private theorem r10_value : value (representative 10) = wordMatrix104 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix104_expansion.symm

private def obstruction10 : quotientSubgroup := (representative 10) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob10M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob10_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob10M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob10M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob10_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob10M3 = ob10M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob10M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob10_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob10M2 = ob10M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob10M0 : QuotientMatrix := quotientDecode #v[2164, 2251, 995, 1238, 1019, 839, 12, 2332, 3789, 1013, 2512, 3933]

private theorem ob10_mul0 : quotientDecode #v[2118, 2995, 306, 332, 2839, 132, 596, 3384, 1842, 2978, 167, 2649] * ob10M1 = ob10M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob10_value : value (obstruction10) = ob10M0 := by
  simp only [obstruction10, r10_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2118, 2995, 306, 332, 2839, 132, 596, 3384, 1842, 2978, 167, 2649] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob10_mul3, ob10_mul2, ob10_mul1, ob10_mul0]

private theorem obstruction10_mem : obstruction10 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 10)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 10)).mul_mem (representative_mem_join 10) ((baseSubgroup ⊔ Subgroup.zpowers (representative 10)).mul_mem (sylow_mem_join 10 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 10)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 10)).inv_mem (sylow_mem_join 10 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 10)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 10)).inv_mem (sylow_mem_join 10 2)) (sylow_mem_join 10 1)))))

private def ob10Power2 : QuotientMatrix := quotientDecode #v[3086, 548, 2000, 2067, 253, 3688, 1845, 1374, 809, 3843, 2939, 1795]

private theorem ob10_power2 : value (obstruction10 ^ 2) = ob10Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob10_value) (by rw [pow_one]; exact ob10_value)
  intro i
  fin_cases i <;> rfl

private def ob10Power3 : QuotientMatrix := quotientDecode #v[2419, 849, 3587, 3097, 1773, 741, 4035, 2836, 733, 2826, 1724, 1111]

private theorem ob10_power3 : value (obstruction10 ^ 3) = ob10Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob10_value) ob10_power2
  intro i
  fin_cases i <;> rfl

private def ob10Power4 : QuotientMatrix := quotientDecode #v[415, 1723, 1479, 2516, 3891, 565, 538, 637, 1631, 3704, 1200, 2427]

private theorem ob10_power4 : value (obstruction10 ^ 4) = ob10Power4 := by
  apply power_step _ 2 2 _ _ _ ob10_power2 ob10_power2
  intro i
  fin_cases i <;> rfl

private def ob10Power7 : QuotientMatrix := quotientDecode #v[1820, 1169, 1175, 2739, 1302, 2162, 687, 2984, 3232, 3635, 2464, 2938]

private theorem ob10_power7 : value (obstruction10 ^ 7) = ob10Power7 := by
  apply power_step _ 3 4 _ _ _ ob10_power3 ob10_power4
  intro i
  fin_cases i <;> rfl

private def ob10Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob10_power14 : value (obstruction10 ^ 14) = ob10Power14 := by
  apply power_step _ 7 7 _ _ _ ob10_power7 ob10_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction10_small_power : (obstruction10 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction10 ^ 14) = 1
  rw [ob10_power14]
  exact decode_identity

private theorem obstruction10_nonidentity : obstruction10 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob10_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3086, 548, 2000, 2067, 253, 3688, 1845, 1374, 809, 3843, 2939, 1795]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative10 :
    representative 10 ∈ involutionMatrixLineStabilizer ∨
    representative 10 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 10), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction10 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 10)).pow_mem obstruction10_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction10_small_power obstruction10_nonidentity

private theorem r11_value : value (representative 11) = wordMatrix108 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix108_expansion.symm

private def obstruction11 : quotientSubgroup := (representative 11) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob11M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob11_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob11M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob11M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob11_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob11M3 = ob11M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob11M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob11_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob11M2 = ob11M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob11M0 : QuotientMatrix := quotientDecode #v[4023, 2768, 1954, 1003, 610, 134, 1649, 3308, 1774, 336, 2423, 2849]

private theorem ob11_mul0 : quotientDecode #v[152, 3011, 1120, 2850, 1771, 3756, 2735, 637, 1185, 672, 2423, 2582] * ob11M1 = ob11M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob11_value : value (obstruction11) = ob11M0 := by
  simp only [obstruction11, r11_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[152, 3011, 1120, 2850, 1771, 3756, 2735, 637, 1185, 672, 2423, 2582] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob11_mul3, ob11_mul2, ob11_mul1, ob11_mul0]

private theorem obstruction11_mem : obstruction11 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 11)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 11)).mul_mem (representative_mem_join 11) ((baseSubgroup ⊔ Subgroup.zpowers (representative 11)).mul_mem (sylow_mem_join 11 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 11)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 11)).inv_mem (sylow_mem_join 11 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 11)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 11)).inv_mem (sylow_mem_join 11 2)) (sylow_mem_join 11 1)))))

private def ob11Power2 : QuotientMatrix := quotientDecode #v[2341, 654, 2163, 2857, 3447, 414, 773, 3076, 3237, 765, 2975, 942]

private theorem ob11_power2 : value (obstruction11 ^ 2) = ob11Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob11_value) (by rw [pow_one]; exact ob11_value)
  intro i
  fin_cases i <;> rfl

private def ob11Power3 : QuotientMatrix := quotientDecode #v[1372, 805, 2771, 69, 744, 1785, 4011, 1524, 1577, 727, 831, 1357]

private theorem ob11_power3 : value (obstruction11 ^ 3) = ob11Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob11_value) ob11_power2
  intro i
  fin_cases i <;> rfl

private def ob11Power5 : QuotientMatrix := quotientDecode #v[2578, 3728, 2190, 595, 1867, 2182, 2929, 3233, 2800, 851, 2624, 3648]

private theorem ob11_power5 : value (obstruction11 ^ 5) = ob11Power5 := by
  apply power_step _ 2 3 _ _ _ ob11_power2 ob11_power3
  intro i
  fin_cases i <;> rfl

private def ob11Power6 : QuotientMatrix := quotientDecode #v[707, 3464, 2388, 36, 3636, 2751, 1981, 395, 520, 1738, 3072, 1399]

private theorem ob11_power6 : value (obstruction11 ^ 6) = ob11Power6 := by
  apply power_step _ 3 3 _ _ _ ob11_power3 ob11_power3
  intro i
  fin_cases i <;> rfl

private def ob11Power11 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob11_power11 : value (obstruction11 ^ 11) = ob11Power11 := by
  apply power_step _ 5 6 _ _ _ ob11_power5 ob11_power6
  intro i
  fin_cases i <;> rfl

private theorem obstruction11_small_power : (obstruction11 ^ 1) ^ 11 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction11 ^ 11) = 1
  rw [ob11_power11]
  exact decode_identity

private theorem obstruction11_nonidentity : obstruction11 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob11_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[4023, 2768, 1954, 1003, 610, 134, 1649, 3308, 1774, 336, 2423, 2849]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative11 :
    representative 11 ∈ involutionMatrixLineStabilizer ∨
    representative 11 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 11), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction11 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 11)).pow_mem obstruction11_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 11 (by decide +kernel)
    obstruction11_small_power obstruction11_nonidentity

private theorem r12_value : value (representative 12) = wordMatrix113 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix113_expansion.symm

private def obstruction12 : quotientSubgroup := (representative 12) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 3) * ((sylowGenerator 1)))))

private def ob12M3 : QuotientMatrix := quotientDecode #v[1315, 3788, 3161, 658, 1953, 612, 2750, 3689, 2461, 795, 1024, 3312]

private theorem ob12_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob12M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob12M2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem ob12_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob12M3 = ob12M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob12M1 : QuotientMatrix := quotientDecode #v[2704, 1044, 1492, 2567, 2887, 649, 4053, 1033, 1232, 4003, 1047, 251]

private theorem ob12_mul1 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob12M2 = ob12M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob12M0 : QuotientMatrix := quotientDecode #v[1812, 1879, 3568, 3582, 3094, 3614, 1529, 3032, 1491, 39, 1305, 2607]

private theorem ob12_mul0 : quotientDecode #v[2918, 177, 1954, 2558, 237, 2644, 3423, 3593, 2767, 3534, 1425, 2333] * ob12M1 = ob12M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob12_value : value (obstruction12) = ob12M0 := by
  simp only [obstruction12, r12_value, s1_inverse_value, s2_inverse_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[2918, 177, 1954, 2558, 237, 2644, 3423, 3593, 2767, 3534, 1425, 2333] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob12_mul3, ob12_mul2, ob12_mul1, ob12_mul0]

private theorem obstruction12_mem : obstruction12 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 12)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 12)).mul_mem (representative_mem_join 12) ((baseSubgroup ⊔ Subgroup.zpowers (representative 12)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 12)).inv_mem (sylow_mem_join 12 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 12)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 12)).inv_mem (sylow_mem_join 12 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 12)).mul_mem (sylow_mem_join 12 3) (sylow_mem_join 12 1)))))

private def ob12Power2 : QuotientMatrix := quotientDecode #v[267, 1201, 1740, 405, 2439, 1118, 1545, 18, 702, 941, 1590, 1115]

private theorem ob12_power2 : value (obstruction12 ^ 2) = ob12Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob12_value) (by rw [pow_one]; exact ob12_value)
  intro i
  fin_cases i <;> rfl

private def ob12Power3 : QuotientMatrix := quotientDecode #v[2158, 3037, 2833, 2297, 2455, 2991, 4052, 2881, 3758, 1832, 3473, 331]

private theorem ob12_power3 : value (obstruction12 ^ 3) = ob12Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob12_value) ob12_power2
  intro i
  fin_cases i <;> rfl

private def ob12Power4 : QuotientMatrix := quotientDecode #v[1681, 2806, 1241, 3308, 1409, 2640, 1285, 3382, 3470, 781, 2623, 3479]

private theorem ob12_power4 : value (obstruction12 ^ 4) = ob12Power4 := by
  apply power_step _ 2 2 _ _ _ ob12_power2 ob12_power2
  intro i
  fin_cases i <;> rfl

private def ob12Power7 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob12_power7 : value (obstruction12 ^ 7) = ob12Power7 := by
  apply power_step _ 3 4 _ _ _ ob12_power3 ob12_power4
  intro i
  fin_cases i <;> rfl

private theorem obstruction12_small_power : (obstruction12 ^ 1) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction12 ^ 7) = 1
  rw [ob12_power7]
  exact decode_identity

private theorem obstruction12_nonidentity : obstruction12 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob12_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1812, 1879, 3568, 3582, 3094, 3614, 1529, 3032, 1491, 39, 1305, 2607]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative12 :
    representative 12 ∈ involutionMatrixLineStabilizer ∨
    representative 12 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 12), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction12 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 12)).pow_mem obstruction12_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction12_small_power obstruction12_nonidentity

private theorem r13_value : value (representative 13) = wordMatrix118 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix118_expansion.symm

private def obstruction13 : quotientSubgroup := (representative 13) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob13M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob13_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob13M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob13M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob13_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob13M3 = ob13M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob13M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob13_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob13M2 = ob13M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob13M0 : QuotientMatrix := quotientDecode #v[3713, 3822, 158, 2611, 974, 2015, 3249, 852, 3042, 3642, 3650, 752]

private theorem ob13_mul0 : quotientDecode #v[3748, 687, 1161, 405, 1050, 2751, 345, 2263, 3515, 1301, 2313, 54] * ob13M1 = ob13M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob13_value : value (obstruction13) = ob13M0 := by
  simp only [obstruction13, r13_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3748, 687, 1161, 405, 1050, 2751, 345, 2263, 3515, 1301, 2313, 54] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob13_mul3, ob13_mul2, ob13_mul1, ob13_mul0]

private theorem obstruction13_mem : obstruction13 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 13)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 13)).mul_mem (representative_mem_join 13) ((baseSubgroup ⊔ Subgroup.zpowers (representative 13)).mul_mem (sylow_mem_join 13 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 13)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 13)).inv_mem (sylow_mem_join 13 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 13)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 13)).inv_mem (sylow_mem_join 13 2)) (sylow_mem_join 13 1)))))

private def ob13Power2 : QuotientMatrix := quotientDecode #v[3933, 3825, 1241, 2228, 3710, 3443, 1398, 2617, 508, 580, 215, 1486]

private theorem ob13_power2 : value (obstruction13 ^ 2) = ob13Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob13_value) (by rw [pow_one]; exact ob13_value)
  intro i
  fin_cases i <;> rfl

private def ob13Power3 : QuotientMatrix := quotientDecode #v[569, 2045, 1755, 1323, 3691, 3999, 880, 3177, 2747, 533, 3290, 3590]

private theorem ob13_power3 : value (obstruction13 ^ 3) = ob13Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob13_value) ob13_power2
  intro i
  fin_cases i <;> rfl

private def ob13Power5 : QuotientMatrix := quotientDecode #v[1696, 3101, 2746, 1344, 1600, 3879, 1475, 2805, 1958, 1982, 621, 3445]

private theorem ob13_power5 : value (obstruction13 ^ 5) = ob13Power5 := by
  apply power_step _ 2 3 _ _ _ ob13_power2 ob13_power3
  intro i
  fin_cases i <;> rfl

private def ob13Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob13_power10 : value (obstruction13 ^ 10) = ob13Power10 := by
  apply power_step _ 5 5 _ _ _ ob13_power5 ob13_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction13_small_power : (obstruction13 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction13 ^ 10) = 1
  rw [ob13_power10]
  exact decode_identity

private theorem obstruction13_nonidentity : obstruction13 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob13_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[3933, 3825, 1241, 2228, 3710, 3443, 1398, 2617, 508, 580, 215, 1486]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative13 :
    representative 13 ∈ involutionMatrixLineStabilizer ∨
    representative 13 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 13), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction13 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 13)).pow_mem obstruction13_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction13_small_power obstruction13_nonidentity

private theorem r14_value : value (representative 14) = wordMatrix123 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix123_expansion.symm

private def obstruction14 : quotientSubgroup := (representative 14) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob14M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob14_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob14M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob14M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob14_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob14M3 = ob14M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob14M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob14_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob14M2 = ob14M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob14M0 : QuotientMatrix := quotientDecode #v[3709, 2592, 330, 3052, 2088, 1588, 1541, 1801, 316, 1114, 2623, 3679]

private theorem ob14_mul0 : quotientDecode #v[3829, 2502, 2660, 3342, 485, 942, 1255, 4068, 1741, 1809, 961, 495] * ob14M1 = ob14M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob14_value : value (obstruction14) = ob14M0 := by
  simp only [obstruction14, r14_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3829, 2502, 2660, 3342, 485, 942, 1255, 4068, 1741, 1809, 961, 495] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob14_mul3, ob14_mul2, ob14_mul1, ob14_mul0]

private theorem obstruction14_mem : obstruction14 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 14)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 14)).mul_mem (representative_mem_join 14) ((baseSubgroup ⊔ Subgroup.zpowers (representative 14)).mul_mem (sylow_mem_join 14 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 14)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 14)).inv_mem (sylow_mem_join 14 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 14)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 14)).inv_mem (sylow_mem_join 14 2)) (sylow_mem_join 14 1)))))

private def ob14Power2 : QuotientMatrix := quotientDecode #v[3320, 3121, 1781, 1703, 903, 307, 338, 2760, 1414, 1502, 2786, 236]

private theorem ob14_power2 : value (obstruction14 ^ 2) = ob14Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob14_value) (by rw [pow_one]; exact ob14_value)
  intro i
  fin_cases i <;> rfl

private def ob14Power3 : QuotientMatrix := quotientDecode #v[156, 1025, 3650, 2639, 1912, 2941, 1329, 229, 1888, 673, 1821, 3486]

private theorem ob14_power3 : value (obstruction14 ^ 3) = ob14Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob14_value) ob14_power2
  intro i
  fin_cases i <;> rfl

private def ob14Power5 : QuotientMatrix := quotientDecode #v[2333, 1562, 691, 1275, 4091, 4088, 296, 164, 2779, 733, 1431, 2724]

private theorem ob14_power5 : value (obstruction14 ^ 5) = ob14Power5 := by
  apply power_step _ 2 3 _ _ _ ob14_power2 ob14_power3
  intro i
  fin_cases i <;> rfl

private def ob14Power10 : QuotientMatrix := quotientDecode #v[209, 2640, 3453, 4068, 3398, 577, 472, 3567, 3570, 1023, 3495, 1430]

private theorem ob14_power10 : value (obstruction14 ^ 10) = ob14Power10 := by
  apply power_step _ 5 5 _ _ _ ob14_power5 ob14_power5
  intro i
  fin_cases i <;> rfl

private def ob14Power6 : QuotientMatrix := quotientDecode #v[912, 1921, 2322, 2718, 423, 1530, 3300, 119, 3216, 2469, 309, 2674]

private theorem ob14_power6 : value (obstruction14 ^ 6) = ob14Power6 := by
  apply power_step _ 3 3 _ _ _ ob14_power3 ob14_power3
  intro i
  fin_cases i <;> rfl

private def ob14Power11 : QuotientMatrix := quotientDecode #v[1881, 1064, 2462, 1908, 2099, 3106, 1012, 3231, 108, 1165, 374, 3912]

private theorem ob14_power11 : value (obstruction14 ^ 11) = ob14Power11 := by
  apply power_step _ 5 6 _ _ _ ob14_power5 ob14_power6
  intro i
  fin_cases i <;> rfl

private def ob14Power21 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob14_power21 : value (obstruction14 ^ 21) = ob14Power21 := by
  apply power_step _ 10 11 _ _ _ ob14_power10 ob14_power11
  intro i
  fin_cases i <;> rfl

private theorem obstruction14_small_power : (obstruction14 ^ 3) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction14 ^ 21) = 1
  rw [ob14_power21]
  exact decode_identity

private theorem obstruction14_nonidentity : obstruction14 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob14_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[156, 1025, 3650, 2639, 1912, 2941, 1329, 229, 1888, 673, 1821, 3486]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative14 :
    representative 14 ∈ involutionMatrixLineStabilizer ∨
    representative 14 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 14), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction14 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 14)).pow_mem obstruction14_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction14_small_power obstruction14_nonidentity

private theorem r15_value : value (representative 15) = wordMatrix127 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix127_expansion.symm

private def obstruction15 : quotientSubgroup := (representative 15) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob15M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob15_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob15M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob15M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob15_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob15M3 = ob15M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob15M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob15_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob15M2 = ob15M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob15M0 : QuotientMatrix := quotientDecode #v[3774, 3649, 3934, 1193, 670, 2383, 401, 526, 394, 1104, 1792, 3775]

private theorem ob15_mul0 : quotientDecode #v[2392, 367, 575, 3442, 1722, 3753, 2028, 646, 1455, 4064, 3955, 991] * ob15M1 = ob15M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob15_value : value (obstruction15) = ob15M0 := by
  simp only [obstruction15, r15_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2392, 367, 575, 3442, 1722, 3753, 2028, 646, 1455, 4064, 3955, 991] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob15_mul3, ob15_mul2, ob15_mul1, ob15_mul0]

private theorem obstruction15_mem : obstruction15 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 15)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 15)).mul_mem (representative_mem_join 15) ((baseSubgroup ⊔ Subgroup.zpowers (representative 15)).mul_mem (sylow_mem_join 15 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 15)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 15)).inv_mem (sylow_mem_join 15 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 15)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 15)).inv_mem (sylow_mem_join 15 2)) (sylow_mem_join 15 1)))))

private def ob15Power2 : QuotientMatrix := quotientDecode #v[390, 704, 2780, 1622, 374, 1452, 4004, 486, 2412, 1039, 730, 3896]

private theorem ob15_power2 : value (obstruction15 ^ 2) = ob15Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob15_value) (by rw [pow_one]; exact ob15_value)
  intro i
  fin_cases i <;> rfl

private def ob15Power3 : QuotientMatrix := quotientDecode #v[667, 1999, 25, 320, 2773, 1596, 2170, 2629, 3100, 3080, 4025, 797]

private theorem ob15_power3 : value (obstruction15 ^ 3) = ob15Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob15_value) ob15_power2
  intro i
  fin_cases i <;> rfl

private def ob15Power5 : QuotientMatrix := quotientDecode #v[399, 3639, 1702, 1736, 3929, 3717, 208, 4041, 30, 2996, 621, 281]

private theorem ob15_power5 : value (obstruction15 ^ 5) = ob15Power5 := by
  apply power_step _ 2 3 _ _ _ ob15_power2 ob15_power3
  intro i
  fin_cases i <;> rfl

private def ob15Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob15_power10 : value (obstruction15 ^ 10) = ob15Power10 := by
  apply power_step _ 5 5 _ _ _ ob15_power5 ob15_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction15_small_power : (obstruction15 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction15 ^ 10) = 1
  rw [ob15_power10]
  exact decode_identity

private theorem obstruction15_nonidentity : obstruction15 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob15_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[390, 704, 2780, 1622, 374, 1452, 4004, 486, 2412, 1039, 730, 3896]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative15 :
    representative 15 ∈ involutionMatrixLineStabilizer ∨
    representative 15 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 15), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction15 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 15)).pow_mem obstruction15_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction15_small_power obstruction15_nonidentity

private theorem r16_value : value (representative 16) = wordMatrix133 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix133_expansion.symm

private def obstruction16 : quotientSubgroup := (representative 16) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob16M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob16_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob16M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob16M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob16_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob16M3 = ob16M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob16M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob16_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob16M2 = ob16M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob16M0 : QuotientMatrix := quotientDecode #v[701, 808, 1125, 44, 1479, 3555, 1541, 1052, 1598, 189, 511, 3432]

private theorem ob16_mul0 : quotientDecode #v[807, 3215, 237, 4015, 681, 280, 1255, 1654, 2911, 276, 352, 1895] * ob16M1 = ob16M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob16_value : value (obstruction16) = ob16M0 := by
  simp only [obstruction16, r16_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[807, 3215, 237, 4015, 681, 280, 1255, 1654, 2911, 276, 352, 1895] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob16_mul3, ob16_mul2, ob16_mul1, ob16_mul0]

private theorem obstruction16_mem : obstruction16 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 16)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 16)).mul_mem (representative_mem_join 16) ((baseSubgroup ⊔ Subgroup.zpowers (representative 16)).mul_mem (sylow_mem_join 16 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 16)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 16)).inv_mem (sylow_mem_join 16 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 16)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 16)).inv_mem (sylow_mem_join 16 2)) (sylow_mem_join 16 1)))))

private def ob16Power2 : QuotientMatrix := quotientDecode #v[2673, 2892, 3265, 2474, 40, 1222, 1946, 113, 3591, 2764, 2527, 355]

private theorem ob16_power2 : value (obstruction16 ^ 2) = ob16Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob16_value) (by rw [pow_one]; exact ob16_value)
  intro i
  fin_cases i <;> rfl

private def ob16Power3 : QuotientMatrix := quotientDecode #v[329, 2471, 3123, 429, 3535, 1195, 1443, 3228, 2522, 2949, 2388, 3149]

private theorem ob16_power3 : value (obstruction16 ^ 3) = ob16Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob16_value) ob16_power2
  intro i
  fin_cases i <;> rfl

private def ob16Power4 : QuotientMatrix := quotientDecode #v[682, 1881, 1318, 2357, 3436, 2489, 4011, 2309, 3980, 2351, 3313, 3174]

private theorem ob16_power4 : value (obstruction16 ^ 4) = ob16Power4 := by
  apply power_step _ 2 2 _ _ _ ob16_power2 ob16_power2
  intro i
  fin_cases i <;> rfl

private def ob16Power7 : QuotientMatrix := quotientDecode #v[3000, 899, 433, 393, 85, 139, 1586, 2285, 1604, 1100, 1035, 389]

private theorem ob16_power7 : value (obstruction16 ^ 7) = ob16Power7 := by
  apply power_step _ 3 4 _ _ _ ob16_power3 ob16_power4
  intro i
  fin_cases i <;> rfl

private def ob16Power8 : QuotientMatrix := quotientDecode #v[2047, 778, 2235, 179, 1306, 1445, 2638, 1126, 802, 947, 70, 1274]

private theorem ob16_power8 : value (obstruction16 ^ 8) = ob16Power8 := by
  apply power_step _ 4 4 _ _ _ ob16_power4 ob16_power4
  intro i
  fin_cases i <;> rfl

private def ob16Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob16_power15 : value (obstruction16 ^ 15) = ob16Power15 := by
  apply power_step _ 7 8 _ _ _ ob16_power7 ob16_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction16_small_power : (obstruction16 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction16 ^ 15) = 1
  rw [ob16_power15]
  exact decode_identity

private theorem obstruction16_nonidentity : obstruction16 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob16_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 3) h
  have hn : (quotientDecode #v[329, 2471, 3123, 429, 3535, 1195, 1443, 3228, 2522, 2949, 2388, 3149]) 0 3 ≠ (1 : QuotientMatrix) 0 3 := by decide +kernel
  exact hn hc

theorem alternative16 :
    representative 16 ∈ involutionMatrixLineStabilizer ∨
    representative 16 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 16), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction16 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 16)).pow_mem obstruction16_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction16_small_power obstruction16_nonidentity

private theorem r17_value : value (representative 17) = wordMatrix137 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix137_expansion.symm

private def obstruction17 : quotientSubgroup := (representative 17) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 3) * ((sylowGenerator 1)))))

private def ob17M3 : QuotientMatrix := quotientDecode #v[1315, 3788, 3161, 658, 1953, 612, 2750, 3689, 2461, 795, 1024, 3312]

private theorem ob17_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob17M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob17M2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem ob17_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob17M3 = ob17M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob17M1 : QuotientMatrix := quotientDecode #v[2704, 1044, 1492, 2567, 2887, 649, 4053, 1033, 1232, 4003, 1047, 251]

private theorem ob17_mul1 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob17M2 = ob17M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob17M0 : QuotientMatrix := quotientDecode #v[3299, 1764, 1241, 58, 2148, 976, 826, 1775, 3985, 1236, 3894, 2897]

private theorem ob17_mul0 : quotientDecode #v[1713, 1721, 1431, 3404, 2163, 3699, 1576, 3243, 348, 4041, 3212, 2688] * ob17M1 = ob17M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob17_value : value (obstruction17) = ob17M0 := by
  simp only [obstruction17, r17_value, s1_inverse_value, s2_inverse_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[1713, 1721, 1431, 3404, 2163, 3699, 1576, 3243, 348, 4041, 3212, 2688] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob17_mul3, ob17_mul2, ob17_mul1, ob17_mul0]

private theorem obstruction17_mem : obstruction17 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 17)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 17)).mul_mem (representative_mem_join 17) ((baseSubgroup ⊔ Subgroup.zpowers (representative 17)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 17)).inv_mem (sylow_mem_join 17 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 17)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 17)).inv_mem (sylow_mem_join 17 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 17)).mul_mem (sylow_mem_join 17 3) (sylow_mem_join 17 1)))))

private def ob17Power2 : QuotientMatrix := quotientDecode #v[2149, 2366, 3678, 3434, 3938, 1780, 1583, 771, 3402, 1630, 1707, 1961]

private theorem ob17_power2 : value (obstruction17 ^ 2) = ob17Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob17_value) (by rw [pow_one]; exact ob17_value)
  intro i
  fin_cases i <;> rfl

private def ob17Power3 : QuotientMatrix := quotientDecode #v[897, 3443, 2538, 3522, 2348, 346, 1750, 322, 3602, 699, 1248, 3477]

private theorem ob17_power3 : value (obstruction17 ^ 3) = ob17Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob17_value) ob17_power2
  intro i
  fin_cases i <;> rfl

private def ob17Power5 : QuotientMatrix := quotientDecode #v[114, 682, 3439, 90, 3875, 83, 3547, 603, 256, 250, 1395, 1554]

private theorem ob17_power5 : value (obstruction17 ^ 5) = ob17Power5 := by
  apply power_step _ 2 3 _ _ _ ob17_power2 ob17_power3
  intro i
  fin_cases i <;> rfl

private def ob17Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob17_power10 : value (obstruction17 ^ 10) = ob17Power10 := by
  apply power_step _ 5 5 _ _ _ ob17_power5 ob17_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction17_small_power : (obstruction17 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction17 ^ 10) = 1
  rw [ob17_power10]
  exact decode_identity

private theorem obstruction17_nonidentity : obstruction17 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob17_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[2149, 2366, 3678, 3434, 3938, 1780, 1583, 771, 3402, 1630, 1707, 1961]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative17 :
    representative 17 ∈ involutionMatrixLineStabilizer ∨
    representative 17 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 17), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction17 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 17)).pow_mem obstruction17_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction17_small_power obstruction17_nonidentity

private theorem r18_value : value (representative 18) = wordMatrix141 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix141_expansion.symm

private def obstruction18 : quotientSubgroup := (representative 18) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 3) * ((sylowGenerator 1)))))

private def ob18M3 : QuotientMatrix := quotientDecode #v[1315, 3788, 3161, 658, 1953, 612, 2750, 3689, 2461, 795, 1024, 3312]

private theorem ob18_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob18M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob18M2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem ob18_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob18M3 = ob18M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob18M1 : QuotientMatrix := quotientDecode #v[2704, 1044, 1492, 2567, 2887, 649, 4053, 1033, 1232, 4003, 1047, 251]

private theorem ob18_mul1 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob18M2 = ob18M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob18M0 : QuotientMatrix := quotientDecode #v[2684, 2093, 2720, 2063, 3659, 17, 1351, 2813, 2002, 3619, 2444, 210]

private theorem ob18_mul0 : quotientDecode #v[2070, 817, 3544, 2737, 2835, 91, 3780, 655, 1249, 3539, 352, 2962] * ob18M1 = ob18M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob18_value : value (obstruction18) = ob18M0 := by
  simp only [obstruction18, r18_value, s1_inverse_value, s2_inverse_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[2070, 817, 3544, 2737, 2835, 91, 3780, 655, 1249, 3539, 352, 2962] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob18_mul3, ob18_mul2, ob18_mul1, ob18_mul0]

private theorem obstruction18_mem : obstruction18 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 18)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 18)).mul_mem (representative_mem_join 18) ((baseSubgroup ⊔ Subgroup.zpowers (representative 18)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 18)).inv_mem (sylow_mem_join 18 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 18)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 18)).inv_mem (sylow_mem_join 18 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 18)).mul_mem (sylow_mem_join 18 3) (sylow_mem_join 18 1)))))

private def ob18Power2 : QuotientMatrix := quotientDecode #v[1859, 2064, 1053, 44, 2148, 1079, 1000, 1986, 2465, 1341, 3922, 2524]

private theorem ob18_power2 : value (obstruction18 ^ 2) = ob18Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob18_value) (by rw [pow_one]; exact ob18_value)
  intro i
  fin_cases i <;> rfl

private def ob18Power3 : QuotientMatrix := quotientDecode #v[1899, 3737, 3860, 702, 3876, 3879, 3669, 2026, 1936, 2263, 910, 1118]

private theorem ob18_power3 : value (obstruction18 ^ 3) = ob18Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob18_value) ob18_power2
  intro i
  fin_cases i <;> rfl

private def ob18Power5 : QuotientMatrix := quotientDecode #v[2926, 2938, 1643, 653, 2616, 1387, 2913, 3055, 3176, 3804, 1919, 2303]

private theorem ob18_power5 : value (obstruction18 ^ 5) = ob18Power5 := by
  apply power_step _ 2 3 _ _ _ ob18_power2 ob18_power3
  intro i
  fin_cases i <;> rfl

private def ob18Power6 : QuotientMatrix := quotientDecode #v[1783, 540, 2215, 3085, 2212, 342, 1545, 1654, 1031, 1059, 2974, 460]

private theorem ob18_power6 : value (obstruction18 ^ 6) = ob18Power6 := by
  apply power_step _ 3 3 _ _ _ ob18_power3 ob18_power3
  intro i
  fin_cases i <;> rfl

private def ob18Power11 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob18_power11 : value (obstruction18 ^ 11) = ob18Power11 := by
  apply power_step _ 5 6 _ _ _ ob18_power5 ob18_power6
  intro i
  fin_cases i <;> rfl

private theorem obstruction18_small_power : (obstruction18 ^ 1) ^ 11 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction18 ^ 11) = 1
  rw [ob18_power11]
  exact decode_identity

private theorem obstruction18_nonidentity : obstruction18 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob18_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[2684, 2093, 2720, 2063, 3659, 17, 1351, 2813, 2002, 3619, 2444, 210]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative18 :
    representative 18 ∈ involutionMatrixLineStabilizer ∨
    representative 18 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 18), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction18 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 18)).pow_mem obstruction18_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 11 (by decide +kernel)
    obstruction18_small_power obstruction18_nonidentity

private theorem r19_value : value (representative 19) = wordMatrix146 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix146_expansion.symm

private def obstruction19 : quotientSubgroup := (representative 19) * ((sylowGenerator 2) * ((sylowGenerator 1) * ((sylowGenerator 0))))

private def ob19M2 : QuotientMatrix := quotientDecode #v[3101, 213, 3495, 3915, 376, 2363, 871, 3638, 1373, 3630, 1047, 3976]

private theorem ob19_mul2 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] = ob19M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob19M1 : QuotientMatrix := quotientDecode #v[3728, 2586, 1650, 2567, 751, 3873, 4034, 1033, 1910, 3077, 1047, 3829]

private theorem ob19_mul1 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * ob19M2 = ob19M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob19M0 : QuotientMatrix := quotientDecode #v[2164, 2938, 2661, 1578, 1161, 3896, 1758, 1701, 3175, 3261, 3972, 3312]

private theorem ob19_mul0 : quotientDecode #v[2699, 1943, 2801, 1838, 1161, 1624, 1881, 3032, 2297, 448, 1002, 3303] * ob19M1 = ob19M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob19_value : value (obstruction19) = ob19M0 := by
  simp only [obstruction19, r19_value, s2_value, s1_value, s0_value, map_mul]
  change quotientDecode #v[2699, 1943, 2801, 1838, 1161, 1624, 1881, 3032, 2297, 448, 1002, 3303] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960]))) = _
  rw [ob19_mul2, ob19_mul1, ob19_mul0]

private theorem obstruction19_mem : obstruction19 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 19)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 19)).mul_mem (representative_mem_join 19) ((baseSubgroup ⊔ Subgroup.zpowers (representative 19)).mul_mem (sylow_mem_join 19 2) ((baseSubgroup ⊔ Subgroup.zpowers (representative 19)).mul_mem (sylow_mem_join 19 1) (sylow_mem_join 19 0))))

private def ob19Power2 : QuotientMatrix := quotientDecode #v[3066, 3093, 3002, 337, 1919, 3637, 254, 2229, 1017, 2651, 3950, 2238]

private theorem ob19_power2 : value (obstruction19 ^ 2) = ob19Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob19_value) (by rw [pow_one]; exact ob19_value)
  intro i
  fin_cases i <;> rfl

private def ob19Power3 : QuotientMatrix := quotientDecode #v[2736, 1516, 3182, 1604, 3440, 1641, 3327, 1013, 1358, 1854, 3453, 1745]

private theorem ob19_power3 : value (obstruction19 ^ 3) = ob19Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob19_value) ob19_power2
  intro i
  fin_cases i <;> rfl

private def ob19Power5 : QuotientMatrix := quotientDecode #v[794, 2, 4069, 3697, 3485, 341, 3029, 2275, 2711, 2424, 3212, 507]

private theorem ob19_power5 : value (obstruction19 ^ 5) = ob19Power5 := by
  apply power_step _ 2 3 _ _ _ ob19_power2 ob19_power3
  intro i
  fin_cases i <;> rfl

private def ob19Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob19_power10 : value (obstruction19 ^ 10) = ob19Power10 := by
  apply power_step _ 5 5 _ _ _ ob19_power5 ob19_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction19_small_power : (obstruction19 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction19 ^ 10) = 1
  rw [ob19_power10]
  exact decode_identity

private theorem obstruction19_nonidentity : obstruction19 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob19_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3066, 3093, 3002, 337, 1919, 3637, 254, 2229, 1017, 2651, 3950, 2238]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative19 :
    representative 19 ∈ involutionMatrixLineStabilizer ∨
    representative 19 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 19), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction19 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 19)).pow_mem obstruction19_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction19_small_power obstruction19_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
