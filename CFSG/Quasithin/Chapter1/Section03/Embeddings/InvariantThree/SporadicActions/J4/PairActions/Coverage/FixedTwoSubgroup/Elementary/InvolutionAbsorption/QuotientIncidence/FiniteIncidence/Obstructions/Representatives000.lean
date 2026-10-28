module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second
import Mathlib.Tactic.FinCases

/-!
# The representative alternatives at indices 0 through 9

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

theorem alternative0 :
    representative 0 ∈ involutionMatrixLineStabilizer ∨
    representative 0 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 0), x ^ 2304 ≠ 1 := by
  left
  exact involutionMatrixLineStabilizer.one_mem

private theorem r1_value : value (representative 1) = wordMatrix049 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix049_expansion.symm

private theorem r1_inverse_value :
    value ((representative 1)⁻¹) = quotientDecode #v[2431, 3264, 3043, 332, 3659, 901, 3399, 2600, 428, 4021, 1047, 212] := by
  apply inverse_value _ _ _ r1_value
  intro i
  fin_cases i <;> rfl

theorem r1_line : representative 1 ∈ involutionMatrixLineStabilizer := by
  apply line_mem_of_inverse _ _ 23 1047 1024 r1_inverse_value
  · rfl
  · rfl
  · rfl
  · change {involutionMatrixVector 23, involutionMatrixVector 1047,
      involutionMatrixVector 1024} =
      {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]

theorem alternative1 :
    representative 1 ∈ involutionMatrixLineStabilizer ∨
    representative 1 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 1), x ^ 2304 ≠ 1 := by
  exact Or.inl r1_line

private theorem r2_value : value (representative 2) = wordMatrix055 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix055_expansion.symm

private def obstruction2 : quotientSubgroup := (representative 2) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob2M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob2_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob2M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob2M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob2_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob2M3 = ob2M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob2M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob2_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob2M2 = ob2M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob2M0 : QuotientMatrix := quotientDecode #v[3423, 4042, 1355, 3528, 1425, 2530, 3010, 444, 1104, 2748, 2008, 2866]

private theorem ob2_mul0 : quotientDecode #v[2699, 3655, 1268, 3733, 1019, 3976, 64, 708, 4064, 4014, 2717, 581] * ob2M1 = ob2M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob2_value : value (obstruction2) = ob2M0 := by
  simp only [obstruction2, r2_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2699, 3655, 1268, 3733, 1019, 3976, 64, 708, 4064, 4014, 2717, 581] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob2_mul3, ob2_mul2, ob2_mul1, ob2_mul0]

private theorem obstruction2_mem : obstruction2 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 2)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 2)).mul_mem (representative_mem_join 2) ((baseSubgroup ⊔ Subgroup.zpowers (representative 2)).mul_mem (sylow_mem_join 2 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 2)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 2)).inv_mem (sylow_mem_join 2 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 2)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 2)).inv_mem (sylow_mem_join 2 2)) (sylow_mem_join 2 1)))))

private def ob2Power2 : QuotientMatrix := quotientDecode #v[3327, 2682, 1815, 3852, 2810, 820, 106, 284, 2443, 1218, 2835, 1639]

private theorem ob2_power2 : value (obstruction2 ^ 2) = ob2Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob2_value) (by rw [pow_one]; exact ob2_value)
  intro i
  fin_cases i <;> rfl

private def ob2Power3 : QuotientMatrix := quotientDecode #v[241, 1085, 2939, 2693, 1409, 2004, 34, 2370, 387, 620, 730, 2202]

private theorem ob2_power3 : value (obstruction2 ^ 3) = ob2Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob2_value) ob2_power2
  intro i
  fin_cases i <;> rfl

private def ob2Power4 : QuotientMatrix := quotientDecode #v[2898, 3703, 3378, 2086, 3947, 912, 1576, 2922, 1913, 31, 1873, 3357]

private theorem ob2_power4 : value (obstruction2 ^ 4) = ob2Power4 := by
  apply power_step _ 2 2 _ _ _ ob2_power2 ob2_power2
  intro i
  fin_cases i <;> rfl

private def ob2Power7 : QuotientMatrix := quotientDecode #v[2795, 1516, 3499, 8, 16, 3884, 3559, 571, 2358, 179, 1127, 3917]

private theorem ob2_power7 : value (obstruction2 ^ 7) = ob2Power7 := by
  apply power_step _ 3 4 _ _ _ ob2_power3 ob2_power4
  intro i
  fin_cases i <;> rfl

private def ob2Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob2_power14 : value (obstruction2 ^ 14) = ob2Power14 := by
  apply power_step _ 7 7 _ _ _ ob2_power7 ob2_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction2_small_power : (obstruction2 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction2 ^ 14) = 1
  rw [ob2_power14]
  exact decode_identity

private theorem obstruction2_nonidentity : obstruction2 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob2_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[3327, 2682, 1815, 3852, 2810, 820, 106, 284, 2443, 1218, 2835, 1639]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative2 :
    representative 2 ∈ involutionMatrixLineStabilizer ∨
    representative 2 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 2), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction2 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 2)).pow_mem obstruction2_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction2_small_power obstruction2_nonidentity

private theorem r3_value : value (representative 3) = wordMatrix060 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix060_expansion.symm

private def obstruction3 : quotientSubgroup := (representative 3) * ((sylowGenerator 2) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 0))))

private def ob3M2 : QuotientMatrix := quotientDecode #v[2077, 3396, 2181, 3915, 3531, 1439, 871, 3638, 1128, 3852, 1047, 1550]

private theorem ob3_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] = ob3M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob3M1 : QuotientMatrix := quotientDecode #v[2704, 907, 1863, 3591, 3659, 901, 3029, 30, 579, 2343, 1047, 1907]

private theorem ob3_mul1 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * ob3M2 = ob3M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob3M0 : QuotientMatrix := quotientDecode #v[4006, 2592, 2814, 1553, 1740, 1240, 516, 179, 1444, 746, 977, 420]

private theorem ob3_mul0 : quotientDecode #v[804, 2513, 666, 1423, 2988, 1401, 3703, 3256, 2166, 2277, 2717, 3169] * ob3M1 = ob3M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob3_value : value (obstruction3) = ob3M0 := by
  simp only [obstruction3, r3_value, s2_value, s1_inverse_value, s0_value, map_mul]
  change quotientDecode #v[804, 2513, 666, 1423, 2988, 1401, 3703, 3256, 2166, 2277, 2717, 3169] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960]))) = _
  rw [ob3_mul2, ob3_mul1, ob3_mul0]

private theorem obstruction3_mem : obstruction3 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 3)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 3)).mul_mem (representative_mem_join 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 3)).mul_mem (sylow_mem_join 3 2) ((baseSubgroup ⊔ Subgroup.zpowers (representative 3)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 3)).inv_mem (sylow_mem_join 3 1)) (sylow_mem_join 3 0))))

private def ob3Power2 : QuotientMatrix := quotientDecode #v[398, 1942, 1314, 2129, 3939, 443, 2068, 1825, 2272, 2228, 3219, 2865]

private theorem ob3_power2 : value (obstruction3 ^ 2) = ob3Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob3_value) (by rw [pow_one]; exact ob3_value)
  intro i
  fin_cases i <;> rfl

private def ob3Power3 : QuotientMatrix := quotientDecode #v[984, 574, 2189, 2762, 1633, 1172, 3478, 4065, 1995, 2557, 396, 2904]

private theorem ob3_power3 : value (obstruction3 ^ 3) = ob3Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob3_value) ob3_power2
  intro i
  fin_cases i <;> rfl

private def ob3Power4 : QuotientMatrix := quotientDecode #v[1316, 1585, 606, 3528, 2113, 3920, 368, 3314, 1471, 2026, 2552, 1075]

private theorem ob3_power4 : value (obstruction3 ^ 4) = ob3Power4 := by
  apply power_step _ 2 2 _ _ _ ob3_power2 ob3_power2
  intro i
  fin_cases i <;> rfl

private def ob3Power7 : QuotientMatrix := quotientDecode #v[2654, 2396, 627, 1442, 1302, 3861, 2216, 2152, 2290, 429, 1755, 671]

private theorem ob3_power7 : value (obstruction3 ^ 7) = ob3Power7 := by
  apply power_step _ 3 4 _ _ _ ob3_power3 ob3_power4
  intro i
  fin_cases i <;> rfl

private def ob3Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob3_power14 : value (obstruction3 ^ 14) = ob3Power14 := by
  apply power_step _ 7 7 _ _ _ ob3_power7 ob3_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction3_small_power : (obstruction3 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction3 ^ 14) = 1
  rw [ob3_power14]
  exact decode_identity

private theorem obstruction3_nonidentity : obstruction3 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob3_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[398, 1942, 1314, 2129, 3939, 443, 2068, 1825, 2272, 2228, 3219, 2865]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative3 :
    representative 3 ∈ involutionMatrixLineStabilizer ∨
    representative 3 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 3), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction3 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 3)).pow_mem obstruction3_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction3_small_power obstruction3_nonidentity

private theorem r4_value : value (representative 4) = wordMatrix065 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix065_expansion.symm

private def obstruction4 : quotientSubgroup := (representative 4) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 3) * ((sylowGenerator 1)))))

private def ob4M3 : QuotientMatrix := quotientDecode #v[1315, 3788, 3161, 658, 1953, 612, 2750, 3689, 2461, 795, 1024, 3312]

private theorem ob4_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob4M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob4M2 : QuotientMatrix := quotientDecode #v[3018, 4063, 743, 881, 1765, 2876, 3877, 283, 844, 2506, 1024, 3738]

private theorem ob4_mul2 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * ob4M3 = ob4M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob4M1 : QuotientMatrix := quotientDecode #v[2704, 1044, 1492, 2567, 2887, 649, 4053, 1033, 1232, 4003, 1047, 251]

private theorem ob4_mul1 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob4M2 = ob4M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob4M0 : QuotientMatrix := quotientDecode #v[2157, 3523, 1643, 3857, 2801, 2571, 2360, 740, 2480, 2076, 3807, 2035]

private theorem ob4_mul0 : quotientDecode #v[3300, 3705, 636, 322, 598, 209, 622, 686, 3168, 1135, 3864, 2403] * ob4M1 = ob4M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob4_value : value (obstruction4) = ob4M0 := by
  simp only [obstruction4, r4_value, s1_inverse_value, s2_inverse_value, s3_value, s1_value, map_mul]
  change quotientDecode #v[3300, 3705, 636, 322, 598, 209, 622, 686, 3168, 1135, 3864, 2403] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob4_mul3, ob4_mul2, ob4_mul1, ob4_mul0]

private theorem obstruction4_mem : obstruction4 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 4)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 4)).mul_mem (representative_mem_join 4) ((baseSubgroup ⊔ Subgroup.zpowers (representative 4)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 4)).inv_mem (sylow_mem_join 4 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 4)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 4)).inv_mem (sylow_mem_join 4 2)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 4)).mul_mem (sylow_mem_join 4 3) (sylow_mem_join 4 1)))))

private def ob4Power2 : QuotientMatrix := quotientDecode #v[1495, 3822, 3919, 2588, 3236, 1360, 424, 4000, 3165, 1144, 3273, 507]

private theorem ob4_power2 : value (obstruction4 ^ 2) = ob4Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob4_value) (by rw [pow_one]; exact ob4_value)
  intro i
  fin_cases i <;> rfl

private def ob4Power3 : QuotientMatrix := quotientDecode #v[1415, 1118, 3436, 3172, 1960, 1190, 3662, 111, 3058, 2060, 1420, 2089]

private theorem ob4_power3 : value (obstruction4 ^ 3) = ob4Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob4_value) ob4_power2
  intro i
  fin_cases i <;> rfl

private def ob4Power4 : QuotientMatrix := quotientDecode #v[1614, 2479, 2773, 3188, 2189, 3480, 3249, 4071, 186, 3721, 3313, 2692]

private theorem ob4_power4 : value (obstruction4 ^ 4) = ob4Power4 := by
  apply power_step _ 2 2 _ _ _ ob4_power2 ob4_power2
  intro i
  fin_cases i <;> rfl

private def ob4Power7 : QuotientMatrix := quotientDecode #v[1688, 1987, 327, 3465, 3273, 3572, 2883, 2153, 2907, 3109, 1293, 3366]

private theorem ob4_power7 : value (obstruction4 ^ 7) = ob4Power7 := by
  apply power_step _ 3 4 _ _ _ ob4_power3 ob4_power4
  intro i
  fin_cases i <;> rfl

private def ob4Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob4_power14 : value (obstruction4 ^ 14) = ob4Power14 := by
  apply power_step _ 7 7 _ _ _ ob4_power7 ob4_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction4_small_power : (obstruction4 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction4 ^ 14) = 1
  rw [ob4_power14]
  exact decode_identity

private theorem obstruction4_nonidentity : obstruction4 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob4_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[1495, 3822, 3919, 2588, 3236, 1360, 424, 4000, 3165, 1144, 3273, 507]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative4 :
    representative 4 ∈ involutionMatrixLineStabilizer ∨
    representative 4 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 4), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction4 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 4)).pow_mem obstruction4_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction4_small_power obstruction4_nonidentity

private theorem r5_value : value (representative 5) = wordMatrix072 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix072_expansion.symm

private def obstruction5 : quotientSubgroup := (representative 5) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob5M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob5_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob5M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob5M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob5_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob5M3 = ob5M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob5M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob5_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob5M2 = ob5M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob5M0 : QuotientMatrix := quotientDecode #v[1831, 2894, 2088, 1952, 1286, 2155, 277, 1979, 3941, 1843, 2325, 3206]

private theorem ob5_mul0 : quotientDecode #v[682, 1565, 485, 1665, 2021, 577, 2977, 1218, 3463, 2779, 3503, 3253] * ob5M1 = ob5M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob5_value : value (obstruction5) = ob5M0 := by
  simp only [obstruction5, r5_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[682, 1565, 485, 1665, 2021, 577, 2977, 1218, 3463, 2779, 3503, 3253] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob5_mul3, ob5_mul2, ob5_mul1, ob5_mul0]

private theorem obstruction5_mem : obstruction5 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 5)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 5)).mul_mem (representative_mem_join 5) ((baseSubgroup ⊔ Subgroup.zpowers (representative 5)).mul_mem (sylow_mem_join 5 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 5)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 5)).inv_mem (sylow_mem_join 5 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 5)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 5)).inv_mem (sylow_mem_join 5 2)) (sylow_mem_join 5 1)))))

private def ob5Power2 : QuotientMatrix := quotientDecode #v[3433, 259, 845, 3731, 1302, 3633, 1388, 92, 2996, 71, 2538, 334]

private theorem ob5_power2 : value (obstruction5 ^ 2) = ob5Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob5_value) (by rw [pow_one]; exact ob5_value)
  intro i
  fin_cases i <;> rfl

private def ob5Power3 : QuotientMatrix := quotientDecode #v[783, 780, 492, 3188, 16, 2282, 134, 2971, 1582, 1364, 456, 2742]

private theorem ob5_power3 : value (obstruction5 ^ 3) = ob5Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob5_value) ob5_power2
  intro i
  fin_cases i <;> rfl

private def ob5Power4 : QuotientMatrix := quotientDecode #v[2999, 2014, 3624, 451, 1286, 3757, 1245, 3492, 651, 2635, 3691, 517]

private theorem ob5_power4 : value (obstruction5 ^ 4) = ob5Power4 := by
  apply power_step _ 2 2 _ _ _ ob5_power2 ob5_power2
  intro i
  fin_cases i <;> rfl

private def ob5Power7 : QuotientMatrix := quotientDecode #v[2882, 1835, 2740, 3376, 1286, 972, 1106, 4045, 696, 787, 2609, 1975]

private theorem ob5_power7 : value (obstruction5 ^ 7) = ob5Power7 := by
  apply power_step _ 3 4 _ _ _ ob5_power3 ob5_power4
  intro i
  fin_cases i <;> rfl

private def ob5Power8 : QuotientMatrix := quotientDecode #v[3723, 737, 2379, 1947, 1302, 368, 1608, 964, 2629, 313, 511, 4052]

private theorem ob5_power8 : value (obstruction5 ^ 8) = ob5Power8 := by
  apply power_step _ 4 4 _ _ _ ob5_power4 ob5_power4
  intro i
  fin_cases i <;> rfl

private def ob5Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob5_power15 : value (obstruction5 ^ 15) = ob5Power15 := by
  apply power_step _ 7 8 _ _ _ ob5_power7 ob5_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction5_small_power : (obstruction5 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction5 ^ 15) = 1
  rw [ob5_power15]
  exact decode_identity

private theorem obstruction5_nonidentity : obstruction5 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob5_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[783, 780, 492, 3188, 16, 2282, 134, 2971, 1582, 1364, 456, 2742]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative5 :
    representative 5 ∈ involutionMatrixLineStabilizer ∨
    representative 5 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 5), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction5 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 5)).pow_mem obstruction5_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction5_small_power obstruction5_nonidentity

private theorem r6_value : value (representative 6) = wordMatrix083 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix083_expansion.symm

private def obstruction6 : quotientSubgroup := (representative 6) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob6M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob6_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob6M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob6M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob6_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob6M3 = ob6M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob6M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob6_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob6M2 = ob6M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob6M0 : QuotientMatrix := quotientDecode #v[2159, 1285, 1355, 1517, 3934, 1271, 4002, 3241, 2026, 2310, 3143, 3512]

private theorem ob6_mul0 : quotientDecode #v[2565, 3971, 1268, 1955, 575, 1584, 622, 2940, 1458, 1532, 2553, 2201] * ob6M1 = ob6M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob6_value : value (obstruction6) = ob6M0 := by
  simp only [obstruction6, r6_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2565, 3971, 1268, 1955, 575, 1584, 622, 2940, 1458, 1532, 2553, 2201] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob6_mul3, ob6_mul2, ob6_mul1, ob6_mul0]

private theorem obstruction6_mem : obstruction6 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 6)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 6)).mul_mem (representative_mem_join 6) ((baseSubgroup ⊔ Subgroup.zpowers (representative 6)).mul_mem (sylow_mem_join 6 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 6)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 6)).inv_mem (sylow_mem_join 6 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 6)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 6)).inv_mem (sylow_mem_join 6 2)) (sylow_mem_join 6 1)))))

private def ob6Power2 : QuotientMatrix := quotientDecode #v[2849, 1673, 3208, 1176, 2636, 3268, 584, 1059, 1471, 2588, 1660, 1272]

private theorem ob6_power2 : value (obstruction6 ^ 2) = ob6Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob6_value) (by rw [pow_one]; exact ob6_value)
  intro i
  fin_cases i <;> rfl

private def ob6Power3 : QuotientMatrix := quotientDecode #v[4044, 1130, 2235, 2653, 3002, 1983, 841, 1498, 353, 2886, 492, 264]

private theorem ob6_power3 : value (obstruction6 ^ 3) = ob6Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob6_value) ob6_power2
  intro i
  fin_cases i <;> rfl

private def ob6Power5 : QuotientMatrix := quotientDecode #v[860, 2785, 3939, 1489, 3041, 3788, 594, 3573, 18, 786, 1792, 295]

private theorem ob6_power5 : value (obstruction6 ^ 5) = ob6Power5 := by
  apply power_step _ 2 3 _ _ _ ob6_power2 ob6_power3
  intro i
  fin_cases i <;> rfl

private def ob6Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob6_power10 : value (obstruction6 ^ 10) = ob6Power10 := by
  apply power_step _ 5 5 _ _ _ ob6_power5 ob6_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction6_small_power : (obstruction6 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction6 ^ 10) = 1
  rw [ob6_power10]
  exact decode_identity

private theorem obstruction6_nonidentity : obstruction6 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob6_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 5) h
  have hn : (quotientDecode #v[2849, 1673, 3208, 1176, 2636, 3268, 584, 1059, 1471, 2588, 1660, 1272]) 0 5 ≠ (1 : QuotientMatrix) 0 5 := by decide +kernel
  exact hn hc

theorem alternative6 :
    representative 6 ∈ involutionMatrixLineStabilizer ∨
    representative 6 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 6), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction6 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 6)).pow_mem obstruction6_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction6_small_power obstruction6_nonidentity

private theorem r7_value : value (representative 7) = wordMatrix090 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix090_expansion.symm

private def obstruction7 : quotientSubgroup := (representative 7) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob7M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob7_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob7M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob7M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob7_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob7M3 = ob7M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob7M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob7_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob7M2 = ob7M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob7M0 : QuotientMatrix := quotientDecode #v[5, 2894, 1735, 1421, 2803, 907, 15, 387, 1704, 1310, 2872, 4017]

private theorem ob7_mul0 : quotientDecode #v[707, 1565, 2509, 410, 3678, 3355, 2610, 1336, 1478, 3520, 2740, 2621] * ob7M1 = ob7M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob7_value : value (obstruction7) = ob7M0 := by
  simp only [obstruction7, r7_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[707, 1565, 2509, 410, 3678, 3355, 2610, 1336, 1478, 3520, 2740, 2621] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob7_mul3, ob7_mul2, ob7_mul1, ob7_mul0]

private theorem obstruction7_mem : obstruction7 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 7)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 7)).mul_mem (representative_mem_join 7) ((baseSubgroup ⊔ Subgroup.zpowers (representative 7)).mul_mem (sylow_mem_join 7 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 7)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 7)).inv_mem (sylow_mem_join 7 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 7)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 7)).inv_mem (sylow_mem_join 7 2)) (sylow_mem_join 7 1)))))

private def ob7Power2 : QuotientMatrix := quotientDecode #v[1730, 1036, 550, 3932, 2320, 3315, 2049, 3168, 2467, 3943, 242, 4033]

private theorem ob7_power2 : value (obstruction7 ^ 2) = ob7Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob7_value) (by rw [pow_one]; exact ob7_value)
  intro i
  fin_cases i <;> rfl

private def ob7Power3 : QuotientMatrix := quotientDecode #v[1252, 2162, 2844, 3721, 1002, 1846, 4020, 1805, 90, 2359, 954, 1718]

private theorem ob7_power3 : value (obstruction7 ^ 3) = ob7Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob7_value) ob7_power2
  intro i
  fin_cases i <;> rfl

private def ob7Power4 : QuotientMatrix := quotientDecode #v[4088, 3464, 1470, 1436, 3954, 3199, 2307, 3009, 1087, 3565, 1422, 2900]

private theorem ob7_power4 : value (obstruction7 ^ 4) = ob7Power4 := by
  apply power_step _ 2 2 _ _ _ ob7_power2 ob7_power2
  intro i
  fin_cases i <;> rfl

private def ob7Power7 : QuotientMatrix := quotientDecode #v[3725, 3282, 3542, 658, 3963, 1895, 2682, 902, 3685, 2984, 2314, 2201]

private theorem ob7_power7 : value (obstruction7 ^ 7) = ob7Power7 := by
  apply power_step _ 3 4 _ _ _ ob7_power3 ob7_power4
  intro i
  fin_cases i <;> rfl

private def ob7Power8 : QuotientMatrix := quotientDecode #v[859, 1208, 1239, 1312, 142, 1670, 3355, 4028, 1233, 2946, 2010, 329]

private theorem ob7_power8 : value (obstruction7 ^ 8) = ob7Power8 := by
  apply power_step _ 4 4 _ _ _ ob7_power4 ob7_power4
  intro i
  fin_cases i <;> rfl

private def ob7Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob7_power15 : value (obstruction7 ^ 15) = ob7Power15 := by
  apply power_step _ 7 8 _ _ _ ob7_power7 ob7_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction7_small_power : (obstruction7 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction7 ^ 15) = 1
  rw [ob7_power15]
  exact decode_identity

private theorem obstruction7_nonidentity : obstruction7 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob7_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1252, 2162, 2844, 3721, 1002, 1846, 4020, 1805, 90, 2359, 954, 1718]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative7 :
    representative 7 ∈ involutionMatrixLineStabilizer ∨
    representative 7 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 7), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction7 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 7)).pow_mem obstruction7_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction7_small_power obstruction7_nonidentity

private theorem r8_value : value (representative 8) = wordMatrix094 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix094_expansion.symm

private def obstruction8 : quotientSubgroup := (representative 8) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob8M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob8_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob8M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob8M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob8_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob8M3 = ob8M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob8M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob8_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob8M2 = ob8M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob8M0 : QuotientMatrix := quotientDecode #v[1085, 2919, 1755, 1538, 3838, 1201, 3292, 2888, 2440, 941, 3143, 157]

private theorem ob8_mul0 : quotientDecode #v[266, 2929, 2988, 1221, 666, 1879, 4019, 3256, 320, 2629, 2553, 3311] * ob8M1 = ob8M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob8_value : value (obstruction8) = ob8M0 := by
  simp only [obstruction8, r8_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[266, 2929, 2988, 1221, 666, 1879, 4019, 3256, 320, 2629, 2553, 3311] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob8_mul3, ob8_mul2, ob8_mul1, ob8_mul0]

private theorem obstruction8_mem : obstruction8 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 8)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 8)).mul_mem (representative_mem_join 8) ((baseSubgroup ⊔ Subgroup.zpowers (representative 8)).mul_mem (sylow_mem_join 8 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 8)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 8)).inv_mem (sylow_mem_join 8 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 8)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 8)).inv_mem (sylow_mem_join 8 2)) (sylow_mem_join 8 1)))))

private def ob8Power2 : QuotientMatrix := quotientDecode #v[748, 2900, 4056, 1165, 2322, 2429, 1385, 102, 1119, 312, 2439, 338]

private theorem ob8_power2 : value (obstruction8 ^ 2) = ob8Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob8_value) (by rw [pow_one]; exact ob8_value)
  intro i
  fin_cases i <;> rfl

private def ob8Power3 : QuotientMatrix := quotientDecode #v[81, 3649, 2455, 1003, 3212, 2914, 3997, 1489, 486, 1477, 3036, 205]

private theorem ob8_power3 : value (obstruction8 ^ 3) = ob8Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob8_value) ob8_power2
  intro i
  fin_cases i <;> rfl

private def ob8Power5 : QuotientMatrix := quotientDecode #v[3735, 3688, 2585, 1056, 998, 885, 3455, 809, 3233, 1507, 893, 3254]

private theorem ob8_power5 : value (obstruction8 ^ 5) = ob8Power5 := by
  apply power_step _ 2 3 _ _ _ ob8_power2 ob8_power3
  intro i
  fin_cases i <;> rfl

private def ob8Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob8_power10 : value (obstruction8 ^ 10) = ob8Power10 := by
  apply power_step _ 5 5 _ _ _ ob8_power5 ob8_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction8_small_power : (obstruction8 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction8 ^ 10) = 1
  rw [ob8_power10]
  exact decode_identity

private theorem obstruction8_nonidentity : obstruction8 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob8_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[748, 2900, 4056, 1165, 2322, 2429, 1385, 102, 1119, 312, 2439, 338]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative8 :
    representative 8 ∈ involutionMatrixLineStabilizer ∨
    representative 8 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 8), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction8 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 8)).pow_mem obstruction8_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction8_small_power obstruction8_nonidentity

private theorem r9_value : value (representative 9) = wordMatrix100 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix100_expansion.symm

private def obstruction9 : quotientSubgroup := (representative 9) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob9M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob9_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob9M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob9M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob9_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob9M3 = ob9M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob9M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob9_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob9M2 = ob9M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob9M0 : QuotientMatrix := quotientDecode #v[1706, 3997, 2189, 2548, 285, 4019, 2832, 2873, 931, 2434, 2423, 2312]

private theorem ob9_mul0 : quotientDecode #v[1831, 1426, 2772, 1304, 433, 2268, 3423, 51, 2800, 2481, 2423, 1353] * ob9M1 = ob9M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob9_value : value (obstruction9) = ob9M0 := by
  simp only [obstruction9, r9_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[1831, 1426, 2772, 1304, 433, 2268, 3423, 51, 2800, 2481, 2423, 1353] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob9_mul3, ob9_mul2, ob9_mul1, ob9_mul0]

private theorem obstruction9_mem : obstruction9 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 9)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 9)).mul_mem (representative_mem_join 9) ((baseSubgroup ⊔ Subgroup.zpowers (representative 9)).mul_mem (sylow_mem_join 9 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 9)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 9)).inv_mem (sylow_mem_join 9 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 9)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 9)).inv_mem (sylow_mem_join 9 2)) (sylow_mem_join 9 1)))))

private def ob9Power2 : QuotientMatrix := quotientDecode #v[534, 1961, 1506, 3233, 1389, 1790, 564, 729, 1948, 3599, 3759, 863]

private theorem ob9_power2 : value (obstruction9 ^ 2) = ob9Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob9_value) (by rw [pow_one]; exact ob9_value)
  intro i
  fin_cases i <;> rfl

private def ob9Power3 : QuotientMatrix := quotientDecode #v[3983, 2178, 2771, 607, 2468, 150, 4001, 2024, 2059, 435, 1337, 2146]

private theorem ob9_power3 : value (obstruction9 ^ 3) = ob9Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob9_value) ob9_power2
  intro i
  fin_cases i <;> rfl

private def ob9Power4 : QuotientMatrix := quotientDecode #v[2345, 3500, 2185, 3009, 1708, 3380, 2174, 1336, 2507, 3843, 2852, 566]

private theorem ob9_power4 : value (obstruction9 ^ 4) = ob9Power4 := by
  apply power_step _ 2 2 _ _ _ ob9_power2 ob9_power2
  intro i
  fin_cases i <;> rfl

private def ob9Power7 : QuotientMatrix := quotientDecode #v[3375, 2722, 602, 1564, 2936, 1713, 3839, 1631, 3442, 1006, 2975, 2768]

private theorem ob9_power7 : value (obstruction9 ^ 7) = ob9Power7 := by
  apply power_step _ 3 4 _ _ _ ob9_power3 ob9_power4
  intro i
  fin_cases i <;> rfl

private def ob9Power8 : QuotientMatrix := quotientDecode #v[1057, 2973, 1510, 145, 3939, 968, 3892, 694, 2559, 2911, 323, 446]

private theorem ob9_power8 : value (obstruction9 ^ 8) = ob9Power8 := by
  apply power_step _ 4 4 _ _ _ ob9_power4 ob9_power4
  intro i
  fin_cases i <;> rfl

private def ob9Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob9_power15 : value (obstruction9 ^ 15) = ob9Power15 := by
  apply power_step _ 7 8 _ _ _ ob9_power7 ob9_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction9_small_power : (obstruction9 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction9 ^ 15) = 1
  rw [ob9_power15]
  exact decode_identity

private theorem obstruction9_nonidentity : obstruction9 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob9_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[3983, 2178, 2771, 607, 2468, 150, 4001, 2024, 2059, 435, 1337, 2146]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative9 :
    representative 9 ∈ involutionMatrixLineStabilizer ∨
    representative 9 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 9), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction9 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 9)).pow_mem obstruction9_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction9_small_power obstruction9_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
