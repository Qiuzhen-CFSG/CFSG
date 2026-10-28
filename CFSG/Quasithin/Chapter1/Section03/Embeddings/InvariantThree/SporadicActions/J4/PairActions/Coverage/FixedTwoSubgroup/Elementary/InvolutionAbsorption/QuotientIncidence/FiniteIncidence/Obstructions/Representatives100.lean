module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second
import Mathlib.Tactic.FinCases

/-!
# The representative alternatives at indices 100 through 109

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

private theorem r100_value : value (representative 100) = wordMatrix457 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix457_expansion.symm

private theorem r100_inverse_value :
    value ((representative 100)⁻¹) = quotientDecode #v[2050, 3287, 1772, 317, 558, 3113, 2007, 2220, 1150, 2074, 1047, 3047] := by
  apply inverse_value _ _ _ r100_value
  intro i
  fin_cases i <;> rfl

theorem r100_line : representative 100 ∈ involutionMatrixLineStabilizer := by
  apply line_mem_of_inverse _ _ 23 1047 1024 r100_inverse_value
  · rfl
  · rfl
  · rfl
  · change {involutionMatrixVector 23, involutionMatrixVector 1047,
      involutionMatrixVector 1024} =
      {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]

theorem alternative100 :
    representative 100 ∈ involutionMatrixLineStabilizer ∨
    representative 100 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 100), x ^ 2304 ≠ 1 := by
  exact Or.inl r100_line

private theorem r101_value : value (representative 101) = wordMatrix460 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix460_expansion.symm

private def obstruction101 : quotientSubgroup := (representative 101) * ((sylowGenerator 2) * ((sylowGenerator 0) * ((sylowGenerator 3) * ((sylowGenerator 2)))))

private def ob101M3 : QuotientMatrix := quotientDecode #v[110, 2621, 2181, 1716, 705, 2797, 2784, 316, 669, 394, 1047, 251]

private theorem ob101_mul3 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] = ob101M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob101M2 : QuotientMatrix := quotientDecode #v[2269, 2621, 3069, 1262, 2314, 3413, 3416, 1668, 1317, 4003, 1047, 899]

private theorem ob101_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * ob101M3 = ob101M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob101M1 : QuotientMatrix := quotientDecode #v[2640, 424, 3503, 1007, 1600, 1639, 581, 3843, 2940, 506, 1047, 489]

private theorem ob101_mul1 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * ob101M2 = ob101M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob101M0 : QuotientMatrix := quotientDecode #v[183, 2260, 2835, 1910, 1306, 970, 2983, 450, 2868, 3501, 1340, 2315]

private theorem ob101_mul0 : quotientDecode #v[3902, 855, 141, 686, 3948, 114, 425, 1480, 189, 78, 268, 301] * ob101M1 = ob101M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob101_value : value (obstruction101) = ob101M0 := by
  simp only [obstruction101, r101_value, s2_value, s0_value, s3_value, map_mul]
  change quotientDecode #v[3902, 855, 141, 686, 3948, 114, 425, 1480, 189, 78, 268, 301] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184])))) = _
  rw [ob101_mul3, ob101_mul2, ob101_mul1, ob101_mul0]

private theorem obstruction101_mem : obstruction101 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 101)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 101)).mul_mem (representative_mem_join 101) ((baseSubgroup ⊔ Subgroup.zpowers (representative 101)).mul_mem (sylow_mem_join 101 2) ((baseSubgroup ⊔ Subgroup.zpowers (representative 101)).mul_mem (sylow_mem_join 101 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 101)).mul_mem (sylow_mem_join 101 3) (sylow_mem_join 101 2)))))

private def ob101Power2 : QuotientMatrix := quotientDecode #v[1122, 3431, 747, 3349, 1200, 862, 3818, 2437, 593, 2521, 1213, 3370]

private theorem ob101_power2 : value (obstruction101 ^ 2) = ob101Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob101_value) (by rw [pow_one]; exact ob101_value)
  intro i
  fin_cases i <;> rfl

private def ob101Power3 : QuotientMatrix := quotientDecode #v[1413, 3102, 2839, 2493, 558, 3221, 1943, 2137, 935, 2689, 3836, 2923]

private theorem ob101_power3 : value (obstruction101 ^ 3) = ob101Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob101_value) ob101_power2
  intro i
  fin_cases i <;> rfl

private def ob101Power4 : QuotientMatrix := quotientDecode #v[1134, 3484, 2552, 2559, 2774, 843, 1037, 119, 2017, 1491, 330, 2282]

private theorem ob101_power4 : value (obstruction101 ^ 4) = ob101Power4 := by
  apply power_step _ 2 2 _ _ _ ob101_power2 ob101_power2
  intro i
  fin_cases i <;> rfl

private def ob101Power7 : QuotientMatrix := quotientDecode #v[2890, 3821, 4, 648, 2819, 3735, 2515, 2976, 260, 2336, 403, 3475]

private theorem ob101_power7 : value (obstruction101 ^ 7) = ob101Power7 := by
  apply power_step _ 3 4 _ _ _ ob101_power3 ob101_power4
  intro i
  fin_cases i <;> rfl

private def ob101Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob101_power14 : value (obstruction101 ^ 14) = ob101Power14 := by
  apply power_step _ 7 7 _ _ _ ob101_power7 ob101_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction101_small_power : (obstruction101 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction101 ^ 14) = 1
  rw [ob101_power14]
  exact decode_identity

private theorem obstruction101_nonidentity : obstruction101 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob101_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1122, 3431, 747, 3349, 1200, 862, 3818, 2437, 593, 2521, 1213, 3370]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative101 :
    representative 101 ∈ involutionMatrixLineStabilizer ∨
    representative 101 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 101), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction101 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 101)).pow_mem obstruction101_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction101_small_power obstruction101_nonidentity

private theorem r102_value : value (representative 102) = wordMatrix464 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix464_expansion.symm

private def obstruction102 : quotientSubgroup := (representative 102) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob102M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob102_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob102M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob102M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob102_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob102M2 = ob102M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob102M0 : QuotientMatrix := quotientDecode #v[936, 3525, 1607, 1394, 3392, 1681, 1070, 2940, 1518, 3975, 3860, 1904]

private theorem ob102_mul0 : quotientDecode #v[1784, 1851, 2233, 964, 2802, 2549, 3417, 844, 1233, 1602, 268, 2408] * ob102M1 = ob102M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob102_value : value (obstruction102) = ob102M0 := by
  simp only [obstruction102, r102_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[1784, 1851, 2233, 964, 2802, 2549, 3417, 844, 1233, 1602, 268, 2408] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob102_mul2, ob102_mul1, ob102_mul0]

private theorem obstruction102_mem : obstruction102 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 102)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 102)).mul_mem (representative_mem_join 102) ((baseSubgroup ⊔ Subgroup.zpowers (representative 102)).mul_mem (sylow_mem_join 102 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 102)).mul_mem (sylow_mem_join 102 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 102)).inv_mem (sylow_mem_join 102 2)))))

private def ob102Power2 : QuotientMatrix := quotientDecode #v[758, 1847, 3223, 2240, 2468, 1287, 1909, 467, 3529, 347, 2314, 2690]

private theorem ob102_power2 : value (obstruction102 ^ 2) = ob102Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob102_value) (by rw [pow_one]; exact ob102_value)
  intro i
  fin_cases i <;> rfl

private def ob102Power3 : QuotientMatrix := quotientDecode #v[134, 1670, 1650, 2082, 2356, 720, 3949, 2449, 1026, 1951, 2601, 3662]

private theorem ob102_power3 : value (obstruction102 ^ 3) = ob102Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob102_value) ob102_power2
  intro i
  fin_cases i <;> rfl

private def ob102Power5 : QuotientMatrix := quotientDecode #v[2675, 546, 1200, 2226, 1919, 3673, 3017, 3530, 3645, 3193, 1256, 1734]

private theorem ob102_power5 : value (obstruction102 ^ 5) = ob102Power5 := by
  apply power_step _ 2 3 _ _ _ ob102_power2 ob102_power3
  intro i
  fin_cases i <;> rfl

private def ob102Power10 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob102_power10 : value (obstruction102 ^ 10) = ob102Power10 := by
  apply power_step _ 5 5 _ _ _ ob102_power5 ob102_power5
  intro i
  fin_cases i <;> rfl

private theorem obstruction102_small_power : (obstruction102 ^ 2) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction102 ^ 10) = 1
  rw [ob102_power10]
  exact decode_identity

private theorem obstruction102_nonidentity : obstruction102 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob102_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[758, 1847, 3223, 2240, 2468, 1287, 1909, 467, 3529, 347, 2314, 2690]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative102 :
    representative 102 ∈ involutionMatrixLineStabilizer ∨
    representative 102 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 102), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction102 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 102)).pow_mem obstruction102_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction102_small_power obstruction102_nonidentity

private theorem r103_value : value (representative 103) = wordMatrix468 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix468_expansion.symm

private def obstruction103 : quotientSubgroup := (representative 103) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob103M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob103_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob103M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob103M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob103_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob103M2 = ob103M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob103M0 : QuotientMatrix := quotientDecode #v[4055, 3464, 41, 2338, 3208, 2910, 2673, 2039, 1827, 201, 1677, 454]

private theorem ob103_mul0 : quotientDecode #v[988, 3902, 1810, 1342, 3453, 834, 735, 1834, 1517, 3932, 3838, 3396] * ob103M1 = ob103M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob103_value : value (obstruction103) = ob103M0 := by
  simp only [obstruction103, r103_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[988, 3902, 1810, 1342, 3453, 834, 735, 1834, 1517, 3932, 3838, 3396] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob103_mul2, ob103_mul1, ob103_mul0]

private theorem obstruction103_mem : obstruction103 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 103)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 103)).mul_mem (representative_mem_join 103) ((baseSubgroup ⊔ Subgroup.zpowers (representative 103)).mul_mem (sylow_mem_join 103 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 103)).mul_mem (sylow_mem_join 103 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 103)).inv_mem (sylow_mem_join 103 2)))))

private def ob103Power2 : QuotientMatrix := quotientDecode #v[985, 3773, 3499, 51, 2462, 1110, 895, 2369, 2150, 2931, 1903, 1796]

private theorem ob103_power2 : value (obstruction103 ^ 2) = ob103Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob103_value) (by rw [pow_one]; exact ob103_value)
  intro i
  fin_cases i <;> rfl

private def ob103Power3 : QuotientMatrix := quotientDecode #v[17, 383, 1980, 1417, 2329, 3541, 281, 835, 3400, 2516, 2844, 334]

private theorem ob103_power3 : value (obstruction103 ^ 3) = ob103Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob103_value) ob103_power2
  intro i
  fin_cases i <;> rfl

private def ob103Power4 : QuotientMatrix := quotientDecode #v[863, 464, 2125, 172, 3224, 3736, 3422, 4036, 827, 1986, 943, 2513]

private theorem ob103_power4 : value (obstruction103 ^ 4) = ob103Power4 := by
  apply power_step _ 2 2 _ _ _ ob103_power2 ob103_power2
  intro i
  fin_cases i <;> rfl

private def ob103Power7 : QuotientMatrix := quotientDecode #v[4039, 1547, 627, 3235, 1409, 3157, 3152, 2856, 1207, 3237, 2385, 1876]

private theorem ob103_power7 : value (obstruction103 ^ 7) = ob103Power7 := by
  apply power_step _ 3 4 _ _ _ ob103_power3 ob103_power4
  intro i
  fin_cases i <;> rfl

private def ob103Power8 : QuotientMatrix := quotientDecode #v[3921, 3385, 3889, 2493, 2446, 3660, 434, 1104, 1242, 1052, 4043, 1975]

private theorem ob103_power8 : value (obstruction103 ^ 8) = ob103Power8 := by
  apply power_step _ 4 4 _ _ _ ob103_power4 ob103_power4
  intro i
  fin_cases i <;> rfl

private def ob103Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob103_power15 : value (obstruction103 ^ 15) = ob103Power15 := by
  apply power_step _ 7 8 _ _ _ ob103_power7 ob103_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction103_small_power : (obstruction103 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction103 ^ 15) = 1
  rw [ob103_power15]
  exact decode_identity

private theorem obstruction103_nonidentity : obstruction103 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob103_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 4) h
  have hn : (quotientDecode #v[17, 383, 1980, 1417, 2329, 3541, 281, 835, 3400, 2516, 2844, 334]) 0 4 ≠ (1 : QuotientMatrix) 0 4 := by decide +kernel
  exact hn hc

theorem alternative103 :
    representative 103 ∈ involutionMatrixLineStabilizer ∨
    representative 103 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 103), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction103 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 103)).pow_mem obstruction103_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction103_small_power obstruction103_nonidentity

theorem alternative104 :
    representative 104 ∈ involutionMatrixLineStabilizer ∨
    representative 104 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 104), x ^ 2304 ≠ 1 := by
  exact Or.inr (Or.inl r104_second)

private theorem r105_value : value (representative 105) = wordMatrix475 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix475_expansion.symm

private def obstruction105 : quotientSubgroup := (representative 105) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹)))

private def ob105M2 : QuotientMatrix := quotientDecode #v[547, 2586, 285, 2141, 2355, 2201, 2170, 945, 206, 571, 1047, 2458]

private theorem ob105_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob105M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob105M1 : QuotientMatrix := quotientDecode #v[3408, 2928, 1510, 1619, 977, 3050, 1942, 3496, 802, 448, 1024, 510]

private theorem ob105_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob105M2 = ob105M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob105M0 : QuotientMatrix := quotientDecode #v[1429, 4040, 358, 1502, 1661, 2254, 2530, 326, 3712, 1574, 1912, 157]

private theorem ob105_mul0 : quotientDecode #v[15, 4006, 1311, 2747, 1386, 415, 510, 932, 4059, 188, 3868, 3927] * ob105M1 = ob105M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob105_value : value (obstruction105) = ob105M0 := by
  simp only [obstruction105, r105_value, s3_value, s1_inverse_value, s2_inverse_value, map_mul]
  change quotientDecode #v[15, 4006, 1311, 2747, 1386, 415, 510, 932, 4059, 188, 3868, 3927] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob105_mul2, ob105_mul1, ob105_mul0]

private theorem obstruction105_mem : obstruction105 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 105)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 105)).mul_mem (representative_mem_join 105) ((baseSubgroup ⊔ Subgroup.zpowers (representative 105)).mul_mem (sylow_mem_join 105 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 105)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 105)).inv_mem (sylow_mem_join 105 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 105)).inv_mem (sylow_mem_join 105 2)))))

private def ob105Power2 : QuotientMatrix := quotientDecode #v[2608, 569, 258, 3153, 1826, 841, 447, 2508, 133, 1854, 3409, 1558]

private theorem ob105_power2 : value (obstruction105 ^ 2) = ob105Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob105_value) (by rw [pow_one]; exact ob105_value)
  intro i
  fin_cases i <;> rfl

private def ob105Power3 : QuotientMatrix := quotientDecode #v[2056, 2270, 328, 3567, 2264, 271, 3984, 513, 1461, 2589, 879, 2445]

private theorem ob105_power3 : value (obstruction105 ^ 3) = ob105Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob105_value) ob105_power2
  intro i
  fin_cases i <;> rfl

private def ob105Power4 : QuotientMatrix := quotientDecode #v[1347, 1332, 700, 2026, 2970, 101, 2168, 947, 766, 491, 1903, 3702]

private theorem ob105_power4 : value (obstruction105 ^ 4) = ob105Power4 := by
  apply power_step _ 2 2 _ _ _ ob105_power2 ob105_power2
  intro i
  fin_cases i <;> rfl

private def ob105Power7 : QuotientMatrix := quotientDecode #v[2460, 3653, 3436, 1384, 2509, 2015, 549, 1192, 2594, 1042, 3625, 3886]

private theorem ob105_power7 : value (obstruction105 ^ 7) = ob105Power7 := by
  apply power_step _ 3 4 _ _ _ ob105_power3 ob105_power4
  intro i
  fin_cases i <;> rfl

private def ob105Power8 : QuotientMatrix := quotientDecode #v[3486, 3282, 3313, 3338, 1940, 4066, 2587, 2862, 445, 3789, 2374, 3325]

private theorem ob105_power8 : value (obstruction105 ^ 8) = ob105Power8 := by
  apply power_step _ 4 4 _ _ _ ob105_power4 ob105_power4
  intro i
  fin_cases i <;> rfl

private def ob105Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob105_power15 : value (obstruction105 ^ 15) = ob105Power15 := by
  apply power_step _ 7 8 _ _ _ ob105_power7 ob105_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction105_small_power : (obstruction105 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction105 ^ 15) = 1
  rw [ob105_power15]
  exact decode_identity

private theorem obstruction105_nonidentity : obstruction105 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob105_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[2056, 2270, 328, 3567, 2264, 271, 3984, 513, 1461, 2589, 879, 2445]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative105 :
    representative 105 ∈ involutionMatrixLineStabilizer ∨
    representative 105 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 105), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction105 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 105)).pow_mem obstruction105_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction105_small_power obstruction105_nonidentity

private theorem r106_value : value (representative 106) = wordMatrix479 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix479_expansion.symm

private def obstruction106 : quotientSubgroup := (representative 106) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob106M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob106_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob106M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob106M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob106_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob106M2 = ob106M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob106M0 : QuotientMatrix := quotientDecode #v[1361, 3808, 744, 3241, 3481, 1719, 665, 590, 3789, 1517, 3019, 2104]

private theorem ob106_mul0 : quotientDecode #v[2394, 525, 3950, 1128, 3045, 3772, 997, 2105, 600, 3530, 192, 1210] * ob106M1 = ob106M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob106_value : value (obstruction106) = ob106M0 := by
  simp only [obstruction106, r106_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[2394, 525, 3950, 1128, 3045, 3772, 997, 2105, 600, 3530, 192, 1210] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob106_mul2, ob106_mul1, ob106_mul0]

private theorem obstruction106_mem : obstruction106 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 106)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 106)).mul_mem (representative_mem_join 106) ((baseSubgroup ⊔ Subgroup.zpowers (representative 106)).mul_mem (sylow_mem_join 106 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 106)).mul_mem (sylow_mem_join 106 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 106)).inv_mem (sylow_mem_join 106 2)))))

private def ob106Power2 : QuotientMatrix := quotientDecode #v[3927, 126, 3876, 3826, 2833, 3615, 962, 2005, 3545, 2166, 1239, 4031]

private theorem ob106_power2 : value (obstruction106 ^ 2) = ob106Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob106_value) (by rw [pow_one]; exact ob106_value)
  intro i
  fin_cases i <;> rfl

private def ob106Power3 : QuotientMatrix := quotientDecode #v[3722, 2326, 3212, 775, 3024, 3703, 1303, 2588, 2440, 3463, 4060, 1091]

private theorem ob106_power3 : value (obstruction106 ^ 3) = ob106Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob106_value) ob106_power2
  intro i
  fin_cases i <;> rfl

private def ob106Power4 : QuotientMatrix := quotientDecode #v[1561, 1892, 4092, 633, 3670, 1776, 454, 3597, 2066, 1577, 3036, 739]

private theorem ob106_power4 : value (obstruction106 ^ 4) = ob106Power4 := by
  apply power_step _ 2 2 _ _ _ ob106_power2 ob106_power2
  intro i
  fin_cases i <;> rfl

private def ob106Power7 : QuotientMatrix := quotientDecode #v[1030, 3135, 2743, 186, 3397, 2295, 793, 1817, 1669, 417, 2844, 2919]

private theorem ob106_power7 : value (obstruction106 ^ 7) = ob106Power7 := by
  apply power_step _ 3 4 _ _ _ ob106_power3 ob106_power4
  intro i
  fin_cases i <;> rfl

private def ob106Power8 : QuotientMatrix := quotientDecode #v[1987, 3373, 3564, 2857, 2078, 2712, 3905, 1162, 3025, 3941, 192, 3695]

private theorem ob106_power8 : value (obstruction106 ^ 8) = ob106Power8 := by
  apply power_step _ 4 4 _ _ _ ob106_power4 ob106_power4
  intro i
  fin_cases i <;> rfl

private def ob106Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob106_power15 : value (obstruction106 ^ 15) = ob106Power15 := by
  apply power_step _ 7 8 _ _ _ ob106_power7 ob106_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction106_small_power : (obstruction106 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction106 ^ 15) = 1
  rw [ob106_power15]
  exact decode_identity

private theorem obstruction106_nonidentity : obstruction106 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob106_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3722, 2326, 3212, 775, 3024, 3703, 1303, 2588, 2440, 3463, 4060, 1091]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative106 :
    representative 106 ∈ involutionMatrixLineStabilizer ∨
    representative 106 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 106), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction106 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 106)).pow_mem obstruction106_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction106_small_power obstruction106_nonidentity

private theorem r107_value : value (representative 107) = wordMatrix483 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix483_expansion.symm

private def obstruction107 : quotientSubgroup := (representative 107) * ((sylowGenerator 3) * ((sylowGenerator 1) * ((sylowGenerator 2))))

private def ob107M2 : QuotientMatrix := quotientDecode #v[1588, 3320, 2189, 3146, 598, 2044, 2170, 1958, 3401, 4028, 1047, 3951]

private theorem ob107_mul2 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] = ob107M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob107M1 : QuotientMatrix := quotientDecode #v[2384, 3474, 2691, 595, 3670, 634, 1942, 2472, 2119, 2725, 1024, 1803]

private theorem ob107_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob107M2 = ob107M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob107M0 : QuotientMatrix := quotientDecode #v[3426, 3766, 3424, 763, 2021, 1609, 2216, 3176, 1164, 3100, 1903, 2186]

private theorem ob107_mul0 : quotientDecode #v[1010, 682, 2511, 3814, 1867, 3086, 406, 2984, 727, 3582, 3868, 1839] * ob107M1 = ob107M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob107_value : value (obstruction107) = ob107M0 := by
  simp only [obstruction107, r107_value, s3_value, s1_value, s2_value, map_mul]
  change quotientDecode #v[1010, 682, 2511, 3814, 1867, 3086, 406, 2984, 727, 3582, 3868, 1839] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184]))) = _
  rw [ob107_mul2, ob107_mul1, ob107_mul0]

private theorem obstruction107_mem : obstruction107 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 107)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 107)).mul_mem (representative_mem_join 107) ((baseSubgroup ⊔ Subgroup.zpowers (representative 107)).mul_mem (sylow_mem_join 107 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 107)).mul_mem (sylow_mem_join 107 1) (sylow_mem_join 107 2))))

private def ob107Power2 : QuotientMatrix := quotientDecode #v[2878, 3563, 1416, 2143, 3444, 3138, 80, 1023, 1180, 1947, 3409, 2223]

private theorem ob107_power2 : value (obstruction107 ^ 2) = ob107Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob107_value) (by rw [pow_one]; exact ob107_value)
  intro i
  fin_cases i <;> rfl

private def ob107Power3 : QuotientMatrix := quotientDecode #v[155, 2255, 3440, 2952, 3853, 2555, 3917, 435, 889, 1373, 2374, 3812]

private theorem ob107_power3 : value (obstruction107 ^ 3) = ob107Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob107_value) ob107_power2
  intro i
  fin_cases i <;> rfl

private def ob107Power5 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob107_power5 : value (obstruction107 ^ 5) = ob107Power5 := by
  apply power_step _ 2 3 _ _ _ ob107_power2 ob107_power3
  intro i
  fin_cases i <;> rfl

private theorem obstruction107_small_power : (obstruction107 ^ 1) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction107 ^ 5) = 1
  rw [ob107_power5]
  exact decode_identity

private theorem obstruction107_nonidentity : obstruction107 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob107_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3426, 3766, 3424, 763, 2021, 1609, 2216, 3176, 1164, 3100, 1903, 2186]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative107 :
    representative 107 ∈ involutionMatrixLineStabilizer ∨
    representative 107 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 107), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction107 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 107)).pow_mem obstruction107_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction107_small_power obstruction107_nonidentity

private theorem r108_value : value (representative 108) = wordMatrix487 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix487_expansion.symm

private def obstruction108 : quotientSubgroup := (representative 108) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob108M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob108_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob108M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob108M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob108_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob108M3 = ob108M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob108M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob108_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob108M2 = ob108M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob108M0 : QuotientMatrix := quotientDecode #v[1909, 2992, 1648, 1098, 2509, 3267, 2710, 3099, 1227, 2166, 3625, 1949]

private theorem ob108_mul0 : quotientDecode #v[3004, 1197, 40, 1828, 2113, 1460, 2724, 90, 2474, 2727, 3398, 924] * ob108M1 = ob108M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob108_value : value (obstruction108) = ob108M0 := by
  simp only [obstruction108, r108_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3004, 1197, 40, 1828, 2113, 1460, 2724, 90, 2474, 2727, 3398, 924] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob108_mul3, ob108_mul2, ob108_mul1, ob108_mul0]

private theorem obstruction108_mem : obstruction108 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 108)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 108)).mul_mem (representative_mem_join 108) ((baseSubgroup ⊔ Subgroup.zpowers (representative 108)).mul_mem (sylow_mem_join 108 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 108)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 108)).inv_mem (sylow_mem_join 108 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 108)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 108)).inv_mem (sylow_mem_join 108 2)) (sylow_mem_join 108 1)))))

private def ob108Power2 : QuotientMatrix := quotientDecode #v[3081, 565, 2503, 2885, 148, 1020, 2045, 2294, 43, 1477, 3646, 525]

private theorem ob108_power2 : value (obstruction108 ^ 2) = ob108Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob108_value) (by rw [pow_one]; exact ob108_value)
  intro i
  fin_cases i <;> rfl

private def ob108Power3 : QuotientMatrix := quotientDecode #v[2699, 3197, 3950, 179, 934, 3332, 1112, 2526, 1100, 3434, 3398, 3385]

private theorem ob108_power3 : value (obstruction108 ^ 3) = ob108Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob108_value) ob108_power2
  intro i
  fin_cases i <;> rfl

private def ob108Power4 : QuotientMatrix := quotientDecode #v[2943, 867, 2774, 1488, 421, 2831, 2360, 1436, 1669, 1232, 2601, 2894]

private theorem ob108_power4 : value (obstruction108 ^ 4) = ob108Power4 := by
  apply power_step _ 2 2 _ _ _ ob108_power2 ob108_power2
  intro i
  fin_cases i <;> rfl

private def ob108Power7 : QuotientMatrix := quotientDecode #v[1998, 1676, 3424, 1834, 1395, 3380, 1892, 3247, 3095, 870, 1903, 999]

private theorem ob108_power7 : value (obstruction108 ^ 7) = ob108Power7 := by
  apply power_step _ 3 4 _ _ _ ob108_power3 ob108_power4
  intro i
  fin_cases i <;> rfl

private def ob108Power8 : QuotientMatrix := quotientDecode #v[3475, 2174, 2858, 429, 2495, 3585, 689, 1939, 2764, 1832, 2622, 3142]

private theorem ob108_power8 : value (obstruction108 ^ 8) = ob108Power8 := by
  apply power_step _ 4 4 _ _ _ ob108_power4 ob108_power4
  intro i
  fin_cases i <;> rfl

private def ob108Power15 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob108_power15 : value (obstruction108 ^ 15) = ob108Power15 := by
  apply power_step _ 7 8 _ _ _ ob108_power7 ob108_power8
  intro i
  fin_cases i <;> rfl

private theorem obstruction108_small_power : (obstruction108 ^ 3) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction108 ^ 15) = 1
  rw [ob108_power15]
  exact decode_identity

private theorem obstruction108_nonidentity : obstruction108 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob108_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[2699, 3197, 3950, 179, 934, 3332, 1112, 2526, 1100, 3434, 3398, 3385]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative108 :
    representative 108 ∈ involutionMatrixLineStabilizer ∨
    representative 108 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 108), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction108 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 108)).pow_mem obstruction108_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction108_small_power obstruction108_nonidentity

private theorem r109_value : value (representative 109) = wordMatrix490 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix490_expansion.symm

private def obstruction109 : quotientSubgroup := (representative 109) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob109M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob109_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob109M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob109M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob109_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob109M2 = ob109M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob109M0 : QuotientMatrix := quotientDecode #v[89, 1520, 2590, 1473, 2264, 1800, 454, 3159, 3740, 563, 3646, 1187]

private theorem ob109_mul0 : quotientDecode #v[265, 81, 2772, 1807, 3316, 372, 3396, 2214, 3414, 3570, 3398, 3735] * ob109M1 = ob109M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob109_value : value (obstruction109) = ob109M0 := by
  simp only [obstruction109, r109_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[265, 81, 2772, 1807, 3316, 372, 3396, 2214, 3414, 3570, 3398, 3735] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob109_mul2, ob109_mul1, ob109_mul0]

private theorem obstruction109_mem : obstruction109 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 109)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 109)).mul_mem (representative_mem_join 109) ((baseSubgroup ⊔ Subgroup.zpowers (representative 109)).mul_mem (sylow_mem_join 109 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 109)).mul_mem (sylow_mem_join 109 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 109)).inv_mem (sylow_mem_join 109 2)))))

private def ob109Power2 : QuotientMatrix := quotientDecode #v[3206, 739, 1127, 3434, 1067, 1872, 3299, 3124, 1022, 2122, 3409, 200]

private theorem ob109_power2 : value (obstruction109 ^ 2) = ob109Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob109_value) (by rw [pow_one]; exact ob109_value)
  intro i
  fin_cases i <;> rfl

private def ob109Power3 : QuotientMatrix := quotientDecode #v[2340, 3331, 1863, 766, 2398, 2959, 1453, 3923, 1217, 1364, 3398, 2128]

private theorem ob109_power3 : value (obstruction109 ^ 3) = ob109Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob109_value) ob109_power2
  intro i
  fin_cases i <;> rfl

private def ob109Power5 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob109_power5 : value (obstruction109 ^ 5) = ob109Power5 := by
  apply power_step _ 2 3 _ _ _ ob109_power2 ob109_power3
  intro i
  fin_cases i <;> rfl

private theorem obstruction109_small_power : (obstruction109 ^ 1) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction109 ^ 5) = 1
  rw [ob109_power5]
  exact decode_identity

private theorem obstruction109_nonidentity : obstruction109 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob109_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 3) h
  have hn : (quotientDecode #v[89, 1520, 2590, 1473, 2264, 1800, 454, 3159, 3740, 563, 3646, 1187]) 0 3 ≠ (1 : QuotientMatrix) 0 3 := by decide +kernel
  exact hn hc

theorem alternative109 :
    representative 109 ∈ involutionMatrixLineStabilizer ∨
    representative 109 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 109), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction109 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 109)).pow_mem obstruction109_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction109_small_power obstruction109_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
