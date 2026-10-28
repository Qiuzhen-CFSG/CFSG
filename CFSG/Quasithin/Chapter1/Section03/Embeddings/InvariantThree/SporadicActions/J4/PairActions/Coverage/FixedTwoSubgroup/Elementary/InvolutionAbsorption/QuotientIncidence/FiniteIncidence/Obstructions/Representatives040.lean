module

public import CFSG.Quasithin.Chapter1.Section03.Embeddings.InvariantThree.SporadicActions.J4.PairActions.Coverage.FixedTwoSubgroup.Elementary.InvolutionAbsorption.QuotientIncidence.FiniteIncidence.Obstructions.Second
import Mathlib.Tactic.FinCases

/-!
# The representative alternatives at indices 40 through 49

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

private theorem r40_value : value (representative 40) = wordMatrix230 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix230_expansion.symm

private def obstruction40 : quotientSubgroup := (representative 40) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob40M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob40_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob40M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob40M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob40_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob40M3 = ob40M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob40M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob40_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob40M2 = ob40M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob40M0 : QuotientMatrix := quotientDecode #v[2184, 999, 285, 462, 888, 3937, 370, 2796, 1323, 3880, 2552, 1208]

private theorem ob40_mul0 : quotientDecode #v[2071, 2422, 433, 1577, 1912, 1475, 3514, 1113, 717, 3734, 1868, 1984] * ob40M1 = ob40M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob40_value : value (obstruction40) = ob40M0 := by
  simp only [obstruction40, r40_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2071, 2422, 433, 1577, 1912, 1475, 3514, 1113, 717, 3734, 1868, 1984] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob40_mul3, ob40_mul2, ob40_mul1, ob40_mul0]

private theorem obstruction40_mem : obstruction40 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 40)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 40)).mul_mem (representative_mem_join 40) ((baseSubgroup ⊔ Subgroup.zpowers (representative 40)).mul_mem (sylow_mem_join 40 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 40)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 40)).inv_mem (sylow_mem_join 40 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 40)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 40)).inv_mem (sylow_mem_join 40 2)) (sylow_mem_join 40 1)))))

private def ob40Power2 : QuotientMatrix := quotientDecode #v[3994, 1166, 3592, 3457, 1702, 472, 2983, 4028, 2323, 2540, 2010, 3779]

private theorem ob40_power2 : value (obstruction40 ^ 2) = ob40Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob40_value) (by rw [pow_one]; exact ob40_value)
  intro i
  fin_cases i <;> rfl

private def ob40Power3 : QuotientMatrix := quotientDecode #v[3326, 32, 934, 2575, 423, 3075, 324, 357, 2436, 1471, 2356, 665]

private theorem ob40_power3 : value (obstruction40 ^ 3) = ob40Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob40_value) ob40_power2
  intro i
  fin_cases i <;> rfl

private def ob40Power5 : QuotientMatrix := quotientDecode #v[3451, 472, 1053, 4018, 619, 525, 3260, 766, 1636, 3734, 3750, 749]

private theorem ob40_power5 : value (obstruction40 ^ 5) = ob40Power5 := by
  apply power_step _ 2 3 _ _ _ ob40_power2 ob40_power3
  intro i
  fin_cases i <;> rfl

private def ob40Power10 : QuotientMatrix := quotientDecode #v[1508, 1535, 2585, 2041, 822, 2114, 1404, 2757, 2716, 1933, 2027, 1037]

private theorem ob40_power10 : value (obstruction40 ^ 10) = ob40Power10 := by
  apply power_step _ 5 5 _ _ _ ob40_power5 ob40_power5
  intro i
  fin_cases i <;> rfl

private def ob40Power6 : QuotientMatrix := quotientDecode #v[4001, 3075, 731, 593, 2970, 1907, 2918, 2971, 2526, 2310, 1311, 908]

private theorem ob40_power6 : value (obstruction40 ^ 6) = ob40Power6 := by
  apply power_step _ 3 3 _ _ _ ob40_power3 ob40_power3
  intro i
  fin_cases i <;> rfl

private def ob40Power11 : QuotientMatrix := quotientDecode #v[2353, 232, 430, 3386, 1248, 1581, 363, 2459, 727, 332, 3493, 419]

private theorem ob40_power11 : value (obstruction40 ^ 11) = ob40Power11 := by
  apply power_step _ 5 6 _ _ _ ob40_power5 ob40_power6
  intro i
  fin_cases i <;> rfl

private def ob40Power21 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob40_power21 : value (obstruction40 ^ 21) = ob40Power21 := by
  apply power_step _ 10 11 _ _ _ ob40_power10 ob40_power11
  intro i
  fin_cases i <;> rfl

private theorem obstruction40_small_power : (obstruction40 ^ 3) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction40 ^ 21) = 1
  rw [ob40_power21]
  exact decode_identity

private theorem obstruction40_nonidentity : obstruction40 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob40_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3326, 32, 934, 2575, 423, 3075, 324, 357, 2436, 1471, 2356, 665]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative40 :
    representative 40 ∈ involutionMatrixLineStabilizer ∨
    representative 40 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 40), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction40 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 40)).pow_mem obstruction40_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction40_small_power obstruction40_nonidentity

private theorem r41_value : value (representative 41) = wordMatrix233 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix233_expansion.symm

private def obstruction41 : quotientSubgroup := (representative 41) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob41M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob41_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob41M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob41M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob41_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob41M2 = ob41M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob41M0 : QuotientMatrix := quotientDecode #v[225, 219, 822, 2074, 3850, 2733, 965, 2488, 512, 3529, 3947, 3460]

private theorem ob41_mul0 : quotientDecode #v[734, 668, 614, 1204, 1420, 3615, 3448, 1767, 2343, 3707, 1868, 1662] * ob41M1 = ob41M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob41_value : value (obstruction41) = ob41M0 := by
  simp only [obstruction41, r41_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[734, 668, 614, 1204, 1420, 3615, 3448, 1767, 2343, 3707, 1868, 1662] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob41_mul2, ob41_mul1, ob41_mul0]

private theorem obstruction41_mem : obstruction41 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 41)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 41)).mul_mem (representative_mem_join 41) ((baseSubgroup ⊔ Subgroup.zpowers (representative 41)).mul_mem (sylow_mem_join 41 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 41)).mul_mem (sylow_mem_join 41 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 41)).inv_mem (sylow_mem_join 41 2)))))

private def ob41Power2 : QuotientMatrix := quotientDecode #v[49, 3415, 2435, 2639, 1511, 2197, 1635, 2945, 3529, 617, 3182, 2657]

private theorem ob41_power2 : value (obstruction41 ^ 2) = ob41Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob41_value) (by rw [pow_one]; exact ob41_value)
  intro i
  fin_cases i <;> rfl

private def ob41Power3 : QuotientMatrix := quotientDecode #v[1350, 3884, 1542, 2206, 3767, 2273, 3056, 2836, 617, 3162, 112, 2500]

private theorem ob41_power3 : value (obstruction41 ^ 3) = ob41Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob41_value) ob41_power2
  intro i
  fin_cases i <;> rfl

private def ob41Power5 : QuotientMatrix := quotientDecode #v[784, 758, 2771, 2716, 1648, 3879, 1361, 2469, 1761, 659, 2833, 969]

private theorem ob41_power5 : value (obstruction41 ^ 5) = ob41Power5 := by
  apply power_step _ 2 3 _ _ _ ob41_power2 ob41_power3
  intro i
  fin_cases i <;> rfl

private def ob41Power10 : QuotientMatrix := quotientDecode #v[514, 3861, 2616, 3776, 1412, 2232, 3521, 2665, 2369, 3232, 731, 266]

private theorem ob41_power10 : value (obstruction41 ^ 10) = ob41Power10 := by
  apply power_step _ 5 5 _ _ _ ob41_power5 ob41_power5
  intro i
  fin_cases i <;> rfl

private def ob41Power6 : QuotientMatrix := quotientDecode #v[195, 510, 1280, 3539, 1216, 1159, 325, 3910, 659, 2881, 3494, 3407]

private theorem ob41_power6 : value (obstruction41 ^ 6) = ob41Power6 := by
  apply power_step _ 3 3 _ _ _ ob41_power3 ob41_power3
  intro i
  fin_cases i <;> rfl

private def ob41Power11 : QuotientMatrix := quotientDecode #v[3346, 507, 3568, 1371, 2021, 2433, 2675, 478, 3232, 506, 158, 2753]

private theorem ob41_power11 : value (obstruction41 ^ 11) = ob41Power11 := by
  apply power_step _ 5 6 _ _ _ ob41_power5 ob41_power6
  intro i
  fin_cases i <;> rfl

private def ob41Power21 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob41_power21 : value (obstruction41 ^ 21) = ob41Power21 := by
  apply power_step _ 10 11 _ _ _ ob41_power10 ob41_power11
  intro i
  fin_cases i <;> rfl

private theorem obstruction41_small_power : (obstruction41 ^ 3) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction41 ^ 21) = 1
  rw [ob41_power21]
  exact decode_identity

private theorem obstruction41_nonidentity : obstruction41 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob41_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[1350, 3884, 1542, 2206, 3767, 2273, 3056, 2836, 617, 3162, 112, 2500]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative41 :
    representative 41 ∈ involutionMatrixLineStabilizer ∨
    representative 41 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 41), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction41 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 41)).pow_mem obstruction41_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction41_small_power obstruction41_nonidentity

private theorem r42_value : value (representative 42) = wordMatrix237 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix237_expansion.symm

private def obstruction42 : quotientSubgroup := (representative 42) * ((sylowGenerator 3) * ((sylowGenerator 1) * ((sylowGenerator 2))))

private def ob42M2 : QuotientMatrix := quotientDecode #v[1588, 3320, 2189, 3146, 598, 2044, 2170, 1958, 3401, 4028, 1047, 3951]

private theorem ob42_mul2 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] = ob42M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob42M1 : QuotientMatrix := quotientDecode #v[2384, 3474, 2691, 595, 3670, 634, 1942, 2472, 2119, 2725, 1024, 1803]

private theorem ob42_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob42M2 = ob42M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob42M0 : QuotientMatrix := quotientDecode #v[7, 530, 2691, 1958, 3444, 2178, 611, 2567, 2917, 1448, 602, 3676]

private theorem ob42_mul0 : quotientDecode #v[349, 240, 4, 3470, 3128, 1118, 3526, 1442, 3368, 3064, 3236, 2396] * ob42M1 = ob42M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob42_value : value (obstruction42) = ob42M0 := by
  simp only [obstruction42, r42_value, s3_value, s1_value, s2_value, map_mul]
  change quotientDecode #v[349, 240, 4, 3470, 3128, 1118, 3526, 1442, 3368, 3064, 3236, 2396] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184]))) = _
  rw [ob42_mul2, ob42_mul1, ob42_mul0]

private theorem obstruction42_mem : obstruction42 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 42)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 42)).mul_mem (representative_mem_join 42) ((baseSubgroup ⊔ Subgroup.zpowers (representative 42)).mul_mem (sylow_mem_join 42 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 42)).mul_mem (sylow_mem_join 42 1) (sylow_mem_join 42 2))))

private def ob42Power2 : QuotientMatrix := quotientDecode #v[2198, 2766, 998, 1667, 2677, 1609, 3420, 866, 244, 3100, 3851, 2972]

private theorem ob42_power2 : value (obstruction42 ^ 2) = ob42Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob42_value) (by rw [pow_one]; exact ob42_value)
  intro i
  fin_cases i <;> rfl

private def ob42Power3 : QuotientMatrix := quotientDecode #v[446, 3239, 1722, 4064, 1765, 560, 1361, 1598, 1809, 3159, 1912, 2759]

private theorem ob42_power3 : value (obstruction42 ^ 3) = ob42Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob42_value) ob42_power2
  intro i
  fin_cases i <;> rfl

private def ob42Power5 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob42_power5 : value (obstruction42 ^ 5) = ob42Power5 := by
  apply power_step _ 2 3 _ _ _ ob42_power2 ob42_power3
  intro i
  fin_cases i <;> rfl

private theorem obstruction42_small_power : (obstruction42 ^ 1) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction42 ^ 5) = 1
  rw [ob42_power5]
  exact decode_identity

private theorem obstruction42_nonidentity : obstruction42 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob42_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[7, 530, 2691, 1958, 3444, 2178, 611, 2567, 2917, 1448, 602, 3676]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative42 :
    representative 42 ∈ involutionMatrixLineStabilizer ∨
    representative 42 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 42), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction42 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 42)).pow_mem obstruction42_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction42_small_power obstruction42_nonidentity

private theorem r43_value : value (representative 43) = wordMatrix242 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix242_expansion.symm

private def obstruction43 : quotientSubgroup := (representative 43) * ((sylowGenerator 1) * ((sylowGenerator 0) * ((sylowGenerator 2)⁻¹)))

private def ob43M2 : QuotientMatrix := quotientDecode #v[4061, 454, 3919, 1894, 323, 2202, 2866, 1307, 3827, 1141, 1024, 1172]

private theorem ob43_mul2 : quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] = ob43M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob43M1 : QuotientMatrix := quotientDecode #v[2704, 4088, 1501, 2567, 162, 3451, 4034, 1033, 206, 2986, 1047, 3840]

private theorem ob43_mul1 : quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * ob43M2 = ob43M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob43M0 : QuotientMatrix := quotientDecode #v[3861, 2941, 2027, 2369, 1633, 3497, 1281, 3071, 1113, 3085, 602, 2742]

private theorem ob43_mul0 : quotientDecode #v[2972, 2524, 33, 1141, 4080, 1579, 3268, 2633, 1310, 180, 309, 1864] * ob43M1 = ob43M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob43_value : value (obstruction43) = ob43M0 := by
  simp only [obstruction43, r43_value, s1_value, s0_value, s2_inverse_value, map_mul]
  change quotientDecode #v[2972, 2524, 33, 1141, 4080, 1579, 3268, 2633, 1310, 180, 309, 1864] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999]))) = _
  rw [ob43_mul2, ob43_mul1, ob43_mul0]

private theorem obstruction43_mem : obstruction43 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 43)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 43)).mul_mem (representative_mem_join 43) ((baseSubgroup ⊔ Subgroup.zpowers (representative 43)).mul_mem (sylow_mem_join 43 1) ((baseSubgroup ⊔ Subgroup.zpowers (representative 43)).mul_mem (sylow_mem_join 43 0) ((baseSubgroup ⊔ Subgroup.zpowers (representative 43)).inv_mem (sylow_mem_join 43 2)))))

private def ob43Power2 : QuotientMatrix := quotientDecode #v[3623, 3476, 1136, 1275, 2538, 3255, 2326, 3350, 1902, 2387, 3409, 2586]

private theorem ob43_power2 : value (obstruction43 ^ 2) = ob43Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob43_value) (by rw [pow_one]; exact ob43_value)
  intro i
  fin_cases i <;> rfl

private def ob43Power3 : QuotientMatrix := quotientDecode #v[2763, 1728, 3219, 2629, 3972, 2904, 1048, 1602, 1905, 2535, 192, 742]

private theorem ob43_power3 : value (obstruction43 ^ 3) = ob43Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob43_value) ob43_power2
  intro i
  fin_cases i <;> rfl

private def ob43Power5 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob43_power5 : value (obstruction43 ^ 5) = ob43Power5 := by
  apply power_step _ 2 3 _ _ _ ob43_power2 ob43_power3
  intro i
  fin_cases i <;> rfl

private theorem obstruction43_small_power : (obstruction43 ^ 1) ^ 5 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction43 ^ 5) = 1
  rw [ob43_power5]
  exact decode_identity

private theorem obstruction43_nonidentity : obstruction43 ^ 1 ≠ 1 := by
  apply ne_one_of_value _ _ (by rw [pow_one]; exact ob43_value)
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[3861, 2941, 2027, 2369, 1633, 3497, 1281, 3071, 1113, 3085, 602, 2742]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative43 :
    representative 43 ∈ involutionMatrixLineStabilizer ∨
    representative 43 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 43), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction43 ^ 1,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 43)).pow_mem obstruction43_mem 1, ?_⟩)
  exact coprime_power_obstruction _ 5 (by decide +kernel)
    obstruction43_small_power obstruction43_nonidentity

private theorem r44_value : value (representative 44) = wordMatrix245 := by
  change ((evaluate [(false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix245_expansion.symm

private theorem r44_inverse_value :
    value ((representative 44)⁻¹) = quotientDecode #v[1, 1804, 306, 2575, 575, 236, 1555, 2836, 1301, 3377, 1047, 1882] := by
  apply inverse_value _ _ _ r44_value
  intro i
  fin_cases i <;> rfl

theorem r44_line : representative 44 ∈ involutionMatrixLineStabilizer := by
  apply line_mem_of_inverse _ _ 1024 1047 23 r44_inverse_value
  · rfl
  · rfl
  · rfl
  · change {involutionMatrixVector 1024, involutionMatrixVector 1047,
      involutionMatrixVector 23} =
      {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]

theorem alternative44 :
    representative 44 ∈ involutionMatrixLineStabilizer ∨
    representative 44 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 44), x ^ 2304 ≠ 1 := by
  exact Or.inl r44_line

private theorem r45_value : value (representative 45) = wordMatrix250 := by
  change ((evaluate [(true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix250_expansion.symm

private theorem r45_inverse_value :
    value ((representative 45)⁻¹) = quotientDecode #v[2431, 161, 162, 113, 3435, 3653, 86, 2917, 2412, 478, 1024, 1166] := by
  apply inverse_value _ _ _ r45_value
  intro i
  fin_cases i <;> rfl

theorem r45_line : representative 45 ∈ involutionMatrixLineStabilizer := by
  apply line_mem_of_inverse _ _ 1047 1024 23 r45_inverse_value
  · rfl
  · rfl
  · rfl
  · change {involutionMatrixVector 1047, involutionMatrixVector 1024,
      involutionMatrixVector 23} =
      {involutionMatrixVector 23, involutionMatrixVector 1024, involutionMatrixVector 1047}
    ext v
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_comm, or_left_comm, or_assoc]

theorem alternative45 :
    representative 45 ∈ involutionMatrixLineStabilizer ∨
    representative 45 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 45), x ^ 2304 ≠ 1 := by
  exact Or.inl r45_line

private theorem r46_value : value (representative 46) = wordMatrix253 := by
  change ((evaluate [(true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix253_expansion.symm

private def obstruction46 : quotientSubgroup := (representative 46) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob46M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob46_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob46M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob46M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob46_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob46M3 = ob46M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob46M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob46_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob46M2 = ob46M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob46M0 : QuotientMatrix := quotientDecode #v[2825, 3839, 25, 757, 2961, 3753, 2875, 3322, 3647, 3707, 2819, 3422]

private theorem ob46_mul0 : quotientDecode #v[3581, 2077, 162, 757, 977, 2383, 722, 2285, 2006, 1104, 1292, 12] * ob46M1 = ob46M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob46_value : value (obstruction46) = ob46M0 := by
  simp only [obstruction46, r46_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[3581, 2077, 162, 757, 977, 2383, 722, 2285, 2006, 1104, 1292, 12] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob46_mul3, ob46_mul2, ob46_mul1, ob46_mul0]

private theorem obstruction46_mem : obstruction46 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 46)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 46)).mul_mem (representative_mem_join 46) ((baseSubgroup ⊔ Subgroup.zpowers (representative 46)).mul_mem (sylow_mem_join 46 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 46)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 46)).inv_mem (sylow_mem_join 46 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 46)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 46)).inv_mem (sylow_mem_join 46 2)) (sylow_mem_join 46 1)))))

private def ob46Power2 : QuotientMatrix := quotientDecode #v[1254, 3525, 621, 1938, 376, 905, 3873, 2222, 2564, 294, 2284, 1243]

private theorem ob46_power2 : value (obstruction46 ^ 2) = ob46Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob46_value) (by rw [pow_one]; exact ob46_value)
  intro i
  fin_cases i <;> rfl

private def ob46Power3 : QuotientMatrix := quotientDecode #v[3213, 1203, 524, 723, 713, 1346, 953, 798, 828, 3696, 1754, 80]

private theorem ob46_power3 : value (obstruction46 ^ 3) = ob46Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob46_value) ob46_power2
  intro i
  fin_cases i <;> rfl

private def ob46Power5 : QuotientMatrix := quotientDecode #v[1408, 2960, 1241, 3826, 1501, 12, 521, 608, 3116, 193, 1386, 3673]

private theorem ob46_power5 : value (obstruction46 ^ 5) = ob46Power5 := by
  apply power_step _ 2 3 _ _ _ ob46_power2 ob46_power3
  intro i
  fin_cases i <;> rfl

private def ob46Power10 : QuotientMatrix := quotientDecode #v[2854, 1289, 2988, 1498, 857, 2603, 2995, 708, 276, 1513, 3617, 1876]

private theorem ob46_power10 : value (obstruction46 ^ 10) = ob46Power10 := by
  apply power_step _ 5 5 _ _ _ ob46_power5 ob46_power5
  intro i
  fin_cases i <;> rfl

private def ob46Power6 : QuotientMatrix := quotientDecode #v[2502, 2673, 3759, 1056, 137, 748, 1927, 3049, 2584, 3272, 3236, 368]

private theorem ob46_power6 : value (obstruction46 ^ 6) = ob46Power6 := by
  apply power_step _ 3 3 _ _ _ ob46_power3 ob46_power3
  intro i
  fin_cases i <;> rfl

private def ob46Power11 : QuotientMatrix := quotientDecode #v[3413, 3264, 3493, 1382, 2322, 2703, 302, 2467, 1463, 1448, 3462, 3060]

private theorem ob46_power11 : value (obstruction46 ^ 11) = ob46Power11 := by
  apply power_step _ 5 6 _ _ _ ob46_power5 ob46_power6
  intro i
  fin_cases i <;> rfl

private def ob46Power21 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob46_power21 : value (obstruction46 ^ 21) = ob46Power21 := by
  apply power_step _ 10 11 _ _ _ ob46_power10 ob46_power11
  intro i
  fin_cases i <;> rfl

private theorem obstruction46_small_power : (obstruction46 ^ 3) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction46 ^ 21) = 1
  rw [ob46_power21]
  exact decode_identity

private theorem obstruction46_nonidentity : obstruction46 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob46_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 2) h
  have hn : (quotientDecode #v[3213, 1203, 524, 723, 713, 1346, 953, 798, 828, 3696, 1754, 80]) 0 2 ≠ (1 : QuotientMatrix) 0 2 := by decide +kernel
  exact hn hc

theorem alternative46 :
    representative 46 ∈ involutionMatrixLineStabilizer ∨
    representative 46 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 46), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction46 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 46)).pow_mem obstruction46_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction46_small_power obstruction46_nonidentity

private theorem r47_value : value (representative 47) = wordMatrix257 := by
  change ((evaluate [(true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix257_expansion.symm

private def obstruction47 : quotientSubgroup := (representative 47) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob47M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob47_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob47M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob47M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob47_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob47M3 = ob47M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob47M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob47_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob47M2 = ob47M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob47M0 : QuotientMatrix := quotientDecode #v[2205, 1230, 202, 1041, 743, 953, 3580, 655, 3026, 4003, 1405, 1265]

private theorem ob47_mul0 : quotientDecode #v[2785, 2921, 1850, 3749, 33, 564, 2847, 3080, 117, 2281, 927, 3221] * ob47M1 = ob47M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob47_value : value (obstruction47) = ob47M0 := by
  simp only [obstruction47, r47_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2785, 2921, 1850, 3749, 33, 564, 2847, 3080, 117, 2281, 927, 3221] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob47_mul3, ob47_mul2, ob47_mul1, ob47_mul0]

private theorem obstruction47_mem : obstruction47 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 47)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 47)).mul_mem (representative_mem_join 47) ((baseSubgroup ⊔ Subgroup.zpowers (representative 47)).mul_mem (sylow_mem_join 47 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 47)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 47)).inv_mem (sylow_mem_join 47 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 47)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 47)).inv_mem (sylow_mem_join 47 2)) (sylow_mem_join 47 1)))))

private def ob47Power2 : QuotientMatrix := quotientDecode #v[2271, 2587, 4012, 3847, 4080, 2860, 168, 1444, 2522, 2200, 3659, 973]

private theorem ob47_power2 : value (obstruction47 ^ 2) = ob47Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob47_value) (by rw [pow_one]; exact ob47_value)
  intro i
  fin_cases i <;> rfl

private def ob47Power3 : QuotientMatrix := quotientDecode #v[493, 503, 16, 2404, 3024, 2018, 1319, 3923, 616, 136, 2961, 1860]

private theorem ob47_power3 : value (obstruction47 ^ 3) = ob47Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob47_value) ob47_power2
  intro i
  fin_cases i <;> rfl

private def ob47Power4 : QuotientMatrix := quotientDecode #v[2910, 2406, 743, 428, 3348, 2312, 399, 1717, 1527, 1694, 2165, 3130]

private theorem ob47_power4 : value (obstruction47 ^ 4) = ob47Power4 := by
  apply power_step _ 2 2 _ _ _ ob47_power2 ob47_power2
  intro i
  fin_cases i <;> rfl

private def ob47Power7 : QuotientMatrix := quotientDecode #v[976, 1550, 3348, 941, 1405, 3144, 1109, 2437, 4021, 1817, 4012, 2164]

private theorem ob47_power7 : value (obstruction47 ^ 7) = ob47Power7 := by
  apply power_step _ 3 4 _ _ _ ob47_power3 ob47_power4
  intro i
  fin_cases i <;> rfl

private def ob47Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob47_power14 : value (obstruction47 ^ 14) = ob47Power14 := by
  apply power_step _ 7 7 _ _ _ ob47_power7 ob47_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction47_small_power : (obstruction47 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction47 ^ 14) = 1
  rw [ob47_power14]
  exact decode_identity

private theorem obstruction47_nonidentity : obstruction47 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob47_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 1) h
  have hn : (quotientDecode #v[2271, 2587, 4012, 3847, 4080, 2860, 168, 1444, 2522, 2200, 3659, 973]) 0 1 ≠ (1 : QuotientMatrix) 0 1 := by decide +kernel
  exact hn hc

theorem alternative47 :
    representative 47 ∈ involutionMatrixLineStabilizer ∨
    representative 47 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 47), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction47 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 47)).pow_mem obstruction47_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction47_small_power obstruction47_nonidentity

private theorem r48_value : value (representative 48) = wordMatrix260 := by
  change ((evaluate [(true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix260_expansion.symm

private def obstruction48 : quotientSubgroup := (representative 48) * ((sylowGenerator 2) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 0))))

private def ob48M2 : QuotientMatrix := quotientDecode #v[2077, 3396, 2181, 3915, 3531, 1439, 871, 3638, 1128, 3852, 1047, 1550]

private theorem ob48_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960] = ob48M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob48M1 : QuotientMatrix := quotientDecode #v[2704, 907, 1863, 3591, 3659, 901, 3029, 30, 579, 2343, 1047, 1907]

private theorem ob48_mul1 : quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * ob48M2 = ob48M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob48M0 : QuotientMatrix := quotientDecode #v[830, 363, 3531, 814, 1634, 3312, 3706, 920, 2143, 357, 1121, 1978]

private theorem ob48_mul0 : quotientDecode #v[1695, 3352, 3965, 1597, 764, 3333, 1881, 1480, 2770, 3386, 3134, 860] * ob48M1 = ob48M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob48_value : value (obstruction48) = ob48M0 := by
  simp only [obstruction48, r48_value, s2_value, s1_inverse_value, s0_value, map_mul]
  change quotientDecode #v[1695, 3352, 3965, 1597, 764, 3333, 1881, 1480, 2770, 3386, 3134, 860] * (quotientDecode #v[3816, 1734, 3436, 1246, 1365, 1279, 2408, 833, 385, 641, 1024, 2184] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[1966, 2, 1916, 317, 199, 3204, 3300, 3108, 3492, 3910, 1024, 3960]))) = _
  rw [ob48_mul2, ob48_mul1, ob48_mul0]

private theorem obstruction48_mem : obstruction48 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 48)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 48)).mul_mem (representative_mem_join 48) ((baseSubgroup ⊔ Subgroup.zpowers (representative 48)).mul_mem (sylow_mem_join 48 2) ((baseSubgroup ⊔ Subgroup.zpowers (representative 48)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 48)).inv_mem (sylow_mem_join 48 1)) (sylow_mem_join 48 0))))

private def ob48Power2 : QuotientMatrix := quotientDecode #v[3110, 2990, 1821, 2628, 1765, 1195, 1043, 4078, 786, 1056, 1493, 1556]

private theorem ob48_power2 : value (obstruction48 ^ 2) = ob48Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob48_value) (by rw [pow_one]; exact ob48_value)
  intro i
  fin_cases i <;> rfl

private def ob48Power3 : QuotientMatrix := quotientDecode #v[907, 3686, 1762, 1390, 2787, 2674, 86, 1149, 3635, 2193, 2379, 3757]

private theorem ob48_power3 : value (obstruction48 ^ 3) = ob48Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob48_value) ob48_power2
  intro i
  fin_cases i <;> rfl

private def ob48Power4 : QuotientMatrix := quotientDecode #v[3033, 3220, 1405, 314, 1432, 860, 1208, 3410, 2681, 382, 228, 13]

private theorem ob48_power4 : value (obstruction48 ^ 4) = ob48Power4 := by
  apply power_step _ 2 2 _ _ _ ob48_power2 ob48_power2
  intro i
  fin_cases i <;> rfl

private def ob48Power7 : QuotientMatrix := quotientDecode #v[34, 3994, 1976, 1450, 3208, 3995, 2249, 3334, 30, 798, 2235, 7]

private theorem ob48_power7 : value (obstruction48 ^ 7) = ob48Power7 := by
  apply power_step _ 3 4 _ _ _ ob48_power3 ob48_power4
  intro i
  fin_cases i <;> rfl

private def ob48Power14 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob48_power14 : value (obstruction48 ^ 14) = ob48Power14 := by
  apply power_step _ 7 7 _ _ _ ob48_power7 ob48_power7
  intro i
  fin_cases i <;> rfl

private theorem obstruction48_small_power : (obstruction48 ^ 2) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction48 ^ 14) = 1
  rw [ob48_power14]
  exact decode_identity

private theorem obstruction48_nonidentity : obstruction48 ^ 2 ≠ 1 := by
  apply ne_one_of_value _ _ ob48_power2
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[3110, 2990, 1821, 2628, 1765, 1195, 1043, 4078, 786, 1056, 1493, 1556]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative48 :
    representative 48 ∈ involutionMatrixLineStabilizer ∨
    representative 48 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 48), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction48 ^ 2,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 48)).pow_mem obstruction48_mem 2, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction48_small_power obstruction48_nonidentity

private theorem r49_value : value (representative 49) = wordMatrix262 := by
  change ((evaluate [(false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, 1), (false, 1), (true, -1), (false, 1), (true, -1), (false, 1), (true, 1), (false, 1)] : U) : QuotientMatrix) = _
  simp only [evaluate, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    Bool.false_eq_true, if_false, if_true, zpow_one, zpow_neg_one,
    Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, mul_one]
  exact wordMatrix262_expansion.symm

private def obstruction49 : quotientSubgroup := (representative 49) * ((sylowGenerator 3) * ((sylowGenerator 1)⁻¹ * ((sylowGenerator 2)⁻¹ * ((sylowGenerator 1)))))

private def ob49M3 : QuotientMatrix := quotientDecode #v[3274, 3904, 233, 1273, 884, 1835, 2392, 1668, 3622, 1207, 1047, 1790]

private theorem ob49_mul3 : quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155] = ob49M3 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob49M2 : QuotientMatrix := quotientDecode #v[3186, 1406, 1861, 1532, 3678, 3585, 475, 3058, 2247, 931, 1024, 236]

private theorem ob49_mul2 : quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * ob49M3 = ob49M2 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob49M1 : QuotientMatrix := quotientDecode #v[2704, 2160, 857, 3591, 430, 2167, 3010, 30, 586, 2361, 1047, 2207]

private theorem ob49_mul1 : quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * ob49M2 = ob49M1 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private def ob49M0 : QuotientMatrix := quotientDecode #v[2682, 2684, 400, 2443, 1937, 2781, 2375, 775, 613, 3459, 1656, 3411]

private theorem ob49_mul0 : quotientDecode #v[2752, 101, 3435, 2342, 456, 784, 1209, 2886, 1737, 1825, 2616, 2271] * ob49M1 = ob49M0 := by
  apply mul_eq_of_packed
  intro i
  fin_cases i <;> rfl

private theorem ob49_value : value (obstruction49) = ob49M0 := by
  simp only [obstruction49, r49_value, s3_value, s1_inverse_value, s2_inverse_value, s1_value, map_mul]
  change quotientDecode #v[2752, 101, 3435, 2342, 456, 784, 1209, 2886, 1737, 1825, 2616, 2271] * (quotientDecode #v[1780, 3065, 1650, 3345, 2920, 2733, 1247, 3470, 2535, 2800, 1047, 100] * (quotientDecode #v[3664, 3396, 910, 1007, 141, 1194, 594, 3843, 1373, 4059, 1047, 3333] * (quotientDecode #v[2792, 454, 1092, 222, 3965, 2752, 2408, 1857, 3241, 4009, 1024, 3999] * (quotientDecode #v[2640, 213, 1708, 1007, 3134, 2062, 594, 3843, 1128, 3833, 1047, 1155])))) = _
  rw [ob49_mul3, ob49_mul2, ob49_mul1, ob49_mul0]

private theorem obstruction49_mem : obstruction49 ∈ (baseSubgroup ⊔ Subgroup.zpowers (representative 49)) :=
  ((baseSubgroup ⊔ Subgroup.zpowers (representative 49)).mul_mem (representative_mem_join 49) ((baseSubgroup ⊔ Subgroup.zpowers (representative 49)).mul_mem (sylow_mem_join 49 3) ((baseSubgroup ⊔ Subgroup.zpowers (representative 49)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 49)).inv_mem (sylow_mem_join 49 1)) ((baseSubgroup ⊔ Subgroup.zpowers (representative 49)).mul_mem ((baseSubgroup ⊔ Subgroup.zpowers (representative 49)).inv_mem (sylow_mem_join 49 2)) (sylow_mem_join 49 1)))))

private def ob49Power2 : QuotientMatrix := quotientDecode #v[1836, 3264, 1779, 1468, 1906, 3936, 2023, 3696, 1523, 2639, 1659, 1950]

private theorem ob49_power2 : value (obstruction49 ^ 2) = ob49Power2 := by
  apply power_step _ 1 1 _ _ _ (by rw [pow_one]; exact ob49_value) (by rw [pow_one]; exact ob49_value)
  intro i
  fin_cases i <;> rfl

private def ob49Power3 : QuotientMatrix := quotientDecode #v[2904, 363, 3313, 589, 2025, 1879, 2197, 675, 791, 394, 1661, 3951]

private theorem ob49_power3 : value (obstruction49 ^ 3) = ob49Power3 := by
  apply power_step _ 1 2 _ _ _ (by rw [pow_one]; exact ob49_value) ob49_power2
  intro i
  fin_cases i <;> rfl

private def ob49Power5 : QuotientMatrix := quotientDecode #v[3339, 804, 1868, 2507, 3488, 1101, 3907, 179, 1489, 767, 1954, 3709]

private theorem ob49_power5 : value (obstruction49 ^ 5) = ob49Power5 := by
  apply power_step _ 2 3 _ _ _ ob49_power2 ob49_power3
  intro i
  fin_cases i <;> rfl

private def ob49Power10 : QuotientMatrix := quotientDecode #v[3050, 1071, 328, 952, 2288, 2925, 3997, 1905, 3368, 1098, 1878, 3586]

private theorem ob49_power10 : value (obstruction49 ^ 10) = ob49Power10 := by
  apply power_step _ 5 5 _ _ _ ob49_power5 ob49_power5
  intro i
  fin_cases i <;> rfl

private def ob49Power6 : QuotientMatrix := quotientDecode #v[195, 1195, 2242, 3323, 148, 3422, 3468, 3661, 950, 658, 2616, 194]

private theorem ob49_power6 : value (obstruction49 ^ 6) = ob49Power6 := by
  apply power_step _ 3 3 _ _ _ ob49_power3 ob49_power3
  intro i
  fin_cases i <;> rfl

private def ob49Power11 : QuotientMatrix := quotientDecode #v[479, 1208, 681, 2086, 2655, 846, 570, 2031, 2584, 3272, 3236, 3284]

private theorem ob49_power11 : value (obstruction49 ^ 11) = ob49Power11 := by
  apply power_step _ 5 6 _ _ _ ob49_power5 ob49_power6
  intro i
  fin_cases i <;> rfl

private def ob49Power21 : QuotientMatrix := quotientDecode #v[1, 2, 4, 8, 16, 32, 64, 128, 256, 512, 1024, 2048]

private theorem ob49_power21 : value (obstruction49 ^ 21) = ob49Power21 := by
  apply power_step _ 10 11 _ _ _ ob49_power10 ob49_power11
  intro i
  fin_cases i <;> rfl

private theorem obstruction49_small_power : (obstruction49 ^ 3) ^ 7 = 1 := by
  apply eq_one_of_value
  rw [← pow_mul]
  change value (obstruction49 ^ 21) = 1
  rw [ob49_power21]
  exact decode_identity

private theorem obstruction49_nonidentity : obstruction49 ^ 3 ≠ 1 := by
  apply ne_one_of_value _ _ ob49_power3
  intro h
  have hc := congrArg (fun M : QuotientMatrix => M 0 0) h
  have hn : (quotientDecode #v[2904, 363, 3313, 589, 2025, 1879, 2197, 675, 791, 394, 1661, 3951]) 0 0 ≠ (1 : QuotientMatrix) 0 0 := by decide +kernel
  exact hn hc

theorem alternative49 :
    representative 49 ∈ involutionMatrixLineStabilizer ∨
    representative 49 ∈ involutionMatrixSecondSubgroup ∨
    ∃ x ∈ baseSubgroup ⊔ Subgroup.zpowers (representative 49), x ^ 2304 ≠ 1 := by
  refine Or.inr (Or.inr ⟨obstruction49 ^ 3,
    (baseSubgroup ⊔ Subgroup.zpowers (representative 49)).pow_mem obstruction49_mem 3, ?_⟩)
  exact coprime_power_obstruction _ 7 (by decide +kernel)
    obstruction49_small_power obstruction49_nonidentity


end CFSG.Quasithin.Chapter1.XiEmbedding.InvariantThree.SporadicActions.J4Reduction.FiniteIncidence.ObstructionCertificate
