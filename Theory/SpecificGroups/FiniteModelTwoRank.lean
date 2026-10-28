module
public import Theory.GroupTheory.PrimeRankOrderBound
public import Theory.Mathieu.M12.Properties.Order
public import Theory.Mathieu.M23.Properties.Order
public import Theory.SpecificGroups.Janko1.Model.Certification.Order
public import Theory.SpecificGroups.Janko3.Model.Order
public import Theory.SpecificGroups.McLaughlin.Multiplier.ModelComparison.Source
public import Theory.SpecificGroups.PSL5Two.TwoRankUpper
public import Theory.AtlasPort.ExceptionalIsomorphisms.Order20160A8.BinaryMaps

/-!
# Coarse two-ranks of finite simple-group models

Lagrange's theorem bounds the two-ranks of alternating groups of degree at
most nine and the Mathieu, Janko and McLaughlin models whose certified orders
have two-part at most 128. The McLaughlin bound uses the proved equivalence
of the literal permutation carrier with the Leech triangle stabilizer.
Field transport combines the binary degree-four order with the existing
structural degree-five rank bound. No group is recognized from its order.

Source application: Aschbacher--Smith 4.4.12, printed p.622.
-/

public section
namespace Theory.SpecificGroups.FiniteModelTwoRank
open Theory.GroupTheory

/-- Every alternating group of degree at most nine has two-rank at most seven. -/
theorem alternating_le_seven {n : ℕ} (hn : n ≤ 9) :
    primeRank 2 (alternatingGroup (Fin n)) ≤ 7 := by
  apply primeRank_le_of_prime_pow_not_dvd
  intro hd
  have hperm := (alternatingGroup (Fin n)).card_subgroup_dvd_card
  rw [Nat.card_perm, Nat.card_fin] at hperm
  have hh := hd.trans (hperm.trans (Nat.factorial_dvd_factorial hn))
  exact (by norm_num [Nat.factorial] : ¬ 2 ^ (7 + 1) ∣ Nat.factorial 9) hh

/-- The certified M₁₁ order bounds its two-rank by seven. -/
theorem m11_le_seven : primeRank 2 Sporadic.Mathieu.M11 ≤ 7 := by
  apply primeRank_le_of_prime_pow_not_dvd
  rw [Sporadic.Mathieu.m11_order]
  norm_num

/-- The certified M₁₂ order bounds its two-rank by seven. -/
theorem m12_le_seven : primeRank 2 Sporadic.Mathieu.M12 ≤ 7 := by
  apply primeRank_le_of_prime_pow_not_dvd
  rw [Sporadic.Mathieu.m12_order]
  norm_num

/-- The certified M₂₂ order bounds its two-rank by seven. -/
theorem m22_le_seven : primeRank 2 Sporadic.Mathieu.M22 ≤ 7 := by
  apply primeRank_le_of_prime_pow_not_dvd
  rw [Sporadic.Mathieu.m22_order]
  norm_num

/-- The certified M₂₃ order bounds its two-rank by seven. -/
theorem m23_le_seven : primeRank 2 Sporadic.Mathieu.M23 ≤ 7 := by
  apply primeRank_le_of_prime_pow_not_dvd
  rw [Sporadic.Mathieu.m23_order]
  norm_num

/-- The certified J₁ matrix-model order bounds its two-rank by seven. -/
theorem j1_le_seven : primeRank 2 Janko1.Model ≤ 7 := by
  apply primeRank_le_of_prime_pow_not_dvd
  rw [Janko1.card_model]
  norm_num

/-- The certified J₃ order bounds its two-rank by seven. -/
theorem j3_le_seven : primeRank 2 Sporadic.Janko3.Model ≤ 7 := by
  apply primeRank_le_of_prime_pow_not_dvd
  rw [Sporadic.Janko3.model_card]
  norm_num

/-- The literal McL permutation carrier has two-rank at most seven. -/
theorem mcl_le_seven : primeRank 2 Sporadic.LeechRelated.McL.Carrier ≤ 7 := by
  apply primeRank_le_of_prime_pow_not_dvd
  rw [Nat.card_congr McLaughlin.Multiplier.permutationModelEquiv.toEquiv,
    Atlas.Sporadic.McLaughlin.card]
  norm_num [Atlas.Sporadic.McLaughlin.order]

/-- The binary linear groups in degrees four and five have two-rank at most seven. -/
theorem binary_linear_le_seven {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = 2) {n : ℕ} (hn : n = 4 ∨ n = 5) :
    primeRank 2 (Matrix.ProjectiveSpecialLinearGroup (Fin n) F) ≤ 7 := by
  let := Fintype.ofFinite F
  let e : F ≃+* ZMod 2 := (ZMod.ringEquivOfPrime F Nat.prime_two
    (by simpa only [Nat.card_eq_fintype_card] using hF)).symm
  rw [primeRank_equiv 2 (Atlas.fieldEquivPSL n e)]
  rcases hn with rfl | rfl
  · apply primeRank_le_of_prime_pow_not_dvd
    rw [Atlas.Order20160A8.psl4Two_card]
    norm_num
  · exact PSL5Two.primeRank_le_six.trans (by decide)

end Theory.SpecificGroups.FiniteModelTwoRank
