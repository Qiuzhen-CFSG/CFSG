module

public import CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.LineNormalizers.Offenders.BestReduction.FullCoreTransfer.Models
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.SpecificGroups.FFLinearPrimeCore
public import Theory.SpecificGroups.Alternating.TwoThreeCycles

/-!
# Excluding every nonsimple product branch at three-rank one

Each factor in B.5.6(3) and (5) contains a cubic, including the exceptional
indecomposable action in (3c) and the possibly nonsplit actions in (5).
The actual internal product isomorphism makes these two contributions to
three-rank independent. In (4), its embedded alternating-six subgroup alone
already has rank two. No splitting of an ambient module is used.

Source: Aschbacher–Smith, combined 1 March 2004 manuscript, B.5.6, printed
p.105, and the rank reduction in the proof of 15.3.67, printed p.1154.
-/

public section
open Subgroup Representation Representation.BinaryOffender Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer.RankOneDispatch
open ChapterB ChapterB.SourceInduction ChapterB.QuasisimpleSource
universe u v
variable {D : Type u} [Group D] [Finite D]
  {W : Type v} [AddCommGroup W] [Module (ZMod 2) W]
  (ρ : Representation (ZMod 2) D W)

private theorem threeRank_pos_of_three_dvd {G : Type*} [Group G] [Finite G]
    (h : 3 ∣ Nat.card G) : 1 ≤ primeRank 3 G := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 3 h
  let : IsElementaryAbelian 3 (zpowers x) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one
      (by simpa only [hx] using pow_orderOf_eq_one x)
  exact IsElementaryAbelian.primeRank_ge_of_card (zpowers x)
    (by rw [Nat.card_zpowers, hx, pow_one])

omit [Finite D] in
private theorem factorNatural_three_dvd (h : FactorNatural ρ) : 3 ∣ Nat.card D := by
  cases h with
  | linearTwo F h =>
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.groupEquiv.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two F.Carrier
  | symmetricFive h =>
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.groupEquiv.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    decide
  | linearThree F _ h =>
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.groupEquiv.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_three F.Carrier

omit [Finite D] in
/-- The exceptional B.5.6(3c) factor has the same actual SL₃(2) actor as
its natural moved submodule; indecomposability does not remove its cubic. -/
theorem sourceFactor_three_dvd {A : Subgroup D} {U : Subrepresentation ρ}
    (h : SourceFactorCase ρ A U) : 3 ∣ Nat.card A := by
  cases h with
  | natural _ h => exact factorNatural_three_dvd _ h
  | doubleNatural F _ _ h =>
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.groupEquiv.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_three F.Carrier
  | exceptional _ h =>
    rw [Nat.card_congr h.natural.groupEquiv.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_three (ZMod 2)

/-- Both original factors contribute rank even when their module sections
are central quotients or exceptional indecomposable extensions. -/
theorem sourceTwoFactor_threeRank (h : SourceTwoFactorCase ρ) :
    2 ≤ primeRank 3 D := by
  have h₁ := threeRank_pos_of_three_dvd (sourceFactor_three_dvd ρ h.firstCase)
  have h₂ := threeRank_pos_of_three_dvd (sourceFactor_three_dvd ρ h.secondCase)
  rw [← primeRank_equiv 3 h.product.equiv, primeRank_prod_eq_add]
  omega

omit [Finite D] in
/-- The actor isomorphism in B.5.6(5a) supplies a cubic even when the
number of natural copies is zero; (5b) retains the same actor on its quotient. -/
theorem hyperplaneSecond_three_dvd {B : Subgroup D} {U : Subrepresentation ρ}
    (h : HyperplaneSecondCase ρ B U) : 3 ∣ Nat.card B := by
  cases h with
  | linearThree _ _ h =>
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.groupEquiv.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_three (ZMod 2)
  | linearTwo F h =>
    obtain ⟨e⟩ := h
    rw [Nat.card_congr e.groupEquiv.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_two F.Carrier

/-- The nonsplit hyperplane clause of B.5.6(5) cannot occur at rank one. -/
theorem hyperplane_threeRank (h : HyperplaneCase ρ) : 2 ≤ primeRank 3 D := by
  have h₁ : 3 ∣ Nat.card h.first := by
    rw [Nat.card_congr h.firstEquiv.toEquiv]
    exact Theory.SpecificGroups.three_dvd_card_sl_three (ZMod 2)
  have h₁ := threeRank_pos_of_three_dvd h₁
  have h₂ := threeRank_pos_of_three_dvd (hyperplaneSecond_three_dvd ρ h.secondCase)
  rw [← primeRank_equiv 3 h.product.equiv, primeRank_prod_eq_add]
  omega

omit ρ in
/-- The adequate outer shape is excluded by its actual A₆ inclusion,
independently of the disputed module splitting in B.5.6(4). -/
theorem outerSixThree_threeRank (h : OuterSixThreeShape D) : 2 ≤ primeRank 3 D := by
  have hA : 2 ≤ primeRank 3 h.first := by
    rw [primeRank_equiv 3 h.firstEquiv]
    exact alternatingGroup.TwoThreeCycles.two_le_primeRank (by decide)
  exact hA.trans (primeRank_le_of_injective 3 h.first.subtype h.first.subtype_injective)

/-- Exhausting the full five-way adequate classification leaves only
B.5.1 or the split two-dimensional S₃ action. -/
theorem quasisimple_or_symmetricThree
    (hr : primeRank 3 D ≤ 1) (h : NontrivialAdequateAlternative ρ) :
    (IsQuasisimple (generalizedFitting D) ∧
      Nonempty (ProjectiveLine.QuasisimpleSourceConclusion ρ (generalizedFitting D))) ∨
      Nonempty (SymmetricThreeCase ρ) := by
  cases h with
  | quasisimple hq ha => exact Or.inl ⟨hq, ⟨ha⟩⟩
  | symmetricThree h => exact Or.inr ⟨h⟩
  | twoFactors h => have := sourceTwoFactor_threeRank ρ h; omega
  | outerSixThree h => have := outerSixThree_threeRank h; omega
  | hyperplane h => have := hyperplane_threeRank ρ h; omega

end CFSG.Quasithin.Chapter15.Section03.AbelianAmalgam.Offenders.BestReduction.FullCoreTransfer.RankOneDispatch
