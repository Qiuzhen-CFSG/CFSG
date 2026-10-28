module
public import CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape.OddCommutator.Source
public import Theory.GroupTheory.PrimeRankResidualCentralizer
public import Theory.Quasithin.PositiveLocalRank
public import Theory.SpecificGroups.ProjectiveLinearThree
public import GorensteinWalter.PSL2Center

/-!
# The three-rank bound for the escaping witness

The canonical supplement is normal in its join with Y. Its quotient is
the actual PSL₂(p), whose center is trivial and whose order is divisible
by three. Commutation modulo the intrinsic two-core therefore adds its
positive three-rank to that of Y. The SQTK bound makes m₃(Y) at most one.
Source: Aschbacher--Smith 13.1.9, first paragraph of printed p.870.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
open Chapter1 Chapter12.Section02 ResidualCentralizerRank
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G}

private theorem psl2_center {A : Type*} [Group A] {p : ℕ}
    (hmodel : ClassicalGroup.IsPSL A 2 p) : center A = ⊥ := by
  obtain ⟨F,hF,hfin,_,⟨e⟩⟩ := hmodel
  let := hF
  let := hfin
  apply le_bot_iff.mp
  intro a ha
  have hz : e a ∈ center (GorensteinWalter.PSL2 F) :=
    (Subgroup.centerCongr e ⟨a,ha⟩).property
  rw [GorensteinWalter.psl2_center_eq_bot F] at hz
  exact mem_bot.mpr (e.injective ((mem_bot.mp hz).trans (map_one e).symm))

private theorem psl2_three_rank {A : Type*} [Group A] [Finite A] {p : ℕ}
    (hmodel : ClassicalGroup.IsPSL A 2 p) : 1 ≤ primeRank 3 A := by
  obtain ⟨F,hF,hfin,_,⟨e⟩⟩ := hmodel
  let := hF
  let := hfin
  apply Theory.Quasithin.one_le_primeRank_of_dvd_card
  rw [Nat.card_congr e.toEquiv]
  exact Matrix.ProjectiveSpecialLinearGroup.three_dvd_card F 2 le_rfl

/-- The literal commuting PSL₂ factor forces the source three-rank bound. -/
theorem threeRank_le_one_of_canonical_commutator
    (h : Hypothesis1311 T) {L H Y : Subgroup G}
    (hH : IsMaximalTwoLocal H) (hAH : canonicalSupplement T L ≤ H) (hYH : Y ≤ H)
    (hYA : Y ≤ normalizer (canonicalSupplement T L : Set G))
    (hc : ⁅Y,canonicalSupplement T L⁆ ≤ Y.pCoreIn 2)
    {p : ℕ} (hmodel : ClassicalGroup.IsPSL (XiQuotient (canonicalSupplement T L)) 2 p) :
    primeRank 3 Y ≤ 1 := by
  let A := canonicalSupplement (T : Subgroup G) L
  let J := Y ⊔ A
  have hcA : ⁅Y,A⁆ ≤ A.pCoreIn 2 :=
    le_pCoreIn_of_normalizes ((isPGroup_pCoreIn 2 Y).to_le hc)
      (le_normalizer_iff_commutator_le_right.mp hYA) (normalizer_commutator_ge_right _ _)
  have hz : Nat.Coprime 3 (Nat.card (center (XiQuotient A))) := by
    rw [psl2_center hmodel,Nat.card_unique]
    exact Nat.coprime_one_right 3
  have hr := primeRank_sum_le_of_normalized_factor (by decide : Odd 3) Y A hYA
    ((commutator_mono (map_subtype_le _) le_rfl).trans hcA) hz
  have hbound : primeRank 3 J ≤ 2 := by
    have hJH : J ≤ H := sup_le hYH hAH
    have hh := (h.simpleQTKE.twoLocal_sqtk hH.1).stronglyQuasithin 3 Nat.prime_three (by decide)
    exact (primeRank_mono 3 hJH).trans hh
  have hpos : 1 ≤ primeRank 3 A := by
    have hh := psl2_three_rank hmodel
    rwa [primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 A) pCore_isPGroup] at hh
  change primeRank 3 (Y ⊔ A : Subgroup G) ≤ 2 at hbound
  omega

end CFSG.Quasithin.Chapter13.Section01.SourceNonquasisimple.Supplements.Escape
