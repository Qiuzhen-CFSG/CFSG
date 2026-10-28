module

public import CFSG.Quasithin.MainForward.SourceCases.At
public import CFSG.Quasithin.MainConverse
public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalPrimeResidualSource

/-!
# Main equivalence from the remaining original local sources

The E branch uses the original ambient source proofs, including natural
reconstruction, the Nine and cubic exclusions, later extraspecial exclusion,
and normalization for a marked quintic residual of order fifteen. The
remaining inputs refer to the same original group and Sylow subgroup.
The earlier D source branches and remaining E duties are still explicit.
-/

public section
namespace CFSG.Quasithin
open Subgroup Theory.GroupTheory ClassificationModels
open Chapter12.Section02 Chapter14.Section08.SourceCases
open ChapterA.Section05To06 Chapter15 Chapter15.Section01 Chapter15.Section03
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- The proper-K classification equivalence with the currently remaining
original D and E source duties. -/
theorem classification_of_original_local_sources_at
    (structural : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Structural1222At KnownSimple.IsKnownSimple T)
    (caseOne : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard → Earlier1332CaseOneAt T)
    (catalogue : Catalogue G) (unitary : UnitaryExclusion G)
    (six : SixRecognition G) (nonabelian : NonabelianRecognition G)
    (abelian : AbelianRecognition G) (five : FiveRecognition G)
    (hna : ¬ IsMulCommutative G)
    (hK : HasProperKSubgroups KnownSimple.IsKnownSimple G)
    (hrank : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ → ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      RankTwoResolver T Mc)
    (hnormalize : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ → ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalPrimeResidualFullNormalizationAt T Mc)
    (hquintic : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ → ∀ Mc : Subgroup G,
      maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc} →
      OriginalQuinticExclusionAt T Mc)
    (h13 : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      MainForward.faithfulLocalComponents T = ∅ →
      ∀ d : CharacteristicTwo.LocalData G, d.T = T →
      IsOrderingMaximal d.T d.M →
      maximalTwoLocalOvergroups (centralizer (d.Z : Set G)) = {d.Mc} →
      ∀ Yplus : Subgroup G, Hypothesis15310 d.M d.Y d.S d.V₁ Yplus →
      primeRank 3 Yplus = 2 →
      ∀ I ∈ outsideFamily Yplus d.S d.M, generalizedFitting I ≠ pCore 2 I) :
    (IsQuasithin G ∧ IsEvenCharacteristic G) ↔ IsQTKEModel G := by
  constructor
  · rintro ⟨hQT, hEC⟩
    have hG : IsSimpleQTKE KnownSimple.IsKnownSimple G :=
      ⟨⟨hQT, hK, hEC⟩, inferInstance, hna⟩
    apply MainForward.forward_of_local_source_branches_at (structural hG) (caseOne hG)
      catalogue unitary six nonabelian abelian five hG
    intro T hmany hempty
    exact source_theoremE_of_original_prime_residual_sources hG T hmany hempty
      (hrank hG T hmany hempty) (hnormalize hG T hmany hempty)
      (hquintic hG T hmany hempty) (h13 hG T hmany hempty)
  · exact MainConverse.quasithin_and_evenCharacteristic_of_model hna

end CFSG.Quasithin
