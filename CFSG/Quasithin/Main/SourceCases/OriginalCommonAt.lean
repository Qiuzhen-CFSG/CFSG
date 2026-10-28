module

public import CFSG.Quasithin.MainForward.SourceCases
public import CFSG.Quasithin.MainConverse
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalSourcesAt
public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalQuinticPrimeSource

/-!
# Main equivalence from the common original source duties

The D dispatcher constructs its case-one, catalogue, unitary, six-row,
Rudvalis and G2 consequences from the same original Chapter12 sources.
The remaining HS recognition keeps the original flag, point and seed.
The E branch supplies all extraspecial normalization and the quintic
residual-order-fifteen normalization. All genuine remaining duties are
explicit, with no universal MS-classification assumption.
-/

public section
namespace CFSG.Quasithin
open Subgroup Theory.GroupTheory ClassificationModels
open Chapter12.Section02 Chapter12.Section08 Chapter14.Section08.SourceCases
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter14.Section03.FaithfulSource
open ChapterA.Section05To06 Chapter15 Chapter15.Section01 Chapter15.Section03
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- The proper-K Main equivalence retaining only the common original
source duties and the marked HS, A5 and remaining E endpoints. -/
theorem classification_of_common_original_sources_at
    (structural : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Structural1222At KnownSimple.IsKnownSimple T)
    (modules : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (larger : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      ∀ n : ℕ, n = 4 ∨ n = 5 → ¬ ClassicalGroup.IsPSL (Chapter1.XiQuotient I) n 2)
    (exits : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ K H : Subgroup G,
      H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (K : Set G)) →
      Hypothesis1223 KnownSimple.IsKnownSimple T (localResidual H) →
      Nonempty ((localResidual H ⧸ pCore 2 (localResidual H)) ≃*
        alternatingGroup (Fin 5)) →
      RankOneModule.GenericExit T (localResidual H) ∧
        RankOneModule.SmallExit T (localResidual H))
    (six : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard → Theorem1381At T)
    (earlier : Chapter14.Section07.LocalStructure.CriticalFusion.Source.ResidualNormalizer.LocalControl.Earlier14710.{u})
    (hs : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (L V : Subgroup G) (_d : Counterexample T L)
        (_h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
        (F : InvariantFlag T V 3), ¬ IsMulCommutative F.U →
        ∀ z : G, F.Vi 1 = zpowers z → HigmanSims.TypeAt z V →
          Nonempty (G ≃* KnownSimple.SporadicName.hs.Carrier))
    (five : FiveRecognition G)
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
      OriginalQuinticPrimeFullNormalizationAt T Mc)
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
  · rintro ⟨hQT,hEC⟩
    have hG : IsSimpleQTKE KnownSimple.IsKnownSimple G :=
      ⟨⟨hQT,hK,hEC⟩,inferInstance,hna⟩
    apply MainForward.forward_of_nonempty_models_and_theoremE hG
    · intro T hmany hne
      exact At.qtkeModel_of_original_sources hmany
        (structural hG T hmany) (modules hG T hmany)
        (larger hG T hmany) (exits hG T hmany) (six hG T hmany)
        earlier (hs hG T hmany) five hG hne
    · intro T hmany hempty
      exact source_theoremE_of_original_quintic_prime_sources hG T hmany hempty
        (hrank hG T hmany hempty) (hnormalize hG T hmany hempty)
        (hquintic hG T hmany hempty) (h13 hG T hmany hempty)
  · exact MainConverse.quasithin_and_evenCharacteristic_of_model hna

end CFSG.Quasithin
