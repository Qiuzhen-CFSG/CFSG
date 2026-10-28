module

public import CFSG.Quasithin.MainForward.SourceCases
public import CFSG.Quasithin.MainConverse
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.InitialNaturalSourcesAt
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalFiveCompleteInterface
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.InitialFourCompleteInterface
public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalPrimeRemainingSource

/-!
# Main equivalence after the original degree-four and A₅ proofs

The original structural and module sources now construct the initial natural
four-space and the complete alternating-five recognition branch. The Main
consumer no longer assumes either degree-four naturality or the earlier
5.2.3 family. Its remaining structural, module, rank-one, six, HS and original
E source duties retain their actual Sylow guards and full catalogue output.
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

/-- The proper-K Main equivalence after supplying the proved original
initial-four and A₅ branches, retaining the other literal source duties. -/
theorem classification_of_original_prime_completed_branches_at
    (structural : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Structural1222At KnownSimple.IsKnownSimple T)
    (modules : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
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
    (hs : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ (L V : Subgroup G) (_d : Counterexample T L)
        (_h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
        (F : InvariantFlag T V 3), ¬ IsMulCommutative F.U →
        ∀ z : G, F.Vi 1 = zpowers z → HigmanSims.TypeAt z V →
          Nonempty (G ≃* KnownSimple.SporadicName.hs.Carrier))
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
      OriginalQuinticPrimeExclusionAt T Mc)
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
    have five : FiveRecognition G :=
      At.Interface.five_recognition_complete (fun S hmany => modules hG S hmany)
    apply MainForward.forward_of_nonempty_models_and_theoremE hG
    · intro T hmany hne
      exact At.qtkeModel_of_initial_natural_sources hmany
        (structural hG T hmany) (modules hG T hmany)
        (fun L V h D hp => At.Interface.initial_four_natural h D hp
          (structural hG T hmany) (modules hG T hmany) hmany) (exits hG T hmany) (six hG T hmany)
        (hs hG T hmany) five hG hne
    · intro T hmany hempty
      exact source_theoremE_of_original_prime_remaining_sources hG T hmany hempty
        (hrank hG T hmany hempty) (hnormalize hG T hmany hempty)
        (hquintic hG T hmany hempty) (h13 hG T hmany hempty)
  · exact MainConverse.quasithin_and_evenCharacteristic_of_model hna

end CFSG.Quasithin
