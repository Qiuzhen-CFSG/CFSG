module

public import CFSG.Quasithin.MainForward.SourceCases
public import CFSG.Quasithin.MainConverse
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.InitialNaturalSourcesAt
public import CFSG.Quasithin.Chapter14.Section08.SourceCases.OriginalFiveInterface
public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalPrimeRemainingSource

/-!
# Main equivalence with the residual-order-fifteen branch excluded

The larger-linear terminal follows from the original degree-four marking
and the same guarded structural and module sources. The original quintic
residual of order fifteen is now excluded; the remaining normalization and
later-exclusion duties both concern literal residual order five. All other
original D/E source duties, proper-K/nonabelian guards, and the full-catalogue
converse are retained.
-/

public section
namespace CFSG.Quasithin
open Subgroup Theory.GroupTheory ClassificationModels
open Chapter12.Section02 Chapter12.Section08 Chapter14.Section08.SourceCases
open Chapter12.Section04.SLThreeCommutatorSource.ConjugateExistence
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
open Chapter14.Section03.FaithfulSource
open ChapterA.Section05To06 Chapter15 Chapter15.Section01 Chapter15.Section03
universe u
variable {G : Type u} [Group G] [Finite G] [IsSimpleGroup G]

/-- The proper-K Main equivalence retaining initial degree-four naturality
and only residual-order-five quintic duties among the remaining sources. -/
theorem classification_of_initial_natural_prime_sources_at
    (structural : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Structural1222At KnownSimple.IsKnownSimple T)
    (modules : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (four : IsSimpleQTKE KnownSimple.IsKnownSimple G → ∀ T : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard →
      ∀ L V : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T L →
      (D : ChosenModule T L V) → ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 4 2 →
      Chapter12.Section09.NaturalModule D 4)
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
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
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
      At.Interface.five_recognition (fun S hmany => modules hG S hmany) h523
    apply MainForward.forward_of_nonempty_models_and_theoremE hG
    · intro T hmany hne
      exact At.qtkeModel_of_initial_natural_sources hmany
        (structural hG T hmany) (modules hG T hmany)
        (four hG T hmany) (exits hG T hmany) (six hG T hmany)
        (hs hG T hmany) five hG hne
    · intro T hmany hempty
      exact source_theoremE_of_original_prime_remaining_sources hG T hmany hempty
        (hrank hG T hmany hempty) (hnormalize hG T hmany hempty)
        (hquintic hG T hmany hempty) (h13 hG T hmany hempty)
  · exact MainConverse.quasithin_and_evenCharacteristic_of_model hna

end CFSG.Quasithin
