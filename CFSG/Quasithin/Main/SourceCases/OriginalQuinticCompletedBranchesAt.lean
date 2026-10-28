module

public import CFSG.Quasithin.Main.SourceCases.OriginalNormalizedCompletedBranchesAt
public import CFSG.Quasithin.Chapter15.SourceAssembly.OriginalQuinticComplete

/-!
# Main equivalence with the original quintic exclusion proved

The actual order-five and order-fifteen source contradictions supply the
original quintic callback internally. All other source duties keep their
exact Sylow guards. The conclusion retains the full QTKE catalogue.
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

/-- The Main equivalence after the complete original quintic exclusion,
with the remaining independent source duties unchanged. -/
theorem classification_of_original_quintic_completed_branches_at
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
  exact classification_of_original_normalized_completed_branches_at structural modules exits
    six hs hna hK hrank
    (fun hG T hmany hempty _ hu => original_quintic_prime_exclusion hG T hmany hempty hu) h13

end CFSG.Quasithin
