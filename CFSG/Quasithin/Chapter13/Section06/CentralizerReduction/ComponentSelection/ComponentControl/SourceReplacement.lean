module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.TwoCore
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.ComponentControl.SourceStrictness
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.RankTwo.LocalApplication.SourceInputs
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.LocalSetup
public import CFSG.Quasithin.Chapter14.Section03.Prelim.FaithfulSource
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Generation
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.ModelInputs.TheoremC
public import CFSG.Quasithin.ChapterA.Section02.SourceAssembly.Complete
/-!
# Replacement hypotheses and all three assertions of 13.6.16

Reselecting a faithful component preserves every original exclusion and the
uniform A5 choice. Apply the earlier omega-center centralizer theorem to that
literal replacement, and use its source normalization to obtain C_T(K)=1.
The proved A/C component generation and adequate B.5 classification then
supply all three conclusions of 13.6.16. Only the genuine universal 13.3.2
normalization and 13.6.3 centralizer theorems remain as earlier-source inputs.
Source: Aschbacher--Smith 13.3.1--2 and 13.6.3,16, printed pp.884,926,930.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
open ComponentElimination.SourceContainment.RankTwo.LocalApplication
open ComponentElimination.SourceTransferFields.HigherFieldParabolics
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The full original standing hypothesis survives selection of any faithful member. -/
theorem replacement_sourceHypothesis {T : Sylow 2 G} {L : Subgroup G}
    (standing : SourceHypothesis T L) (K : Subgroup G)
    (hK : K ∈ MainForward.faithfulLocalComponents T) : SourceHypothesis T K where
  qtke := standing.qtke
  local_component := hK
  no_larger_field := standing.no_larger_field
  no_linear := standing.no_linear
  no_alternating_nine := standing.no_alternating_nine
  no_sporadic := standing.no_sporadic
  five_minimal := fun _ => standing.five_minimal standing.a5
  a5 := standing.five_minimal standing.a5 K hK
  counterexample := standing.counterexample

theorem sourceHypothesis_hypothesis1331 {T : Sylow 2 G} {L : Subgroup G}
    (standing : SourceHypothesis T L) :
    Chapter14.Section03.FaithfulSource.Hypothesis1331 T L where
  qtke := standing.qtke
  local_component := standing.local_component
  no_larger_field := by rintro ⟨f,hf,h⟩; exact standing.no_larger_field f hf h
  no_linear := standing.no_linear
  no_alternating_nine := standing.no_alternating_nine
  no_sporadic := standing.no_sporadic
  five_minimal := standing.five_minimal

/-- All assertions of 13.6.16, retaining the genuine universal earlier 13.3.2 and 13.6.3. -/
theorem component_control_of_replacement_source
    (T : Sylow 2 G) (L : Subgroup G) (standing : SourceHypothesis T L)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
      (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (z v : G) (hz : z ∈ omegaOneCenterAmbient (T : Subgroup G))
    (hvT : v ∈ T) (hv : v ≠ 1) (hv2 : v ^ 2 = 1)
    (hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) v) (Gv v))
    (hidx : (Tv (T : Subgroup G) v).relIndex (T : Subgroup G) = 2)
    (hchar : generalizedFitting (Gv v) = pCore 2 (Gv v))
    (K : Subgroup G) (hK : K ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v))
    (hS : Tv (T : Subgroup G) v ≤ normalizer (K : Set G))
    (hm : ¬ K ≤ centralizer ({z} : Set G)) :
    (K ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥ ∧
    CharacteristicNormalizerObstruction (Tv (T : Subgroup G) v) K ∧
      K = ⁅K, elementaryAbelianMaxJ (Tv (T : Subgroup G) v)⁆ := by
  have hnorm : ∀ I ∈ MainForward.faithfulLocalComponents T,
      (T : Subgroup G) ≤ normalizer (I : Set G) := by
    intro I hI
    exact h1332 T I (sourceHypothesis_hypothesis1331 (replacement_sourceHypothesis standing I hI))
  have hcore : ∀ I ∈ Chapter1.LIn (Gv v) (Tv (T : Subgroup G) v),
      Tv (T : Subgroup G) v ≤ normalizer (I : Set G) →
      ¬ I ≤ centralizer ({z} : Set G) → (I ⊔ (T : Subgroup G)).pCoreIn 2 = ⊥ := by
    apply twoCore_eq_bot_of_earlier_source standing.qtke
      (fun X _ _ hX hO => ChapterA.Section03.SourceComponents.generation
        (fun Y _ _ => ChapterA.Section02.theoremA_knownSimple (G := Y))
        (ChapterA.Section03.SourceComponents.source_model_inputs_of_theoremC
          (fun Y _ _ => ChapterA.Section02.theoremC_knownSimple (G := Y))) hX hO)
      T L standing.local_component standing.a5 standing.five_minimal hnorm _ z v hz hvT hv hSylow hidx
    intro I hI _ _
    exact centralizer_T_eq_bot_of_omega (T : Subgroup G) I T.isPGroup' (hnorm I hI)
      (h63 T I (replacement_sourceHypothesis standing I hI))
  exact ⟨hcore K hK hS hm,characteristic_normalizer_and_thompson_source standing.qtke
    T z v hz hvT hv hv2 hSylow hidx hchar hcore K hK hS hm⟩
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection
