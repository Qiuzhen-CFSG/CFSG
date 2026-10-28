module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132.Selection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SevenExclusion
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.OriginalExclusion
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceCatalogue.ReducedSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceOrthogonal.OriginalContradiction

/-!
# The reduced original catalogue from C.1.32 and prescribed MS replacement

The nonlinear C.1.32 selection removes A₆, G₂(2)′ and covered A₆.
The existing original A₇ selection and binary linear-three proof remove
the other small rows. Thus the literal K⁺ quotient is SL₄(2) or SL₅(2).
Applying the original orthogonal endgame proves the required nonsingular
centralizer containment on the same flag and quotient maps.

Only the genuine small C.1.32 implication and prescribed MS93 path
replacement remain, produced respectively by `qt-e-ms-small-ranktwo`
and `qt-ms93-distance-eight-earlier`. Full C.1.34 exhaustiveness is not
an input to this application. Source: Aschbacher--Smith 13.6.22--23,
printed pp.932--933, and MS93 (4.4.4).
-/

@[expose] public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.ChapterC
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]

/-- The precise earlier MS path input, only at original selected components
and their literal joins with Tᵥ. The minimum with the same star image is
again selected, so it is covered by this same input. -/
def SourcePathReplacement (L T : Subgroup G) (z v : G) : Prop :=
  ∀ K : Subgroup G, K ∈ Yz L T z v →
    ∀ (i : BinaryMS.Input KnownSimple.IsKnownSimple
      (K.subgroupOf (K ⊔ Tv T v)) ((Tv T v).subgroupOf (K ⊔ Tv T v)))
      (t : BinaryMS.MS93.InputSetup i),
      BinaryMS.MS93.CommonFacts t.reduction.radical t.source t.geometry →
      4 < t.geometry.b t.reduction.radical → ∀ {a a'}
      (p : BinaryMS.MS93.DistanceEight.PathCentrality.CriticalPath
        t.reduction.radical t.geometry a a'),
      BinaryMS.MS93.DistanceEight.PathCentrality.HasTurnConjugators _ p →
      BinaryMS.MS93.DistanceEight.PathCentrality.PrescribedReplacement _ p

variable {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The actual reduced quotient catalogue, with all five original small
rows eliminated and no independent quotient-exclusion callback. -/
theorem reduced_catalogue_original_source_of_rankTwo_and_replacement
    (rankTwo : ∀ (J : Type u) [Group J] [Finite J] (B R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple B R → RankTwoAlternatives B R)
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (hfailure : ¬ Gv (markedV d.flag.module) ≤ normalizer (V : Set G))
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      RankTwo.LocalApplication.SourceHypothesis S I →
        omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (replacement : SourcePathReplacement L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module)) :
    Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* SL(4,ZMod 2)) ∨
    Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* SL(5,ZMod 2)) := by
  have hnonlinear := not_nonlinear_plus_original_source_of_rankTwo rankTwo d V₃ earlier
    standing hm hfusion hform hfailure h1332 h63 hK hL hz
  have h3 := LinearThreeBranch.not_plus_linearThree_original_source_of_replacement
    d V₃ earlier standing hm hfusion hform hfailure h1332 h63 hK hL hz
      (fun K₀ _ hY => replacement K₀ hY)
  have h7 := not_alternating_plus_original_source d V₃ earlier standing hm
    hfusion hform hfailure h1332 h63 hK hL hz
  have hmodel := SourceCatalogue.reduced_model_original_source d V₃ earlier standing hm
    hfusion hform hfailure h1332 h63 K hK hL hz
  cases hmodel with
  | linear n hn e =>
    have he := e.map fun e => e.trans (BinaryLinear.OuterCyclic.projectiveEquivSL (by omega))
    have hn' : n = 3 ∨ n = 4 ∨ n = 5 := by omega
    rcases hn' with rfl | rfl | rfl
    · exact (h3 he).elim
    · exact Or.inl he
    · exact Or.inr he
  | symplectic e => exact (hnonlinear (Or.inl e)).elim
  | g2 e => exact (hnonlinear (Or.inr (Or.inl e))).elim
  | ahat6 e => exact (hnonlinear (Or.inr (Or.inr e))).elim
  | a7 e => exact (h7 e).elim

/-- Actual nonsingular-centralizer containment from the two remaining
independent source inputs. The source assembly must discharge both inputs. -/
theorem centralizer_le_normalizer_of_rankTwo_and_replacement
    (rankTwo : ∀ (J : Type u) [Group J] [Finite J] (B R : Subgroup J),
      SmallMSPair KnownSimple.IsKnownSimple B R → RankTwoAlternatives B R)
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (hform : FusionPreservesForm d.flag.module)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      RankTwo.LocalApplication.SourceHypothesis S I →
        omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (replacement : SourcePathReplacement L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module)) :
    Gv (markedV d.flag.module) ≤ normalizer (V : Set G) := by
  by_contra hfailure
  apply hfailure
  apply SourceOrthogonal.centralizer_le_normalizer_of_original_reduced_models
    d V₃ earlier standing hm hfusion hform h1332 h63 hL hz
  intro K hK
  exact reduced_catalogue_original_source_of_rankTwo_and_replacement rankTwo d V₃ earlier
    standing hm hfusion hform hfailure h1332 h63 hK hL hz replacement

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132
