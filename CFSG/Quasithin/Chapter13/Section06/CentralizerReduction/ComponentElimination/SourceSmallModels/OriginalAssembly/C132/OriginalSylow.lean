module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132.Catalogue
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.OriginalSylowClassification

/-!
# C.1.32 on the actual selected component and centralizer Sylow

The selected pair K,T_v carries its original Sylow witness. The proved
Sylow-pair reconstruction therefore supplies all C.1.32 alternatives on
that actual pair. The native small-block exclusions, prescribed MS
replacement and orthogonal endgame give the literal nonsingular
centralizer bound. No universal classification of nonsylow MS pairs is used.

Original Chapter13 normalization, omega centralizers and path replacement
remain explicit independent source interfaces in these local consumers.
Source: Aschbacher--Smith13.6.22--23 and C.1.32.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
open CFSG.Quasithin.ChapterC
open scoped MatrixGroups
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The actual selected Sylow pair supplies the nonlinear block alternatives. -/
theorem not_nonlinear_plus_original_sylow_source
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
      centralizer ({markedZ d.flag.module} : Set G)) :
    ¬ NonlinearSmallQuotient (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K) := by
  intro hmodel
  obtain ⟨hms,hcentral⟩ := smallMSPair_original_source d V₃ earlier standing hm hfusion
    h1332 h63 hK hL hz hmodel
  have hblocks := blocks_of_rankTwoAlternatives K _ hcentral (hms.rankTwo_of_original_sylow_knownSimple hK.1.2.2.1)
  obtain ⟨hb,hc⟩ := not_binary_or_coveredSix_original_source d V₃ earlier standing hm
    hfusion hform hfailure h1332 h63 hK hL hz hmodel.reduced
  rcases hblocks with h | h | h
  · exact hb (.g2 h)
  · exact hb (.alternating h)
  · exact hc h


/-- The actual reduced catalogue after source-specific Sylow reconstruction. -/
theorem reduced_catalogue_original_sylow_source
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
  have hnonlinear := not_nonlinear_plus_original_sylow_source d V₃ earlier
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

/-- Actual nonsingular centralizer containment using the proved original
Sylow-pair classification, with no universal small-MS premise. -/
theorem centralizer_le_normalizer_of_original_sylow_source
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
  exact reduced_catalogue_original_sylow_source d V₃ earlier
    standing hm hfusion hform hfailure h1332 h63 hK hL hz replacement


end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.C132
