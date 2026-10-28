module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.OriginalExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.PathCentrality.Source44.Replacement.OriginalSource

/-!
# Prescribed replacement in the original 13.6.22 consumer

The original MS93 (4.4.4) theorem supplies prescribed replacement on each
actual characteristic reduction of the minimal equal-star component. Applying
the existing source exclusion removes its last MS replacement premise while
retaining the original earlier local hypotheses and the 13.3.2 and 13.6.3 inputs.

Source: Aschbacher--Smith, The Classification of Quasithin Groups II,
13.6.22, printed pp.932--933; Meierfrankenfeld--Stellmacher (1993),
(4.4.4), printed p.894.
-/

public section
open Subgroup Representation Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
open CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface
open CFSG.Quasithin.Chapter13.Section06.CentralizerReduction
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- Original binary linear-three exclusion with the MS replacement premise discharged. -/
theorem not_plus_linearThree_original_source
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
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G), RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* BinaryLinearThree.Group) := by
  apply not_plus_linearThree_original_source_of_replacement d V₃ earlier standing hm
    hfusion hform hfailure h1332 h63 hK hL hz
  intro K₀ _hle _hY i t common hb a a' p hp
  exact BinaryMS.MS93.DistanceEight.PathCentrality.Source44.Replacement.OriginalSource.prescribedReplacement
    common hb p hp

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
