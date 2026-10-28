module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentSelection.MinimalIntrinsic
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeOriginal.IntrinsicSource

/-!
# The original binary linear-three replacement and its MS pair

The selected minimum with the original star image has quasisimple intrinsic
two-core quotient by the radical-Sylow argument. Instantiate the complete
known-simple A.3.6 theorem, identify its intrinsic quotient with L₃(2), and
apply the original MS-pair construction. The replacement retains W_K and
contains the original Lᵥ. No quasisimplicity or classification callback remains.

The remaining nonshort module classification and its final fourth-case
exclusion belong to their independent source producers.

Source: Aschbacher--Smith 13.6.22, printed pp.932--933, first paragraph.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
open ComponentSelection A5Module ComponentReduction InitialSieve
open SourceTransferFields.HigherFieldParabolics.LinearThree
open SourceTransferFields.HigherFieldParabolics.LinearThree.LocalStructure
universe u
variable {G : Type u} [Group G] [Finite G]
variable {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The original minimal replacement has the intrinsic L₃(2) model and actual
MS pair. Quasisimplicity and every component-classification premise are discharged. -/
theorem exists_intrinsic_model_and_msPair_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : SourceContainment.RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
    (h1332 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      Chapter14.Section03.FaithfulSource.Hypothesis1331 S I →
        (S : Subgroup G) ≤ normalizer (I : Set G))
    (h63 : ∀ (S : Sylow 2 G) (I : Subgroup G),
      SourceContainment.RankTwo.LocalApplication.SourceHypothesis S I →
      omegaOneCenterAmbient (S : Subgroup G) ⊓ centralizer (I : Set G) = ⊥)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G))
    (e : plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* BinaryLinearThree.Group)
 :
    ∃ K₀ : Subgroup G, K₀ ≤ K ∧
      K₀ ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ∧
      WK K₀ L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) =
        WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ∧
      Lv L (markedV d.flag.module) ≤ K₀ ∧
      Nonempty ((K₀ ⧸ pCore 2 K₀) ≃* BinaryLinearThree.Group) ∧
      CFSG.Quasithin.Chapter1.RadicalExclusions.ModelReduction.FullSieve.SourceInterface.LinearThreeMSPair
        KnownSimple.IsKnownSimple K₀ (Tv (T : Subgroup G) (markedV d.flag.module)) 1 (ZMod 2) ∧
      MSSourceModels.NonabelianCenters.CaseFourQuotient.FrattiniCentralizer.Nonabelian.Realization.JoinProduct
        K₀ (Tv (T : Subgroup G) (markedV d.flag.module)) := by
  obtain ⟨K₀,hle,hmin,hY,hn,hW,hLV,⟨e₀⟩⟩ :=
    exists_minimal_equalStar_original_source d V₃ earlier standing hm hfusion h1332 h63 hK hL hz e
  have hmin₀ : Minimal (fun D => D ∈ Chapter1.LIn
      (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module))
      (Tv (T : Subgroup G) (markedV d.flag.module)) ∧
      starImage (markedZ d.flag.module) (markedV d.flag.module) D =
        starImage (markedZ d.flag.module) (markedV d.flag.module) K₀) K₀ := by
    simpa only [hmin.1.2] using hmin
  let := intrinsic_quasisimple_of_minimal_equalStar standing.qtke
    (ChapterA.SQTKStructure.a36Input_of_theoremsAC
      (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
      (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple))
    K₀ (K ⊔ Tv (T : Subgroup G) (markedV d.flag.module)) L (T : Subgroup G)
    (markedZ d.flag.module) (markedV d.flag.module) (marked_orders d.flag.module).2 hY hn hmin₀
  exact ⟨K₀,hle,hY,hW,hLV,
    intrinsic_model_and_msPair_of_quasisimple_original_source d V₃ earlier standing hm hfusion
      h1332 h63 hY hL hz e₀⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.LinearThreeBranch
