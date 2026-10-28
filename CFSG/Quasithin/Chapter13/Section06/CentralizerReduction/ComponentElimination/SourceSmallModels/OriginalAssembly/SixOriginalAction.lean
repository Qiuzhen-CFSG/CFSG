module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SourcePreparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SixMoved
public import Theory.SpecificGroups.SymplecticFour.Sylow.DerivedNormalizerSolvable.Binary
/-!
# Original-flag A₆ module preparation

The literal source flag supplies every local input to B.5 on W_K.
The A₆ quotient therefore gives its actual natural moved quotient, and
U_K has order sixteen or thirty-two. No block, shortness, splitting or
classification premise is assumed. This prepares the genuine remaining
whole-core selection in Aschbacher--Smith 13.6.22, printed p.932.
-/
public section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
open LinearThree.CentralAction.ModuleAlternatives
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

theorem six_actionData_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
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
    (eC : plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* alternatingGroup (Fin 6)) :
    ∃ hW : IsElementaryAbelian 2
      (WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)),
      let := hW
      Nonempty (SixModels.ActionData
        (wkRepresentation K L (T : Subgroup G) (markedZ d.flag.module)
          (markedV d.flag.module) hL hz)
        (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
          (markedV d.flag.module) hL hz K)) := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hSylow : Chapter1.IsSylowIn 2 (Tv (T : Subgroup G) (markedV d.flag.module))
      (Gv (markedV d.flag.module)) := ⟨c.reductions.centralizerSylow, c.reductions.sylow_image⟩
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz (.symplectic ⟨eC.trans (Theory.SpecificGroups.SymplecticFour.Binary.derivedEquivAlternatingSix (F := ZMod 2) (by simp)).symm⟩)).1
  let hW := wk_elementary K L (T : Subgroup G) (markedZ d.flag.module)
    (markedV d.flag.module) hK.1.1 hSylow (markedZ_mem_Tv_omega d) hchar
  refine ⟨hW, ?_⟩
  exact SixModels.source_actionData K L (T : Subgroup G)
    (markedZ d.flag.module) (markedV d.flag.module) hL hz hK hn hLK hSylow
    (markedZ_mem_Tv_omega d) hchar
    (standing.qtke.involution_centralizer_sqtk (marked_orders d.flag.module).2).isKGroup eC
theorem six_moved_card_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
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
    (eC : plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* alternatingGroup (Fin 6)) :
    Nat.card (UK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)) = 16 ∨
    Nat.card (UK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)) = 32 := by
  obtain ⟨hW,hmoved⟩ := six_actionData_original_source d V₃ earlier standing hm hfusion
    h1332 h63 hK hL hz eC
  let := hW
  obtain ⟨m⟩ := hmoved
  obtain ⟨e⟩ := m.natural
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  let := plusImage_K_normal K L (T : Subgroup G) (markedZ d.flag.module)
    (markedV d.flag.module) hL hz hK hn
  exact six_moved_card K L (T : Subgroup G) _ _ hL hz m.component_le_offenders
    m.conclusion.sectionData m.irrPlus e

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
