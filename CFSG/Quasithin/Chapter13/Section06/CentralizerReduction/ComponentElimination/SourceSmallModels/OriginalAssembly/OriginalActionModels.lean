module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SourcePreparation
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.AlternatingModels

/-!
# The A₇ action models from the original flag

The original flag and earlier local statements construct the centralizer
Sylow subgroup, characteristic-two identity, component invariance and
Lᵥ containment. The marked seed lies in the Sylow omega-center, and the
standing QTKE hypothesis supplies the complete local K-group condition.
These discharge every local hypothesis of the B.5 action classification
on the original W_K and its literal plus quotient.

The conclusion retains the elementary-module instance alongside the full
moved action data. No block, shortness, form-preservation or normalizer
failure hypothesis is required. The constructed chart feeds the C.1.24
selection step in Aschbacher–Smith 13.6.22, printed p.932.
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

theorem alternating_actionData_original_source
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
      (markedV d.flag.module) hL hz K ≃* alternatingGroup (Fin 7)) :
    ∃ hW : IsElementaryAbelian 2
      (WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)),
      let := hW
      Nonempty (AlternatingModels.ActionData
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
    hfusion h1332 h63 hK hL hz (.a7 ⟨eC⟩)).1
  let hW := wk_elementary K L (T : Subgroup G) (markedZ d.flag.module)
    (markedV d.flag.module) hK.1.1 hSylow (markedZ_mem_Tv_omega d) hchar
  refine ⟨hW, ?_⟩
  exact AlternatingModels.source_actionData K L (T : Subgroup G)
    (markedZ d.flag.module) (markedV d.flag.module) hL hz hK hn hLK hSylow
    (markedZ_mem_Tv_omega d) hchar
    (standing.qtke.involution_centralizer_sqtk (marked_orders d.flag.module).2).isKGroup eC
end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
