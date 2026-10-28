module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.G2Selection.Action

/-!
# The original binary G₂ moved-quotient action in 13.6.22

The intrinsic K/O₂(K) marking transfers SQTK from the original involution
centralizer. The earlier source statements supply the Sylow, invariance,
containment and characteristic-two inputs. B.5.1 therefore identifies the
actual U_K/C_(U_K)(K) with the natural derived binary G₂ module, retaining
the full original plus actor and its faithful quotient action.

No short-block or reconstruction assumption occurs. The remaining equality
[O₂(K),K]=U_K belongs to the separate block-reconstruction argument.
Source: Aschbacher–Smith, 13.6.22, printed pp.932–933.
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

/-- B.5.1 identifies the literal full moved quotient from the original flag.
The natural action and elementary-module instance are returned together. -/
theorem g2_actionData_original_source
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
      (markedV d.flag.module) hL hz K ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    ∃ hW : IsElementaryAbelian 2
      (WK K L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module)),
      let := hW
      Nonempty (G2Selection.Action.Data
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
    hfusion h1332 h63 hK hL hz (.g2 ⟨eC⟩)).1
  obtain ⟨eK, _, _⟩ := g2_intrinsic_marking_original_source d V₃ earlier standing
    hfusion hK hL hz eC
  have hlocal := standing.qtke.involution_centralizer_sqtk (marked_orders d.flag.module).2
  have hsqK : IsSQTK KnownSimple.IsKnownSimple K :=
    (IsSQTK.equiv (subgroupOfEquivOfLe hK.1.1)).mp (hlocal.subgroup _)
  have hsqQ : IsSQTK KnownSimple.IsKnownSimple (K ⧸ pCore 2 K) := by
    refine ⟨?_, hsqK.isKGroup.quotient _⟩
    intro p hp ho
    let : Fact p.Prime := ⟨hp⟩
    exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
      (hsqK.stronglyQuasithin p hp ho)
  let hW := wk_elementary K L (T : Subgroup G) (markedZ d.flag.module)
    (markedV d.flag.module) hK.1.1 hSylow (markedZ_mem_Tv_omega d) hchar
  refine ⟨hW, ?_⟩
  exact G2Selection.Action.source_data K L (T : Subgroup G)
    (markedZ d.flag.module) (markedV d.flag.module) hL hz hK hn hLK hSylow
    (markedZ_mem_Tv_omega d) hchar
    ((IsSQTK.equiv (eK.trans eC.symm)).mp hsqQ) eC

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly
