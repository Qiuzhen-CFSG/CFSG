module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.SixSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.SixMarked
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.Endgame

/-!
# Original ordinary-A₇ exclusion in 13.6.22

The source module identity, local residual quotient and Baumann-normalizer
placement construct the actual six-point replacement in Y_z. Retaining the
natural-module comparison in its chosen coordinates shows that Lᵥ and this
replacement have the same fixed subgroup on W_K: two explicit cubic actors
connect its six moved letters. Its two-core commutator lies in the original
elementary module, so checked Sylow averaging centralizes the same earlier
marked a. Original 13.6.17 gives the contradiction.

Every replacement, module, fixed-space, Sylow and action input is constructed.
No additional block classification of the replacement is needed. The genuine
earlier flag/local, fusion/form, failed-normalization, reduced-catalogue and
universal 13.3.2/13.6.3 inputs are retained with the original maps.

Source: Aschbacher–Smith, 13.6.17 and the ordinary A₇ paragraph and endgame
of 13.6.22, printed pp.930–933.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
open ComponentSelection A5Module SourceContainment ComponentReduction InitialSieve
open OrdinarySevenOriginal AlternatingBranches.OrdinarySeven
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The original ordinary A₇ configuration produces a selected replacement
which centralizes the same marked a. No extra action premise remains. -/
theorem ordinarySeven_replacement_centralizes_markedA_of_localConfiguration
    (d : FlagSource T L V V₁ V₂)
    (c : LocalConfiguration (normalizer (L : Set G)) d.flag)
    (hblock : IsAlternatingBlock K 7)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hL : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      normalizer (Lv L (markedV d.flag.module) : Set G))
    (hz : Tv (T : Subgroup G) (markedV d.flag.module) ≤
      centralizer ({markedZ d.flag.module} : Set G)) :
    ∃ B : Subgroup G,
      B ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ∧
      B ≤ Gv (markedA d.flag.module) := by
  obtain ⟨hW, hWT, hR, hUK⟩ := module_inputs_of_localConfiguration d c hblock hK hn hLK hchar hL hz
  let := hW
  obtain ⟨h23, h3⟩ := residual_plus_local_orders d c hK hn hchar hL hz
  let P3 : Sylow 3 (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz (Lv L (markedV d.flag.module))) := Classical.choice inferInstance
  obtain ⟨hLM, hLn, h65⟩ := residual_local_normality_and_baumann d c
  have hzL : ⁅zpowers (markedZ d.flag.module), Lv L (markedV d.flag.module)⁆ ≠ ⊥ := by
    intro he
    have hc := AlternatingBranches.CoveredSix.source_commutator_card d.flag.module
    rw [AlternatingBranches.CoveredSix.source_commutator_eq_seed d.flag.module, he, card_bot] at hc
    norm_num at hc
  obtain ⟨e, hLB, _, hTB, hB, hfix⟩ := exists_replacement_with_fixed_comparison
    K L (T : Subgroup G) (normalizer (L : Set G))
    (ChapterB.baumann (Tv (T : Subgroup G) (markedV d.flag.module)))
    (markedZ d.flag.module) (markedV d.flag.module) hblock hL hz hK hn hLK rfl
    hWT hR hUK hLM hLn h65 h23 P3 (h3 P3) hzL
  exact ⟨replacement K e 6, hB,
    replacement_centralizes_markedA d c hblock hK hn hLK hchar hL hz e hLB hTB hfix⟩

/-- The original source hypotheses exclude the ordinary A₇ block. -/
theorem not_ordinarySeven_original_source
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
      centralizer ({markedZ d.flag.module} : Set G))
    (model : RankTwo.ReducedModel (plusImage K L (T : Subgroup G)
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K)) :
    ¬ IsAlternatingBlock K 7 := by
  intro hblock
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke
    hm standing.counterexample hfusion
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz model).1
  obtain ⟨B, hB, hc⟩ := ordinarySeven_replacement_centralizes_markedA_of_localConfiguration
    d c hblock hK hn hLK hchar hL hz
  exact selected_not_centralizes_markedA_original_source d V₃ earlier standing hm hfusion hform
    hfailure h1332 h63 B hB hL hz hc

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
