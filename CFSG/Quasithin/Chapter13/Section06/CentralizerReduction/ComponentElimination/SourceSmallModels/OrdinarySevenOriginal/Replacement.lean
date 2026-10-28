module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.Module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal.LocalInputs

/-!
# The ordinary A₇ replacement from the original source

The original flag and local configuration now supply the complete module,
Baumann, residual-normality and Sylow-three inputs of the seven-letter
calculation. Its actual residual lift has quotient A₆, contains Lᵥ and lies
in the same Y_z family. The construction retains the quotient coordinates,
relative-normalizer identity and both placements used in that calculation.

This is the subgroup replacement in the ordinary A₇ paragraph of 13.6.22.
The subsequent A₆ action and centralizer contradiction remain separate.
Source: Aschbacher–Smith, printed p.932.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
open ComponentSelection A5Module SourceContainment ComponentReduction InitialSieve
open AlternatingBranches.OrdinarySeven
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- Construct the literal seven-letter residual replacement with every
source placement and Y_z clause, from the original local configuration. -/
theorem replacement_of_localConfiguration
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
    ∃ e : (K ⧸ pCore 2 K) ≃* alternatingGroup (Fin 7),
      let S := ChapterB.baumann (Tv (T : Subgroup G) (markedV d.flag.module))
      Lv L (markedV d.flag.module) =
        (pResidual 2 (K ⊓ normalizer (S : Set G) : Subgroup G)).map
          (K ⊓ normalizer (S : Set G)).subtype ∧
      K ⊓ normalizer (S : Set G) ≤ ambientPreimage K e 6 ∧
      Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (ambientPreimage K e 6 : Set G) ∧
      Lv L (markedV d.flag.module) ≤ replacement K e 6 ∧
      replacement K e 6 ≤ K ∧
      Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (replacement K e 6 : Set G) ∧
      ⁅zpowers (markedZ d.flag.module), replacement K e 6⁆ ≠ ⊥ ∧
      IsPPerfect 2 (replacement K e 6) ∧
      Nonempty ((replacement K e 6 ⧸ pCore 2 (replacement K e 6)) ≃* alternatingGroup (Fin 6)) ∧
      replacement K e 6 ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ∧
      starImage (markedZ d.flag.module) (markedV d.flag.module) (replacement K e 6) ∈
        Xz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) := by
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
  let S := ChapterB.baumann (Tv (T : Subgroup G) (markedV d.flag.module))
  obtain ⟨e, hres, hN, hT, hLB, hBK, hBn, hBm, he, hw⟩ :=
    SourcePlacement.source_replacement K L (T : Subgroup G) (normalizer (L : Set G)) S
      (markedZ d.flag.module) (markedV d.flag.module) hblock hL hz hK hn hLK rfl
      hWT hR hUK hLM hLn h65 h23 P3 (h3 P3) hzL
  have hB := replacement_mem_Yz K L (T : Subgroup G) S
    (markedZ d.flag.module) (markedV d.flag.module) e 6 hK hres hN hT hzL hw
  have hsn := Source.starImage_normalizes_of_normalizes
    (Tv (T : Subgroup G) (markedV d.flag.module)) (replacement K e 6)
    (markedZ d.flag.module) (markedV d.flag.module) (hBK.trans hK.1.1) hBn
  have hspan : conjugateSpanBy
      (starImage (markedZ d.flag.module) (markedV d.flag.module) (replacement K e 6))
      (starImage (markedZ d.flag.module) (markedV d.flag.module)
        (Tv (T : Subgroup G) (markedV d.flag.module))) =
      starImage (markedZ d.flag.module) (markedV d.flag.module) (replacement K e 6) :=
    le_antisymm (conjugateSpanBy_le le_rfl hsn) (le_conjugateSpanBy _ _)
  refine ⟨e, hres, hN, hT, hLB, hBK, hBn, hBm, replacement_twoPerfect K e 6, he, hB, ?_⟩
  simpa only [hspan] using hB.2.2

/-- The ordinary A₇ paragraph, with the earlier characteristic-two,
component-invariance and 13.6.20 containment premises discharged. -/
theorem replacement_original_source
    (d : FlagSource T L V V₁ V₂) (V₃ : Subgroup G)
    (earlier : EarlierLocal T L (normalizer (L : Set G)) V V₂ V₃ (markedZ d.flag.module))
    (standing : RankTwo.LocalApplication.SourceHypothesis T L)
    (hm : SymmetricSix.ModuleData d.flag.module)
    (hfusion : ControlsFusionOfZ d.flag.module)
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
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K))
    (hblock : IsAlternatingBlock K 7) :
    ∃ B : Subgroup G,
      B ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ∧
      Lv L (markedV d.flag.module) ≤ B ∧ B ≤ K ∧
      Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (B : Set G) ∧
      ⁅zpowers (markedZ d.flag.module), B⁆ ≠ ⊥ ∧ IsPPerfect 2 B ∧
      Nonempty ((B ⧸ pCore 2 B) ≃* alternatingGroup (Fin 6)) ∧
      starImage (markedZ d.flag.module) (markedV d.flag.module) B ∈
        Xz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module) ∧
      ¬ IsAlternatingBlock B 7 := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke
    hm standing.counterexample hfusion
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz model).1
  obtain ⟨e, _, _, _, hLB, hBK, hBn, hBm, hp, he, hB, hs⟩ :=
    replacement_of_localConfiguration d c hblock hK hn hLK hchar hL hz
  exact ⟨replacement K e 6, hB, hLB, hBK, hBn, hBm, hp, he, hs,
    replacement_not_ordinarySeven K e 6⟩

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
