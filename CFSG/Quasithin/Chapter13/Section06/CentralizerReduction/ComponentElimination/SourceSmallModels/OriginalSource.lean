module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.SourceGeometry
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.KnownSimple
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceTransferFields.OriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.AlternatingBranches.CoveredSix.Exclusion

/-!
# Original binary rank-two and covered-six exclusions

The original flag supplies the moving four-group, its parabolic action and
its actual Sylow-central conjugate a. The proved A₆ and G₂(2)′ fixed-space
calculations, followed by Sylow averaging in C_G(v)/⟨v⟩, force K to centralize
a. The original 13.6.17 transfer contradicts that centralization. The same
containment and local configuration feed the covered-A₆ normalizer obstruction.

The complete 13.6.20 producer supplies Lᵥ≤K, and earlier original-source
producers supply component invariance and characteristic two. No action
marking, B.2.14 supplement, A.3.12 or A.3.18 callback remains. The genuine
flag/local data, reduced catalogue, fusion/form, failed-normalization and
universal 13.3.2/13.6.3 premises remain with the section assembly. These are
three cases of 13.6.22; the linear-three and seven-point cases are separate.

Source: Aschbacher–Smith, 13.6.17 and 13.6.20–22, printed pp.930–933.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
open CFSG.Quasithin.ChapterC
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
open ComponentSelection A5Module ComponentReduction InitialSieve
open SourceContainment
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- The A₆ and G₂(2)′ source actions centralize the exact original marked a. -/
theorem binary_centralizes_markedA_of_localConfiguration
    (d : FlagSource T L V V₁ V₂)
    (c : LocalConfiguration (normalizer (L : Set G)) d.flag)
    (h : BinaryRankTwo.SourceBlock K)
    (hK : K ∈ Yz L (T : Subgroup G) (markedZ d.flag.module) (markedV d.flag.module))
    (hn : Tv (T : Subgroup G) (markedV d.flag.module) ≤ normalizer (K : Set G))
    (hLK : Lv L (markedV d.flag.module) ≤ K)
    (hchar : generalizedFitting (Gv (markedV d.flag.module)) =
      pCore 2 (Gv (markedV d.flag.module)))
    (hTL : (T : Subgroup G) ≤ normalizer (L : Set G)) :
    K ≤ Gv (markedA d.flag.module) := by
  have hs : IsShort K := by
    cases h with
    | alternating h => exact h.2.1
    | g2 h => exact h.1
  obtain ⟨e⟩ := sourceLineData_of_localConfiguration d c hs hK hn hLK hchar hTL
  have hf := BinaryRankTwo.source_centralizer_eq e h
  rw [BinaryRankTwo.sourceU_eq K hs] at hf
  exact short_centralizes_markedA d c hs hK hn hLK hchar hTL hf

/-- The original source excludes the A₆, G₂(2)′ and covered-A₆ block cases. -/
theorem not_binary_or_coveredSix_original_source
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
    ¬ BinaryRankTwo.SourceBlock K ∧ ¬ IsExceptionalAhat6Block K := by
  obtain ⟨c⟩ := localConfiguration_of_earlier_source d (normalizer (L : Set G)) V₃
    earlier standing.counterexample hfusion
  have hn := component_invariant_original_source d V₃ earlier standing.qtke hm
    standing.counterexample hfusion K hK
  have hchar := generalizedFitting_eq_pCore_of_earlier_source d V₃ earlier standing.qtke
    hm standing.counterexample hfusion
  have hLK := (containment_and_noncontainment_original_source d V₃ earlier standing hm
    hfusion h1332 h63 hK hL hz model).1
  refine ⟨?_, AlternatingBranches.CoveredSix.not_exceptional_of_localConfiguration
    d.flag c hK hn hLK hchar earlier.T_normalizes_L le_rfl⟩
  intro h
  have hc := binary_centralizes_markedA_of_localConfiguration d c h hK hn hLK hchar
    earlier.T_normalizes_L
  have hnc := (SourceTransferFields.noncentrality_and_field_exclusions_original_source
    d V₃ earlier standing hm hfusion hform hfailure h1332 h63 K hK hL hz
    ChapterB.QuasisimpleSource.BinaryField.two).1 c.aPoint
  have hconj : ∃ g : G, (c.aPoint : G) = MulAut.conj g (markedZ d.flag.module) := by
    obtain ⟨g, hg⟩ := c.a_conjugate
    exact ⟨g, c.aPoint_val.trans hg.symm⟩
  apply hnc hconj c.a_checked_central
  simpa only [c.aPoint_val, Gv] using hc

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
