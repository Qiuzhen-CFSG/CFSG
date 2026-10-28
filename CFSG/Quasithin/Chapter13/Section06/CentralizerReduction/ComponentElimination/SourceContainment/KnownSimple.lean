module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment.OriginalSource
public import CFSG.Quasithin.ChapterA.Section03.SourceComponents.Containment.KnownSimple

/-!
# Containment and escape on the full known-simple catalogue

The proved full-catalogue unique-containment assertion of A.3.12 supplies
the last component-classification input in the original 13.6.20 assembly.
Together with the model-independent join-core argument for 13.6.21, it
gives Lᵥ≤K and K⊄N(L) on the same original marked configuration.

No A.3.6, A.3.8, A.3.12, A.3.18 or B.5 classification callback remains.
The original flag, preceding local data, singular fusion, reduced-model
catalogue and universal 13.3.2/13.6.3 inputs remain the genuine source
premises for the enclosing nonsingular-centralizer proof.

Source: Aschbacher–Smith, A.3.12, pp.47–48, and 13.6.20–21, pp.931–932.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment
open ComponentSelection A5Module ComponentReduction InitialSieve
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

/-- Both original source conclusions, with every component and module
classification input supplied by its full-catalogue producer. -/
theorem containment_and_noncontainment_original_source
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
      (markedZ d.flag.module) (markedV d.flag.module) hL hz K)) :
    Lv L (markedV d.flag.module) ≤ K ∧ ¬ K ≤ normalizer (L : Set G) := by
  refine ⟨lv_le_original_source_without_A318 d V₃ earlier standing hm hfusion ?_
    h1332 h63 hK hL hz model,
    not_le_normalizer_original_source d V₃ earlier standing hm hfusion h1332 h63 hK⟩
  intro X _ _ hX hO S B hB
  exact ChapterA.Section03.SourceComponents.containment_knownSimple hX hO S B hB

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceContainment
