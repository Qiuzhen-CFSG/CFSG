module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OriginalAssembly.SevenSelection
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.OrdinarySevenOriginal
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels.ExceptionalSevenOriginal

/-!
# Excluding the original A₇ plus quotient in 13.6.22

C.1.24 now constructs the ordinary or exceptional A₇ block from the actual
plus quotient and original flag hypotheses. Each constructed block violates
its proved original source exclusion. Thus the alternating-seven constructor
is removed from the reduced quotient catalogue without a block-selection,
shortness, or action-model premise.

Source: Aschbacher--Smith 13.6.22, printed p.932.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
open ComponentSelection A5Module ComponentReduction InitialSieve SourceContainment
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {K L V V₁ V₂ : Subgroup G}

theorem not_alternating_plus_original_source
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
    : ¬ Nonempty (plusImage K L (T : Subgroup G) (markedZ d.flag.module)
      (markedV d.flag.module) hL hz K ≃* alternatingGroup (Fin 7)) := by
  rintro ⟨e⟩
  rcases OriginalAssembly.alternating_blocks_original_source d V₃ earlier standing hm hfusion
    h1332 h63 hK hL hz e with ho | he
  · exact not_ordinarySeven_original_source d V₃ earlier standing hm hfusion hform hfailure
      h1332 h63 hK hL hz (.a7 ⟨e⟩) ho
  · exact not_exceptionalSeven_original_source d V₃ earlier standing hm hfusion hform hfailure
      h1332 h63 hK hL hz (.a7 ⟨e⟩) he

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentElimination.SourceSmallModels
