module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5ComponentNormalizer.Completion

/-!
# Original A₅ component normalizer containment

The literal 13.3.1 input supplies the original fundamental setup. The proved
component-normalizer clause of source 10.2.6(2) places N_G(L) in the normalizer of the original
T-orbit of L, without a chosen module or element-centralizer premise.
Source: Aschbacher--Smith, 10.2.6 and 13.3.2, printed pp.748–749 and884–885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Component-normalizer control for the original Chapter13 input. -/
theorem component_normalizer_le
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    normalizer (L : Set G) ≤ normalizer (localOrbit T L : Set G) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_a5_component_normalizer_le D e hn

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
