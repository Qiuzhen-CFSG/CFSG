module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5BaumannNormalizerControl

/-!
# Baumann normalizer containment from the original Hypothesis 13.3.1

The original hypothesis constructs the fundamental setup. The completed
alternating-five 10.2.1 theorem then places the Baumann normalizer in the
normalizer of the original component orbit.

Source: Aschbacher–Smith 10.2.1 and 13.3.2(2), printed pp.743,884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- Original 13.3.1 supplies the full alternating-five Baumann normalizer conclusion. -/
theorem baumann_normalizer_le
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_a5_baumann_normalizer_le D e hn

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
