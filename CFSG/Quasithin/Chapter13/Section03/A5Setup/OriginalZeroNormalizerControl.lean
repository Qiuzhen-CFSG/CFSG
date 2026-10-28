module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5ZeroNormalizerControl

/-!
# The original zero-center Baumann normalizer conclusion

The literal Hypothesis 13.3.1 constructs the fundamental setup. Its original
zero-center alternating-five branch therefore has Baumann normalizer inside
the normalizer of the original component orbit. This application discharges
the four-factor action and elementary-choice premises of the 10.2.1 argument.

Source: Aschbacher–Smith 10.2.1 and 13.3.2(2), printed pp.743,884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem zero_baumann_normalizer_le
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓
      centralizer (localOrbit T L : Set G) = ⊥) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact Chapter10.source_a5_zero_baumann_normalizer_le D e hn hz

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
