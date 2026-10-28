module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalFixedCenterTransvection
public import CFSG.Quasithin.Chapter10.SourceA5FixedCenterClassifiedAction

/-!
# G.6.4 for the original 13.3.1 fixed-center action

The literal Fundamental Setup yields its original H-star orbit W and
centralizer quotient. On the exact displacement orbit submodule, the actual
source actor satisfies every G.6.1 assumption and the full G.6.4 conclusion.
All generation and faithfulness premises are discharged.

Source: Aschbacher–Smith 10.2.1, G.6.4 and13.3.2(2), pp.743,345–346,884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem exists_original_fixed_center_classified_action
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hne : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥)
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L, Chapter10.SourceFixedCenterClassifiedAction D := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_exists_fixed_center_classified_action D e hn hne hout⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
