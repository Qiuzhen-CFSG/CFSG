module
public import CFSG.Quasithin.Chapter10.SourceA5EscapingOrthogonalAction
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalFixedCenterOrthogonalAction
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalZeroNormalizerControl

/-!
# The orthogonal action from the original escaping normalizer

The original 13.3.1 hypotheses construct the fundamental setup. Zero-center
normalizer control and positive-center recognition together give the literal
orthogonal action without a separate assumption on the fixed center.

Source: Aschbacher–Smith, 10.2.1 and 13.3.2(2), printed pp.743,884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

theorem exists_original_escaping_orthogonal_action
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      Chapter10.SourceFixedCenterOrthogonalAction D := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_exists_escaping_orthogonal_action D e hn hout⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
