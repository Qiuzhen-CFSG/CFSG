module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalParabolicSetup
public import CFSG.Quasithin.Chapter10.SourceLocalParabolicAction

/-!
# The marked Chapter 10 action for the original A₅ input

Hypothesis 13.3.1 with the actual A₅ quotient supplies its Fundamental
Setup. In the nonnormal branch the resulting local module gives either
the Baumann normalizer bound or the marked symmetric-five action from
E.2.3. Both the minimal-parabolic and module-equality premises of the
earlier conditional consumer have now been discharged or avoided.

The remaining symmetric-five normalizer argument is still required.
Source: Aschbacher–Smith, 10.2.1 and 13.3.2(2), printed pp.742–743,885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The original 13.3.1 input reaches the actual marked E.2.3 alternatives,
without assuming normalization of its component or of a chosen module. -/
theorem exists_original_local_action
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal ∨
        Chapter10.SourceFiveAction D := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D, Chapter10.source_a5_baumann_normalizer_or_five_action_unconditional D e hn⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
