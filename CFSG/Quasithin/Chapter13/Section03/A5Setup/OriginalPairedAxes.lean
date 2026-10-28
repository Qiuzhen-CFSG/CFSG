module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5OriginalPairedAxes

/-!
# The original A₅ block on its marked quotient axis

Hypothesis 13.3.1 supplies the original Fundamental Setup. The Chapter 10
axis theorem then locates its literal L in the same marked paired action
used by the Baumann-normalizer escape, with no supplied alignment premise.
Source: Aschbacher–Smith, 10.2.1 and 13.3.2(2), pp.742–743 and884–885.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The paired axes locate the original block under the original 13.3.1 hypotheses. -/
theorem original_paired_axes
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      Chapter10.SourceOriginalPairedAxes D := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_a5_original_paired_axes D e hn hout⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
