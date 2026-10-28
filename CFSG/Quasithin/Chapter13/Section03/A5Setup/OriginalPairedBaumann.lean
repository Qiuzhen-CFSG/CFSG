module
public import CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
public import CFSG.Quasithin.Chapter12.Section02.ReductionSource.OrbitSetup
public import CFSG.Quasithin.Chapter10.SourceA5ZeroCentralizerBaumann

/-!
# The original paired Baumann action under Hypothesis 13.3.1

The original A₅ Fundamental Setup and a Baumann normalizer escaping M yield
the paired marked E.2.3 action. Nonnormality excludes the single factor;
the same quotient identifies the Thompson and Baumann images with the two
transposition four-groups. This is the quotient input to the zero-centralizer
four-dihedral-factor calculation, without any supplied model or coordinates.

Source: Aschbacher–Smith, 10.2.1 and 13.3.2(2), pp.742–743 and 884–885.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
open Chapter3.Section02
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The actual 13.3.1 input gives the paired Baumann quotient marking on
its original local module. -/
theorem paired_baumann_action
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G)) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      Chapter10.SourcePairedBaumannAction D := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_a5_paired_baumann_action D e hn hout⟩

/-- The original zero-centralizer hypotheses identify the marked action's
kernel with O₂(L₀T). -/
theorem zero_centralizer_paired_baumann_action
    (h : Chapter14.Section03.FaithfulSource.Hypothesis1331 T L)
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hout : ¬ normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤
      normalizer (localOrbit T L : Set G))
    (hz : omegaOneCenterAmbient (T : Subgroup G) ⊓ centralizer (localOrbit T L : Set G) = ⊥) :
    ∃ D : FundamentalSetup KnownSimple.IsKnownSimple T L,
      Chapter10.SourcePairedBaumannAction D ∧
        centralizer (D.moduleSubgroup.subgroupOf (localJoin T L) : Set (localJoin T L)) =
          pCore 2 (localJoin T L) := by
  obtain ⟨D⟩ := (hypothesis1221 h e).exists_original_fundamentalSetup
  exact ⟨D,Chapter10.source_a5_zero_centralizer_paired_action D e hn hout hz⟩

end CFSG.Quasithin.Chapter13.Section03.A5Setup.OriginalMaximality
