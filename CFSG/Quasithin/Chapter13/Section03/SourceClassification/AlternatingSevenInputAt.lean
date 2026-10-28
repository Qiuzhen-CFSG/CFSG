module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.At.Source
public import CFSG.Quasithin.Chapter12.Section02.SourceApplications.RecognitionAt
public import CFSG.Quasithin.Chapter13.Section03.SourceClassification.AlternatingSevenInput

/-!
# The guarded A₇ exclusion at the original G,T

The local structural and seven-module inputs give 12.2.13 under the standing
multiple-overgroup hypothesis. Hypothesis 13.1.1 excludes its three recognized
ambient groups, giving centralizer escape for every original chosen module.
The localized Chapter12 proof constructs the natural action, weak closure,
normal A₅ component and terminal product, and excludes the literal quotient
by the preimage of Z(I/O₂(I)). No recognition or local-analysis premise remains.

The catalogue application removes exactly this row before applying the existing
maximal-component reduction to the original faithful member. Its other catalogue
rows and maximal quasisimplicity remain with qt-d-1332-source; the structural
and module producers remain with qt-d-1222-source and qt-d-1332-source.

Source: Aschbacher–Smith, 12.3.1, pp.807–812, and 13.1.2(3), p.866.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceClassification
open Chapter12.Section02 Chapter12.Section03.SourceAlternatingSeven
open Chapter13.Section01 Noncentrality.SupercriticalSource
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {I : Subgroup G}

/-- Uniform escape at the same ambient G,T, with recognition discharged. -/
theorem centralizerEscape_of_source_inputs_at
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T) :
    CentralizerEscape T := by
  intro L V hi D
  exact SourceAssembly.At.centralizer_escape_of_many_at structural modules hmany h
    hi.maximal_faithful hi.quasisimple D

/-- Exclude the actual I/O₂,Z(I) ≃ A₇ row using only the guarded original
ambient hypotheses and the two earlier 12.2.2 inputs at G,T. -/
theorem alternatingSeven_excluded_of_source_inputs_at
    (h : Hypothesis1311 T)
    (hi : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T) :
    ¬ Nonempty (CentralQuotient I ≃* alternatingGroup (Fin 7)) :=
  centralQuotient_not_alternatingSeven_at hi structural modules
    (centralizerEscape_of_source_inputs_at h hmany structural modules)

/-- Remove the literal A₇ row from the maximal quotient catalogue. The
other rows are the independent earlier-source input of the catalogue owner. -/
theorem maximal_models_of_alternatingSeven_exclusion_at
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (catalogue : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I) ∨
        Nonempty (CentralQuotient I ≃* alternatingGroup (Fin 7))) :
    ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I) := by
  intro I hi
  exact (catalogue I hi).resolve_right
    (alternatingSeven_excluded_of_source_inputs_at h hi hmany structural modules)

/-- The original MaximalReduction consumer, with the A₇ elimination and
the local structural input supplied at the same G,T. No replacement of the
faithful member, its quotient, or its chosen modules is made. -/
theorem source1332OneTwo_of_catalogue_with_alternatingSeven_at
    (h : Hypothesis1311 T)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (modules : Theorem1222ModulesAt KnownSimple.IsKnownSimple T)
    (quasisimple : ∀ I : Subgroup G, FaithfulMaximalLocal T I →
      IsQuasisimple (I ⧸ pCore 2 I))
    (catalogue : ∀ I : Subgroup G, Hypothesis1223 KnownSimple.IsKnownSimple T I →
      MidSizeModel (Chapter1.XiQuotient I) ∨
        Nonempty (CentralQuotient I ≃* alternatingGroup (Fin 7))) :
    Source1332OneTwo T :=
  SourceAssembly.At.source1332OneTwo_of_maximal_models h quasisimple
    (maximal_models_of_alternatingSeven_exclusion_at h hmany structural modules catalogue)
    structural

end CFSG.Quasithin.Chapter13.Section03.SourceClassification
