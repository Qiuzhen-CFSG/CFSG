module

public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Intersections
public import CFSG.Quasithin.Chapter12.Section03.SourceAlternatingSeven.Source
public import CFSG.Quasithin.Chapter13.Section01.SourceHypotheses

/-!
# The actual A₇ row of the maximal-component catalogue

Hypothesis 13.1.1 rules out the global recognition alternatives of 12.2.13,
giving uniform centralizer escape. The Chapter12 source assembly constructs
local analysis, the repaired weak-closure bounds and the terminal contradiction,
excluding an actual isomorphism I/O₂,Z(I) ≃ A₇. This removes the A₇ rows from
the maximal-component catalogue used by SourceClassification/MaximalReduction.

The universal structural 12.2.2, seven-case module classification and 12.2.13
remain the permitted earlier inputs, discharged by qt-d-1332-source through
their Chapter12 producers. This export requires Hypothesis 13.1.1; it does
not discharge a Chapter12 consumer having only Hypothesis 12.2.3.
Source: Aschbacher--Smith, pp.807--812 and 13.1.2(3), p.866.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section03.SourceClassification
open Chapter12.Section02 Chapter12.Section03.SourceAlternatingSeven
open Chapter13.Section01
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {I : Subgroup G}

/-- All maximal members, including those constructed later in 12.3,
inherit the escape alternative from the same ambient exclusions. -/
theorem centralizerEscape_of_hypothesis1311
    (h : Hypothesis1311 T)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u}) : CentralizerEscape T := by
  intro L V hi D
  exact h.centralizer_escape earlier hi.maximal_faithful hi.quasisimple D

/-- The proposed maximal A₇ row gives the original chosen module and an
escaping ambient point centralizer, using exactly the allowed earlier inputs. -/
theorem alternatingSeven_setup_escape
    (h : Hypothesis1311 T)
    (hi : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (e : CentralQuotient I ≃* alternatingGroup (Fin 7))
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    ∃ (V : Subgroup G) (_S : Setup T I V),
      (T : Subgroup G) ≤ normalizer (V : Set G) ∧
      ∃ v ∈ V, v ≠ 1 ∧ ¬ centralizer ({v} : Set G) ≤ normalizer (I : Set G) := by
  obtain ⟨_, ⟨⟨V, ⟨D⟩⟩⟩, hv⟩ := structural G T I hi
  exact ⟨V, ⟨hi, D, e⟩, (hv V D).1,
    h.centralizer_escape earlier hi.maximal_faithful hi.quasisimple D⟩

/-- On the same original chosen module, the source escape lies in the
weight-four orbit after the independent local centralizer analysis. -/
theorem alternatingSeven_weight_four_escape
    (h : Hypothesis1311 T)
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u})
    {V : Subgroup G} (S : Setup T I V) (D : S.LocalAnalysis) :
    ∃ v : V, v ≠ 1 ∧ BinarySevenCode.weight (D.model.coordinates v).toAdd.val = 4 ∧
      ¬ centralizer ({(v : G)} : Set G) ≤ normalizer (I : Set G) :=
  weight_four_escape S D
    (h.centralizer_escape earlier S.hypothesis.maximal_faithful
      S.hypothesis.quasisimple S.chosen)

/-- Exclude the actual A₇ central-quotient rows of 13.1.2(3), with centralizer
escape discharged from the original Chapter13 ambient hypotheses. -/
theorem alternatingSeven_excluded_of_source_inputs
    (h : Hypothesis1311 T)
    (hi : Hypothesis1223 KnownSimple.IsKnownSimple T I)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (modules : Theorem1222Modules KnownSimple.IsKnownSimple.{u})
    (earlier : Theorem12213 KnownSimple.IsKnownSimple.{u}) :
    ¬ Nonempty (CentralQuotient I ≃* alternatingGroup (Fin 7)) :=
  centralQuotient_not_alternatingSeven hi structural modules
    (centralizerEscape_of_hypothesis1311 h earlier)

end CFSG.Quasithin.Chapter13.Section03.SourceClassification
