module

public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.OriginalEscape
public import CFSG.Quasithin.Chapter12.Section02.StructuralSource.At

/-!
# Vector and singular escape at the original A₅ context

Apply 12.2.13 only at the original G,T,L,V. Hypothesis 13.3.1 excludes
its three recognition alternatives. The existing two-orbit argument then
transports the escaping vector to the singular line of this same Context,
using its nonsingular centralizer bound and its actual marking.

This is conditional on the local earlier 12.2.13 implication; it does not
extend that implication to other ambient groups or Sylow subgroups.
Source: Aschbacher--Smith, 12.2.13 and 13.3.5, pp.799 and 886.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source

variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- Only the earlier classification on the same G and T is required. -/
theorem vector_escape_of_source12213_at (d : Context T L V V₁ V₂ V₃)
    (h12213 : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T) :
    ∃ x ∈ V, x ≠ 1 ∧ ¬ centralizer ({x} : Set G) ≤ normalizer (L : Set G) := by
  rcases h12213 L V (original_hypothesis1223 d) d.chosen with hx | hl | ha | hm
  · exact hx
  · obtain ⟨n, hn, _, hg⟩ := hl
    exact (d.hypothesis.no_linear (n+1) (by rcases hn with rfl | rfl <;> simp) hg).elim
  · exact (d.hypothesis.no_alternating_nine ha.2).elim
  · exact (d.hypothesis.hypothesis1311.no_M24 hm.2).elim

/-- Apply the orbit transport to precisely the marking used by the
terminal consumer, without choosing a new Context or a new singular line. -/
theorem singular_escape_of_source12213_at (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (h12213 : Chapter12.Section02.Theorem12213At KnownSimple.IsKnownSimple T) :
    ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G) :=
  singular_escape_of_vector_escape d hCv (vector_escape_of_source12213_at d h12213)

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
