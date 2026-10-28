module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.OmegaCandidate
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LocalTransport
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.Lifting
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.CandidateComplete
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ActorNoSource523
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ClassificationKnownSimple
public import CFSG.KnownSimple.CarrierCatalogue.ClassificationInclusion

/-!
# The original A₅ terminal branch reaches the full classification

The original candidate construction below uses genuine earlier 5.2.3
to select a normalized component in the
central omega centralizer. The A₇ generation bound and E.2.2 diagram
argument construct its exceptional candidate. Transport to the singular
centralizer and the full A.3.12 embedding theorem then produce an actual
normal quasisimple exceptional C-component in C_G(V₁). The existing
13.6.27 and module-ratio endgame excludes this entire local alternative.

Only the genuine global alternatives of 5.2.3 remain; these are explicit
members of the complete Main Theorem and known-simple catalogues. No
component existence, quotient model, diagram action, normality,
quasisimplicity or uniqueness assumption is retained. The earlier 5.2.3
input, nonsingular-centralizer bound and singular escape remain with their
source producers.

The final catalogue endpoints below now use the source-specialized route in
`ClassificationKnownSimple`, which discharges the embedding, normality and
earlier seed uses without the universal A.3.12 input. Their old signatures
are preserved for compatibility; the reexported `_knownSimple` variants omit
that input. The preceding candidate constructor retains its original proof
from the full embedding theorem. Genuine 5.2.3 and the two original
centralizer conditions remain inputs to both routes.

The global family here includes field-two rank-two endpoints, as does
Source523.GlobalAlternative. Consequently the final result is the full
Main Theorem catalogue, without asserting the narrower field restriction
in the standalone Theorem D catalogue.
Source: Aschbacher–Smith, 13.6.27 and its terminal paragraph,
printed pp.934–935; Theorem 5.2.3, printed p.649.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open Components Components.CandidateSelection Components.SuzukiIsolation
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Context T L V V₁ V₂ V₃)
  (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
    IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
    ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
      Chapter1.Section02.A312Conclusion B)
  (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
  (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
  (hcounter : IsA5Counterexample G)
  (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
include d hA312 hCv houtside hcounter h523

/-- Construct the normal quasisimple exceptional component in the literal
singular centralizer, or retain the genuine earlier global model. -/
theorem source_normal_candidate_or_global :
    (∃ K : Subgroup (centralizer (V₁ : Set G)), K.IsCComponent ∧ K.Normal ∧ IsQuasisimple (K ⧸ pCore 2 K) ∧
      Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K) ∨
    Source523.GlobalAlternative G := by
  let := d.elementary
  rcases omega_candidate_or_global d hA312 hCv houtside hcounter h523 with hl | hg
  · obtain ⟨KZ, hKZ, hcZ⟩ := hl
    obtain ⟨B, hB, hn, hc, _⟩ :=
      exists_normalized_local_candidate_in_singular_centralizer d KZ hKZ hcZ
    have hTC : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
      d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
    let S := T.subtype hTC
    have hH := SourceAbelian.point_centralizer_mem_family d houtside
    have hsq := Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1
    have hQ : IsSQTK KnownSimple.IsKnownSimple
        ((centralizer (V₁ : Set G)) ⧸ pCore 2 (centralizer (V₁ : Set G))) :=
      by
      refine ⟨?_, hsq.isKGroup.quotient _⟩
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
        (hsq.stronglyQuasithin p hp ho)
    obtain ⟨K, hK, hnK, _, hcK⟩ := exists_normal_candidate_of_local_candidate hA312 hQ S hB hn hc
    exact Or.inl ⟨K, hK, hnK, hcK.quotient_isQuasisimple hK, hcK⟩
  · exact Or.inr hg

-- Retain the unused hA312 binder in the three compatibility interfaces.
set_option linter.unusedSectionVars false in
/-- The entire local alternative of 5.2.3 is excluded by the terminal ratio
argument on its constructed component. -/
theorem source_globalAlternative_of_A5_counterexample : Source523.GlobalAlternative G := by
  exact source_globalAlternative_of_source523 d hCv houtside hcounter h523

set_option linter.unusedSectionVars false in
/-- The original A₅ counterexample lies in the full Main Theorem catalogue. -/
theorem source_qtkeModel_of_A5_counterexample : ClassificationModels.IsQTKEModel G := by
  exact source_qtkeModel_of_A5_counterexample_knownSimple d hCv houtside hcounter h523

set_option linter.unusedSectionVars false in
/-- The resulting actual model satisfies the complete guarded known-simple
class, using finiteness and simplicity from the original source hypotheses. -/
theorem source_knownSimple_of_A5_counterexample : KnownSimple.IsKnownSimple G := by
  exact source_knownSimple_of_A5_counterexample_knownSimple d hCv houtside hcounter h523

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
