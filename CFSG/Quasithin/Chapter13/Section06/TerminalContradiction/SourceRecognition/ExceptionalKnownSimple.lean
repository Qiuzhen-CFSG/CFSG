module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.OmegaKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LocalTransport
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LiftingKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.Source523KnownSimple
public import CFSG.KnownSimple.CarrierCatalogue.ClassificationInclusion
/-!
# The original A₅ branch reduced to an actual normal J₄ component

The genuine 5.2.3 theorem constructs the central-omega exceptional seed.
All auxiliary A.3.12 callbacks have been removed. The proved exceptional
containing catalogue transports that seed to the singular centralizer;
its ordinary exceptional candidates are excluded by the original terminal
ratio argument. Hence the original counterexample yields a global known
model or a literal normal C-component with J₄ two-core quotient.

The J₄ alternative is a remaining mathematical obligation, not an assumed
classification exclusion. The result preserves the original hypotheses
and can be completed by an independent source J₄ exclusion.
Source: Aschbacher–Smith 13.6.27, pp.934–935, and A.3.12, pp.47–48.
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
  (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
  (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
  (hcounter : IsA5Counterexample G)
  (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
include d hCv houtside hcounter h523

/-- The original component construction, with the one unresolved J₄ row retained. -/
theorem source_normal_candidate_or_jankoFour_or_global :
    (∃ K : Subgroup (centralizer (V₁ : Set G)), K.IsCComponent ∧ K.Normal ∧
      (Candidate ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K ∨
        Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model))) ∨ Source523.GlobalAlternative G := by
  let := d.elementary
  rcases omega_candidate_or_global_knownSimple d hCv houtside hcounter h523 with hl | hg
  · obtain ⟨KZ, hKZ, hcZ⟩ := hl
    obtain ⟨B, hB, hn, hc, _⟩ :=
      exists_normalized_local_candidate_in_singular_centralizer d KZ hKZ hcZ
    have hTC : (T : Subgroup G) ≤ centralizer (V₁ : Set G) :=
      d.flag.one_invariant.trans (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
    let S := T.subtype hTC
    have hH := SourceAbelian.point_centralizer_mem_family d houtside
    have hsq := Chapter1.RadicalExclusions.sqtk_of_mem_H d.hypothesis.qtke hH.1.1
    have hQ : IsSQTK KnownSimple.IsKnownSimple
        ((centralizer (V₁ : Set G)) ⧸ pCore 2 (centralizer (V₁ : Set G))) := by
      refine ⟨?_, hsq.isKGroup.quotient _⟩
      intro p hp ho
      let : Fact p.Prime := ⟨hp⟩
      exact (primeRank_quotient_le_of_isTwoGroup p ho _ pCore_isPGroup).trans
        (hsq.stronglyQuasithin p hp ho)
    obtain ⟨K, hK, hnK, _, hcK⟩ := normal_candidate_or_jankoFour hQ S hB hn hc
    exact Or.inl ⟨K, hK, hnK, hcK⟩
  · exact Or.inr hg

/-- All proved exceptional candidate rows are eliminated in the original context. -/
theorem source_jankoFour_or_global :
    (∃ K : Subgroup (centralizer (V₁ : Set G)), K.IsCComponent ∧ K.Normal ∧
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model)) ∨ Source523.GlobalAlternative G := by
  let := d.elementary
  rcases source_normal_candidate_or_jankoFour_or_global d hCv houtside hcounter h523 with hl | hg
  · obtain ⟨K, hK, hn, hc | hj⟩ := hl
    · let := hn
      let := hc.quotient_isQuasisimple hK
      exact (terminal_contradiction_of_A5_source523_knownSimple d hCv houtside hcounter h523 hK hc).elim
    · exact Or.inl ⟨K, hK, hn, hj⟩
  · exact Or.inr hg

/-- The full known-simple goal follows after exactly the remaining actual
J₄ singular-centralizer exclusion. -/
theorem source_knownSimple_of_no_jankoFour
    (hJ4 : ∀ K : Subgroup (centralizer (V₁ : Set G)), K.IsCComponent → K.Normal →
      Nonempty ((K ⧸ pCore 2 K) ≃* Janko4.Model) → False) : KnownSimple.IsKnownSimple G := by
  rcases source_jankoFour_or_global d hCv houtside hcounter h523 with hl | hg
  · obtain ⟨K, hK, hn, hj⟩ := hl
    exact (hJ4 K hK hn hj).elim
  · have hm : ClassificationModels.IsQTKEModel G := by
      rcases hg with hm | ⟨f, hf⟩
      · exact .sporadic ⟨.m23, hm⟩
      · exact .rank_two f hf
    exact ⟨inferInstance, d.hypothesis.qtke.simple, hm.isKnownSimpleCarrier⟩

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
