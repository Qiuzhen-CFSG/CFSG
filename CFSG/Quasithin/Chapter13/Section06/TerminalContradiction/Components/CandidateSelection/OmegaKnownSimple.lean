module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.OmegaCandidate
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ParametersKnownSimple
/-!
# The original central-omega seed without A.3.12

The callback-free A₅ parameters construct the original outside residual.
The genuine source 5.2.3 theorem selects its containing component, and the
proved A₇ exclusion and diagram action produce the exceptional candidate.
The proper-embedding theorem is not used before the subsequent lift.
Source: Aschbacher–Smith 13.6.25–27, pp.934–935.
-/
public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open SourceParameters CentralizerReduction CentralizerReduction.A5Module
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G} [IsElementaryAbelian 2 V]
open Section05.A5Source
/-- The first residual of 13.6.27 lies in the original line centralizer. -/
theorem source_initial_residual_of_context_knownSimple
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G) :
    ∃ H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)),
      H ≤ centralizer (V₁ : Set G) ∧
      1 < ChapterE.generationParameter H ∧
      (pResidual 2 H).map H.subtype ⊔ (T : Subgroup G) = H ∧
      ¬ (pResidual 2 H).map H.subtype ≤ normalizer (L : Set G) ∧
      (T : Subgroup G) ≤ normalizer ((pResidual 2 H).map H.subtype : Set G) := by
  obtain ⟨s, hs, _⟩ := source_parameter_setup_knownSimple d hCv houtside hcounter
  have hc : centralizer ({s.z.val} : Set G) = centralizer (V₁ : Set G) := by
    rw [← hs, zpowers_eq_closure, centralizer_closure]
  have hT : (T : Subgroup G) ≤ centralizer ({s.z.val} : Set G) := by
    rw [hc]
    exact d.flag.one_invariant.trans
      (normalizer_le_centralizer_of_card_two V₁ d.flag.one_card)
  simpa only [hc] using exists_initial_residual_knownSimple d.hypothesis.qtke s hT


namespace Components.CandidateSelection
open SuzukiIsolation
variable (d : Context T L V V₁ V₂ V₃)

omit [IsElementaryAbelian 2 V] in
/-- Apply the genuine full 5.2.3 to the constructed HStar member. The local
branch has its source normalization proved; the full global alternatives
remain available to the final classification assembly. -/
theorem selected_seed_or_global_knownSimple
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) :
    Nonempty (SelectedSeed T (normalizer (L : Set G))) ∨ Source523.GlobalAlternative G := by
  let := d.elementary
  obtain ⟨s, hs, _⟩ := source_parameter_setup_knownSimple d hCv houtside hcounter
  obtain ⟨H, hH, _, hn, hgen, hout, hTR⟩ :=
    source_initial_residual_of_context_knownSimple d hCv houtside hcounter
  rcases h523 G T L (normalizer (L : Set G)) V 2
      (original_source523_setup d s) H hH hn with hl | hg
  · obtain ⟨_, _, K, hK, hRK, hm⟩ := hl
    have hns : ¬ Group.IsSolvable H := by
      intro hsol
      exact hH.1.2 ((source_13_6_25_knownSimple d.hypothesis.qtke s).2.2.1 H hH.1.1 hsol)
    exact Or.inl ⟨{
      H := H
      star := hH
      parameter := hn
      nonsolvable := hns
      K := K
      component := hK
      contains := hRK
      residual_generates := hgen
      normalizes := normalizes_component_over_residual T H _
        (sylow_le_omega_centralizer T) hns hTR hK hRK
      residual_outside := hout
      models := hm }⟩
  · exact Or.inr hg


omit [IsElementaryAbelian 2 V] in
/-- Select an actual exceptional component in the central omega centralizer,
with every model and diagram premise supplied by the original source. -/
theorem omega_candidate_or_global_knownSimple
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) :
    (∃ K : Subgroup (centralizer
        (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G)),
      K.IsCComponent ∧ Candidate ((T : Subgroup G).subgroupOf
        (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))) K) ∨
      Source523.GlobalAlternative G := by
  let := d.elementary
  rcases selected_seed_or_global_knownSimple d hCv houtside hcounter h523 with hseed | hg
  · obtain ⟨seed⟩ := hseed
    obtain ⟨s, _, _⟩ := source_parameter_setup_knownSimple d hCv houtside hcounter
    exact Or.inl ⟨seed.K, seed.component, seed.candidate d s⟩
  · exact Or.inr hg
end Components.CandidateSelection
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
