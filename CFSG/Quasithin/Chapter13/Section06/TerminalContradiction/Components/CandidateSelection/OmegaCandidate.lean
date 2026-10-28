module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.SourceSelection
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.AlternatingSeven
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection.LinearDiagramNonsolvable

/-!
# The exceptional candidate in the original central omega centralizer

The normalized component selected by source 5.2.3 cannot have A₇ quotient:
its Sylow extension is outside the unique maximal local, so 13.6.25 and
the actual A₇ generation bound give contradictory values of n. For the
linear equality branch, the selected outside local is nonsolvable and
minimal parabolic; E.2.2 therefore supplies the actual diagram action.
The two remaining sporadic quotient identifications are already candidates.

Thus no exceptional model or diagram premise is left in the initial
component selection. Its lift into the singular centralizer is the next
step. The full earlier 5.2.3 global alternatives remain explicit because
they are themselves outcomes of the final classification.
Source: Aschbacher–Smith, 13.6.27, printed p.934, and E.2.2, pp.215–216.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
open SuzukiIsolation SourceParameters Section06.CentralizerReduction
open Section06.CentralizerReduction.A5Module
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}
  (d : Section05.A5Source.Context T L V V₁ V₂ V₃)

include d in
/-- The exact component selected by 5.2.3 is an exceptional candidate. -/
theorem SelectedSeed.candidate [IsElementaryAbelian 2 V]
    (s : EarlierA5Setup T L V (normalizer (L : Set G)) (normalizer (V : Set G)))
    (seed : SelectedSeed T (normalizer (L : Set G))) :
    Candidate ((T : Subgroup G).subgroupOf
      (centralizer (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G))) seed.K := by
  rcases seed.models with ⟨_, ha | hj | hm⟩ | ⟨he, ⟨e⟩⟩
  · exact (source523_seed_not_alternatingSeven d.hypothesis.qtke s seed.H
      seed.residual_outside seed.K seed.contains seed.normalizes ha).elim
  · exact Or.inl hj
  · exact Or.inr (Or.inl hm)
  · have hHC : seed.H ≤ centralizer
        (Stellmacher.omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
      rw [← seed.residual_generates]
      exact sup_le (seed.contains.trans (map_subtype_le _)) (sylow_le_omega_centralizer T)
    exact linear_candidate_of_HStar_nonsolvable T d.normalizes_L seed.star
      seed.nonsolvable hHC e seed.K he

/-- Select an actual exceptional component in the central omega centralizer,
with every model and diagram premise supplied by the original source. -/
theorem omega_candidate_or_global
    (hA312 : ∀ (Y : Type u) [Group Y] [Finite Y],
      IsSQTK KnownSimple.IsKnownSimple Y → pCore 2 Y = ⊥ →
      ∀ (S : Sylow 2 Y) (B : Subgroup Y), B ∈ ChapterA.Section03.localCComponents S →
        Chapter1.Section02.A312Conclusion B)
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
  rcases selected_seed_or_global d hA312 hCv houtside hcounter h523 with hseed | hg
  · obtain ⟨seed⟩ := hseed
    obtain ⟨s, _, _⟩ := source_parameter_setup d hA312 hCv houtside hcounter
    exact Or.inl ⟨seed.K, seed.component, seed.candidate d s⟩
  · exact Or.inr hg
end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateSelection
