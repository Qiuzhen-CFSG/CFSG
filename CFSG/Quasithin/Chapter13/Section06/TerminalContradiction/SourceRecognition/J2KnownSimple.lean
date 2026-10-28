module
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ResidualKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.ContextKnownSimple
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.SourceRecognition.J2Complete
public import CFSG.Quasithin.Chapter13.Section06.TerminalContradiction.Components.CandidateStructure
/-!
# The original J₂ terminal contradiction over known simple groups

The actual J₂ component is isolated by its full three- and five-rank.
The callback-free parameter and prime-core deductions then construct the
component conclusion used by the original quadratic-ratio contradiction.
Neither A.3.12 nor 5.2.3 is needed after the actual component is supplied.
The exceptional local-seed construction remains a separate input producer.

Source: Aschbacher–Smith 13.6.25–27 and terminal paragraph, pp.934–935.
-/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
open CentralizerReduction CentralizerReduction.A5Module Section05.A5Source
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ : Subgroup G}

/-- The J₂ component branch with both former universal classification
callbacks and the quotient-quasisimplicity premise discharged. -/
theorem terminal_contradiction_of_A5_j2_knownSimple
    (d : Context T L V V₁ V₂ V₃)
    (hCv : centralizer ({markedV d.flag.flag.module} : Set G) ≤ normalizer (V : Set G))
    (houtside : ¬ centralizer (V₁ : Set G) ≤ normalizer (L : Set G))
    (hcounter : IsA5Counterexample G)
    {K : Subgroup (centralizer (V₁ : Set G))} (hK : K.IsCComponent)
    (e : (K ⧸ pCore 2 K) ≃* Sporadic.LeechRelated.J2.Carrier) : False := by
  let := d.elementary
  have hc : Components.Candidate
      ((T : Subgroup G).subgroupOf (centralizer (V₁ : Set G))) K := Or.inl ⟨e⟩
  let := hc.quotient_isQuasisimple hK
  exact terminal_contradiction_of_A5_context_knownSimple d hCv houtside hcounter
    (source_component_conclusion_of_context_knownSimple d hCv houtside hcounter
      hK hc (source_j2_component_unique d houtside hK e))

end CFSG.Quasithin.Chapter13.Section06.TerminalContradiction
