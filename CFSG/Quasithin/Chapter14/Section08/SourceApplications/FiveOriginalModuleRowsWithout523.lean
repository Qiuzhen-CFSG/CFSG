module
public import CFSG.Quasithin.Chapter14.Section08.SourceCases
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OriginalContextWithout523
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OriginalSylowModules

/-!
# Full alternating-five recognition from original Chapter12 module rows

The actual rows at the original Sylow construct the marked Context. The
same guarded family supplies every later module choice at its own Sylow.
The intrinsic outside and initial terminal proofs then give the full
Main-Theorem catalogue without the universal earlier5.2.3 theorem.
The original Chapter12 module family is the only remaining input.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Chapter13.Section06.CentralizerReduction.SourceAssembly
variable {G : Type*} [Group G] [Finite G]

/-- The complete original A₅ dispatcher branch, retaining only the
genuine Chapter12 module rows at every guarded Sylow. -/
theorem fiveRecognition_from_original_module_rows_without_source523
    (modules : ∀ S : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        Theorem1222ModulesAt KnownSimple.IsKnownSimple S) : FiveRecognition G := by
  intro T L hmany hmax hfive
  obtain ⟨a⟩ := hfive
  obtain ⟨V,V₁,V₂,V₃,_,⟨d⟩⟩ := exists_context_from_original_module_rows
    (hypothesis1331 hmax.1) a hmany (modules T hmany)
  exact original_context_model_without_source523 d hmany
    (fun S I _ => original_modules_at_every_sylow d hmany modules S I)

end CFSG.Quasithin.Chapter14.Section08.SourceCases
