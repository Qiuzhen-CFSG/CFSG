module
public import CFSG.Quasithin.Chapter14.Section08.SourceApplications.FiveOriginalSource
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.OriginalSylowModules

/-!
# Alternating-five recognition from actual Chapter12 module rows

The uniform original A5 quotient marks supply the quasisimple and model
premises of the earlier chosen-module row adapter. Hence the actual
Chapter12 module rows at each guarded Sylow construct the initial Context
and every later module rechoice. The proved original source argument then
reaches the full Main-Theorem catalogue.

Only the genuine Chapter12 module theorem and earlier5.2.3 classifier remain
explicit; no separate A5 module-classification or local-source callback is
required. Source: Aschbacher--Smith12.2.2(3d),13.3.2(3),13.6.1.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section08.SourceCases
open Chapter12.Section02 Chapter14.Section03.FaithfulSource
open Chapter13.Section06.CentralizerReduction.SourceAssembly
open Chapter13.Section06.TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]

/-- Actual Chapter12 module rows and the genuine earlier5.2.3 theorem
supply the complete A5 dispatcher branch. -/
theorem fiveRecognition_from_original_module_rows
    (modules : ∀ S : Sylow 2 G,
      1 < (maximalTwoLocalOvergroups (S : Subgroup G)).ncard →
        Theorem1222ModulesAt KnownSimple.IsKnownSimple S)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple) : FiveRecognition G := by
  intro T L hmany hmax hfive
  obtain ⟨a⟩ := hfive
  obtain ⟨V,V₁,V₂,V₃,_,⟨d⟩⟩ := exists_context_from_original_module_rows
    (hypothesis1331 hmax.1) a hmany (modules T hmany)
  exact original_context_model_from_modules d hmany
    (fun S I _ => original_modules_at_every_sylow d hmany modules S I) h523

end CFSG.Quasithin.Chapter14.Section08.SourceCases
