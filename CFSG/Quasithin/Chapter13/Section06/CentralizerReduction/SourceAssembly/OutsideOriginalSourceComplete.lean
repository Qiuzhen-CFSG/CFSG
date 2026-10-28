module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.SolvableOriginalSourceComplete
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableOriginalSourceComplete

/-!
# Both original outside-source cases

The solvable source is proved directly. For a nonsolvable moving outside
group, the actual elementary lift gives generation parameter two and the
genuine earlier5.2.3 theorem gives a Main-Theorem model. Consequently every
outside group centralizes the original Sylow omega-center in a surviving
catalogue counterexample.

Only the original earlier module clause and the genuine5.2.3 classifier
remain explicit. This is not the nonsingular-point centralizer conclusion.
Source: Aschbacher--Smith 13.2.7--8, pp.880--884.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside Section03.SourceCompletion
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- Original outside centralization with both local cases discharged on
the same Context, module and Sylow. -/
theorem original_outside_centralizes_omega_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G))) :
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  by_cases hs : Group.IsSolvable H
  · exact original_solvable_centralizes_omega_from_source d hmany hH hs
  · exact original_nonsolvable_centralizes_omega_from_modules d hmany hmodules h523 hno hH hs

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
