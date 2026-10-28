module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableParameterOriginalSource
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.SourceSolvabilityReduction

/-!
# Original5.2.3 after the unbounded nonsolvable source proof

The original elementary lift proves the actual generation parameter is two.
The genuine earlier5.2.3 theorem therefore places every nonsolvable moving
outside group in the full Main-Theorem catalogue. In a catalogue
counterexample, every nonsolvable outside group centralizes the original
Sylow omega-center; every outside group moving that center is solvable.

The original earlier module clause and5.2.3 classifier remain separate
inputs. The solvable outside branch and nonsingular-point centralizer are
not asserted here.
Source: Aschbacher--Smith 13.2.8(1), p.880, and5.2.3, p.649.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside Section03.SourceCompletion
open TerminalContradiction.Components.SuzukiIsolation
universe u
variable {G : Type u} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- The actual earlier classifier applies with its generation premise now
proved for every original nonsolvable outside mover. -/
theorem original_nonsolvable_model_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G))
    (hs : ¬ Group.IsSolvable H) : ClassificationModels.IsQTKEModel G := by
  have hn := (original_nonsolvable_parameter_from_modules d hmany hmodules hH hZ hs).2
  exact main_model_of_source523_omega_movement d h523 hH hZ (by omega)

/-- In a surviving catalogue counterexample, every original nonsolvable
outside group centralizes the whole Sylow omega-center. -/
theorem original_nonsolvable_centralizes_omega_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  by_contra hZ
  exact hno (original_nonsolvable_model_from_modules d hmany hmodules h523 hH hZ hs)

/-- Every remaining original outside mover is solvable. This discharges
the nonsolvable branch without adding a generation callback. -/
theorem original_outside_mover_solvable_from_modules
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (h523 : Source523.EarlierTheorem.{u} KnownSimple.IsKnownSimple)
    (hno : ¬ ClassificationModels.IsQTKEModel G)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    Group.IsSolvable H := by
  by_contra hs
  exact hno (original_nonsolvable_model_from_modules d hmany hmodules h523 hH hZ hs)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
