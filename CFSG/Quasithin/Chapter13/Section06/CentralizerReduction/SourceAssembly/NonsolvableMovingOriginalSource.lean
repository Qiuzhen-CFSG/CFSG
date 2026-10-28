module
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly.NonsolvableParameterOriginalSource
public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.OriginalMovingResidualExclusion

/-!
# Original nonsolvable outside groups centralize the omega-center

The earlier original module clause supplies the actual residual Context.
The genuine nonsolvable source construction supplies n(H)=2. The direct
normalized and cubic source obstructions then exclude omega-movement.
Neither the earlier 5.2.3 classifier nor an ambient catalogue exclusion
is an input. The solvable branch remains a separate argument.
-/

public section
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
open Section05.A5Source Section02.A5Outside Section02.A5Outside.OriginalCentralization
open Section03.SourceCompletion
variable {G : Type*} [Group G] [Finite G]
  {T : Sylow 2 G} {L V V₁ V₂ V₃ H : Subgroup G}

/-- The actual nonsolvable outside subgroup centralizes the entire original
omega-center, using only the earlier original module clause. -/
theorem original_nonsolvable_centralizes_omega_without_source523
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hs : ¬ Group.IsSolvable H) :
    H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G) := by
  by_contra hZ
  obtain ⟨W,W₁,W₂,W₃,_,⟨e⟩⟩ :=
    original_nonsolvable_context_from_modules d hmany hmodules hH hZ hs
  have hn := (original_nonsolvable_parameter_from_modules d hmany hmodules hH hZ hs).2
  have hm := (original_nonsolvable_structure_from_source d hmany hH hZ hs).2.2.1
  exact original_moving_residual_context_impossible d e hmany hH (by omega) hm hZ

/-- Consequently every original outside mover is solvable, without an
earlier classification premise or a catalogue-counterexample assumption. -/
theorem original_outside_mover_solvable_without_source523
    (d : Context T L V V₁ V₂ V₃)
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hmodules : OriginalAlternatingFiveModules1332At T L)
    (hH : H ∈ Chapter3.HStar (T : Subgroup G) (normalizer (L : Set G)))
    (hZ : ¬ H ≤ centralizer (omegaOneCenterAmbient (T : Subgroup G) : Set G)) :
    Group.IsSolvable H := by
  by_contra hs
  exact hZ (original_nonsolvable_centralizes_omega_without_source523 d hmany hmodules hH hs)

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.SourceAssembly
