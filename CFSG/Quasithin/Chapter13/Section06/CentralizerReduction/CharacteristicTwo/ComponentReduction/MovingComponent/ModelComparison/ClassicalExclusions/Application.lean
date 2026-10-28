module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.ClassicalExclusions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison

/-!+# Applying the intrinsic classical exclusions to the marked component

The uniform classical comparison is instantiated on the actual component
image by the existing consumer, which proves its finite simple perfect
hypotheses. This discharges the classical premise in the moving-component
comparison. The separate exceptional exclusions remain explicit for their
source assembly owner; no new condition on the marked action is introduced.

Source: Aschbacher–Smith, proof of 13.6.6, printed p.927.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
open InitialSieve A5Module

universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G} {s : Marking L V}

/-- The marked source comparison now requires only the exceptional model exclusions. -/
theorem source_comparison_of_uniform_exceptional_exclusions
    (hexceptional : ∀ (Q : Type u) [Group Q] [Finite Q] [IsSimpleGroup Q]
      [Group.IsPerfect Q], ExceptionalExclusions Q)
    {T : Subgroup G} {K : Subgroup (Gv (markedV s))} {m : ℕ}
    (d : SourceInput s T K m) : Conclusion K m := by
  exact source_comparison_of_uniform_exclusions
    (fun Q _ _ _ _ => classical_exclusions Q) hexceptional d

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
