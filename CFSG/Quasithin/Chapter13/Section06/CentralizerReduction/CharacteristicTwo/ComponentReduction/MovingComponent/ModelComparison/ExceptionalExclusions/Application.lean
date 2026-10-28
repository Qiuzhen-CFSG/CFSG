module

public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison.ExceptionalExclusions
public import CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.CharacteristicTwo.ComponentReduction.MovingComponent.ModelComparison

/-!
# Applying the exceptional exclusions to the moving component

These applications discharge the exceptional comparison premise of the
published consumers on their literal component image. The independent
classical exclusions remain explicit for the model-comparison assembly
owner; triality is already discharged by `ModelComparison`.

Source: Aschbacher–Smith, moving-component paragraph of 13.6.6, p.927.
-/

public section
namespace CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
open Chapter1.Section02 InitialSieve A5Module
open Chapter15.Section03.Candidates.ComponentStructure

/-- The field-indexed case split now needs only the independent classical comparisons. -/
theorem rankOneAt_of_classical_exclusions {Q : Type*} [Group Q] [Finite Q]
    [IsSimpleGroup Q] [Group.IsPerfect Q] {m : ℕ}
    (hclassical : ClassicalExclusions Q) (hm : 1 < m)
    (hbinary : BinaryModelAt Q m) (hnormal : NonnormalCComponentModel Q) :
    RankOneAt Q m :=
  rankOneAt_of_exclusions hclassical (exceptional_exclusions Q) hm hbinary hnormal

universe u
variable {G : Type u} [Group G] [Finite G] {L V : Subgroup G}
  {s : Marking L V} {U : Subgroup G} {K : Subgroup (Gv (markedV s))} {m : ℕ}

/-- Discharge the exceptional premise on the actual simple perfect component image. -/
theorem source_comparison_of_classical_exclusions
    (hclassical : ∀ (Q : Type u) [Group Q] [Finite Q] [IsSimpleGroup Q]
      [Group.IsPerfect Q], ClassicalExclusions Q)
    (d : SourceInput s U K m) : Conclusion K m :=
  source_comparison_of_uniform_exclusions hclassical exceptional_exclusions d

end CFSG.Quasithin.Chapter13.Section06.CentralizerReduction.ComponentReduction.MovingComponent.ModelComparison
