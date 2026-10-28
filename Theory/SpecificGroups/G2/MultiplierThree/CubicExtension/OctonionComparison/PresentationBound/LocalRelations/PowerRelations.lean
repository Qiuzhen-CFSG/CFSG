module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.Contracts
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.WordCalculus
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.PowerRelations.Square
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.PowerRelations.SixthPower
public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalPresentation

/-!
# The two remaining max3 power relations in the source presentation

The first power base and the cube of the second base are conjugate to the
original involution by checked source-word calculations. This proves the two
literal relators required by `local_relations_of_remaining`; no local power
premise, ambient order bound, or permutation faithfulness is assumed.

Source: the six ATLAS G23G1-P1 equations and the literal G23G1-max3W1 words.
See `PowerRelations/source/README.md` for the replay and its measurements.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations
open Subgroup.CosetWordCertificate Replay

/-- Both fixed power identities hold on the actual max3 generators. -/
theorem remaining_power_relations : RemainingPowerRelations :=
  ⟨PowerRelations.localRelator_two_holds, PowerRelations.localRelator_four_holds⟩

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations
