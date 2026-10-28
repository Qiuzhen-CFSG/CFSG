module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalPresentation

/-!
# Remaining literal local relations

These two propositions specify the five still-unproved identities on the actual
max3 generators. They are proof obligations, not assertions about a permutation
image. The power identities can be proved independently while the mixed-word
argument takes them as explicit inputs; the owner must supply both in its final
assembly. All signed words remain those in `LocalPresentation`.

Source: the fixed seven GAP-discovered local words documented in
`PresentationBound/source/README.md`, to be lifted from ATLAS G23G1-P1.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations
open Subgroup.CosetWordCertificate

/-- The square relation at index two and sixth-power relation at index four. -/
def RemainingPowerRelations : Prop :=
  eval boundGenerator (localRelatorLetters 2) = 1 ∧
  eval boundGenerator (localRelatorLetters 4) = 1

/-- The three remaining mixed words, with every signed letter fixed upstream. -/
def RemainingMixedRelations : Prop :=
  eval boundGenerator (localRelatorLetters 3) = 1 ∧
  eval boundGenerator (localRelatorLetters 5) = 1 ∧
  eval boundGenerator (localRelatorLetters 6) = 1

end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations
