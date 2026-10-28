module

public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Model
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.Action
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.SubgroupActions.Left
public import Theory.Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FourteenTraceSeparation.FiveCorner.Presentation.Coordinates.Coefficients.SubgroupActions.Right

/-!
# The two cached subgroup actions are the original word actions

Kernel-checked compositions first certify the repeated segments of the two
subgroup words, then compare their full compositions to the unchanged left
and right tables on every one of the 24192 points. The normalization proof
restores the original letters, and `fastWalk_eq` restores the original walker.
Thus this discharges exactly the subgroup-action premise of
`OrbitData.coefficientCertificate_of_checks`, without a geometry hypothesis.

Source: Presentation/source/discovery/p-generator-words.json and
coset-action.json; certificate construction: SubgroupActions/source/README.md.
-/

public section
namespace Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients

/-- Both cached tables evaluate the literal, unchanged subgroup words. -/
theorem subgroupActionsCorrect : SubgroupActionsCorrect := by
  apply subgroupActionsCorrect_of_fast
  · intro x
    apply Fin.ext
    change treeLookup leftTree x.val % 24192 = (fastWalk leftWord x).val
    rw [SubgroupActionCertificate.left_correct_normalized x,
      SubgroupActionCertificate.fastWalk_normalize]
  · intro x
    apply Fin.ext
    change treeLookup rightTree x.val % 24192 = (fastWalk rightWord x).val
    rw [SubgroupActionCertificate.right_correct_normalized x,
      SubgroupActionCertificate.fastWalk_normalize]

end Representation.JankoTwo.SmallBinaryDegrees.AbsoluteWindow.FiveCorner.Presentation.OrbitData.Coefficients
