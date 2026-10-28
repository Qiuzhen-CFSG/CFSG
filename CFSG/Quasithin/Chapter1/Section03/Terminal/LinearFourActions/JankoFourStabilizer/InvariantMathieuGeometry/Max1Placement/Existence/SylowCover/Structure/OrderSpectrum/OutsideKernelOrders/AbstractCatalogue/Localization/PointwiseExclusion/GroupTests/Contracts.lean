module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.ConjugateData
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Interpretation

/-!
# Independent conjugate-pair equation families

The square coordinates are handled separately. The remaining equations divide
into three independent product calculations on the same nine selected conjugates.
These are explicit calculation contracts, not proved source conclusions.
Their producers may assume CollectedConjugates; final assembly must supply it.
Source: the equation-to-coordinate map in PointwiseExclusion/source/equations.json,
whose interpretation must be justified using the unchanged literal presentation.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
open PointwiseCalculation Symbolic

/-- A bounded family of the existing equations, from actual pairwise commutation. -/
def ConjugateTestsBetween (lower upper : Nat) : Prop :=
  ∀ b : Boolean.Bits, PairwiseConjugateCommutation (boolValue b) →
    ∀ i : Fin 33, lower ≤ i.val → i.val < upper → Boolean.equations b i = false

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
