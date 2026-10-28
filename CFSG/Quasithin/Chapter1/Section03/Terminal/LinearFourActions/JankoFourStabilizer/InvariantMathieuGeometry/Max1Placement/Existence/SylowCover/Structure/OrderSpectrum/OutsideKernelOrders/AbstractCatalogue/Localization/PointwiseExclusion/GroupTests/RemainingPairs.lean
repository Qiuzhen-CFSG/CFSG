module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.Interface
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Contracts
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.RemainingPairs.Equation25
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.RemainingPairs.Equation26
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.RemainingPairs.Equation27
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.RemainingPairs.Equation28
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.RemainingPairs.Equation29
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.RemainingPairs.Equation30
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.RemainingPairs.Equation31
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.RemainingPairs.Equation32

/-!
# The remaining eight conjugate-pair coordinate tests

Both multiplication orders are collected in the literal presentation.
Pairwise commutation and normal-form uniqueness force the selected coordinate
differences to vanish; these differences are the original equations 25–32.

The only inputs are full presentation cardinality and the common collected
conjugate identities. The latter must be supplied by the final coordinate-test
assembly. Source context: Aschbacher–Smith A.3.12(17), pp.47–48; see
RemainingPairs/source/README.md and the unchanged source/equations.json.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
open Janko4.LocalStructure.SylowNormalEights Presentation

/-- Actual commutation of the selected conjugates forces equations 25–32. -/
theorem remainingPairTests (hcard : Nat.card Carrier = 2^21)
    (hconj : CollectedConjugates) : ConjugateTestsBetween 25 33 := by
  intro b hc i hlo _
  have hi : i = 25 ∨ i = 26 ∨ i = 27 ∨ i = 28 ∨ i = 29 ∨ i = 30 ∨ i = 31 ∨ i = 32 := by
    omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact RemainingPairs.test25 hcard hconj b hc
  · exact RemainingPairs.test26 hcard hconj b hc
  · exact RemainingPairs.test27 hcard hconj b hc
  · exact RemainingPairs.test28 hcard hconj b hc
  · exact RemainingPairs.test29 hcard hconj b hc
  · exact RemainingPairs.test30 hcard hconj b hc
  · exact RemainingPairs.test31 hcard hconj b hc
  · exact RemainingPairs.test32 hcard hconj b hc

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
