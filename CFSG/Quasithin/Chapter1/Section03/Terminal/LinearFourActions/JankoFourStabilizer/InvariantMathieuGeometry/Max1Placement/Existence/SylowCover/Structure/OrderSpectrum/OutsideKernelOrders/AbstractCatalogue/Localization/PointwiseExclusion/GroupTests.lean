module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.Interface
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.SquareTests
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Contracts
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Conjugates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.IdentityPairs
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.ZeroPairs
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.RemainingPairs

/-!
# Assembly of the literal pointwise coordinate tests

The twelve square equations follow from the actual ascending word and full
presentation order. The nine certified inverse conjugates supply the common
premise of the three conjugate-pair families, proving the other twenty-one
equations. Normal-form uniqueness turns the actual group equalities into the
required Boolean equations. The final theorem needs only the presentation
cardinality hypothesis and supplies CoordinateTests to the pointwise exclusion
assembly. No Boolean classification is reproved in this module.

Source: Aschbacher–Smith A.3.12, pp.47–48; the literal power-conjugate presentation
and PointwiseExclusion/source/equations.json. See GroupTests/source/README.md for
checked calculations, assembly contracts, and performance measurements.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
open Janko4.LocalStructure.SylowNormalEights Presentation
open PointwiseCalculation GroupTests

/-- Assemble the square equations with the three conjugate-pair families. -/
theorem coordinateTests_of_conjugateFamilies
    (hcard : Nat.card Carrier = 2^21)
    (hidentity : ConjugateTestsBetween 12 18)
    (hzero : ConjugateTestsBetween 18 25)
    (hremaining : ConjugateTestsBetween 25 33) : CoordinateTests := by
  intro b hs hc i
  by_cases h12 : i.val < 12
  · exact square_tests hcard b hs i h12
  by_cases h18 : i.val < 18
  · exact hidentity b hc i (by omega) h18
  by_cases h25 : i.val < 25
  · exact hzero b hc i (by omega) h25
  exact hremaining b hc i (by omega) i.isLt

/-- All thirty-three equations follow from square-one and actual pairwise
conjugate commutation, under the exact presentation cardinality hypothesis.
This discharges the CoordinateTests input of pointwiseExclusion_of_coordinate_tests. -/
theorem coordinateTests_of_card (hcard : Nat.card Carrier = 2^21) : CoordinateTests :=
  coordinateTests_of_conjugateFamilies hcard
    (identityPairTests hcard collectedConjugates)
    (zeroPairTests hcard collectedConjugates)
    (remainingPairTests hcard collectedConjugates)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
