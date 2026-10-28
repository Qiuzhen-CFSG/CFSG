module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseSetup
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.Symbolic
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.Boolean

/-!
# Independent word-calculation contracts for pointwise exclusion

The Boolean implication is already proved. These contracts separate its two
remaining connections to the literal presentation: deriving the selected
coordinate equations and realizing the resulting kernel pattern inside the
original eleven-word subgroup. Their producers can import this interface
without importing the final pointwise assembly.

Source: Aschbacher–Smith A.3.12, pp.47–48; the original presentation and
candidate-kernel words are retained unchanged.
-/

@[expose] public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
open Janko4.LocalStructure.SylowNormalEights Presentation
open PointwiseCalculation

/-- The thirty-three displayed coordinate equations, in the actual presentation. -/
def CoordinateTests : Prop :=
  ∀ b : Boolean.Bits, Symbolic.boolValue b ^ 2 = 1 →
    PairwiseConjugateCommutation (Symbolic.boolValue b) → Boolean.Tests b

/-- Interpretation of the kernel coordinate pattern in the eleven original words. -/
def KernelPatternMembership : Prop :=
  ∀ b : Boolean.Bits, Boolean.KernelPattern b → Symbolic.boolValue b ∈ abstractKernel

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization
