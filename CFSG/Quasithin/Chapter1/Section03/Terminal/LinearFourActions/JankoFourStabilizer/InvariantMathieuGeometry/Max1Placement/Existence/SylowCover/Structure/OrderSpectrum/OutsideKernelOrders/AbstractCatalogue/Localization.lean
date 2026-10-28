module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Setup
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseSetup
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.LowerBound
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion

/-!
# Assembly of the outside-kernel subgroup interval

The lower bound is proved by checked normal-closure calculations, with no
cardinal or elementarity premise. The upper bound follows from an elementwise
exclusion for involutions whose generator conjugates commute pairwise.
`intervalLocalization_of_pointwise` consumes that exact input;
`intervalLocalization_of_card` discharges it using the proved coordinate tests
and literal kernel membership under the full presentation cardinality hypothesis.
No subgroup catalogue or matrix realization is assumed here.

Source context: Aschbacher–Smith A.3.12, pp.47–48; see the source notes in
`Localization/source/README.md` for the literal conventions and finite checks.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue

/-- Complete interval assembly from the independent elementwise exclusion. -/
theorem intervalLocalization_of_pointwise (hp : Localization.PointwiseExclusion) :
    IntervalLocalization := by
  intro A hn he hout
  have henv := Localization.envelope_bound_of_pointwise hp A hn he hout
  exact ⟨Localization.core_le_of_normal_in_envelope A hn henv hout, henv⟩

/-- Every normal elementary two-subgroup outside the original eleven-word kernel
lies between the literal core and envelope. The cardinality hypothesis is used
only by the pointwise exclusion to distinguish ascending normal forms. -/
theorem intervalLocalization_of_card
    (hcard : Nat.card Janko4.LocalStructure.SylowNormalEights.Presentation.Carrier = 2 ^ 21) :
    IntervalLocalization :=
  intervalLocalization_of_pointwise (Localization.pointwiseExclusion_of_card hcard)

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue
