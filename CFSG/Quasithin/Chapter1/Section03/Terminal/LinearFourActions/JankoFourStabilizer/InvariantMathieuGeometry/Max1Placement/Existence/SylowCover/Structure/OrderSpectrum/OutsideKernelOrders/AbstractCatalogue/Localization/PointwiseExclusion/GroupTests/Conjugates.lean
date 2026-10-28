module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.Interface
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.ConjugateData
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Conjugates.Conjugate00
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Conjugates.Conjugate01
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Conjugates.Conjugate02
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Conjugates.Conjugate03
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Conjugates.Conjugate05
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Conjugates.Conjugate06
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Conjugates.Conjugate07
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Conjugates.Conjugate08
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.AbstractCatalogue.Localization.PointwiseExclusion.GroupTests.Conjugates.Conjugate09

/-!
# Certified coordinates of the nine selected conjugates

Each candidate normal form is connected to the literal positive inverse word,
the ascending input word, and the final generator by bounded collection checks.
Soundness is inherited from the unchanged power-conjugate presentation. The
Boolean application below discharges the common conjugate-coordinate premise
of the three pair-test families; no cardinality assumption is needed here.

Source: Aschbacher–Smith A.3.12, pp.47–48 (the J₄ branch), and the original
SylowNormalEights presentation. See Conjugates/source/README.md.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
open PointwiseCalculation Symbolic

/-- All nine selected candidate normal forms have their asserted group values. -/
theorem collectedConjugates : CollectedConjugates := by
  intro i hi v
  simp only [selectedConjugate, List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ConjugateCertificates.conjugate00_value v
  · exact ConjugateCertificates.conjugate01_value v
  · exact ConjugateCertificates.conjugate02_value v
  · exact ConjugateCertificates.conjugate03_value v
  · exact ConjugateCertificates.conjugate05_value v
  · exact ConjugateCertificates.conjugate06_value v
  · exact ConjugateCertificates.conjugate07_value v
  · exact ConjugateCertificates.conjugate08_value v
  · exact ConjugateCertificates.conjugate09_value v

/-- Application to the actual inverse conjugates of the original Boolean word. -/
theorem selectedConjugate_coordinates (i : Fin 21) (hi : selectedConjugate i)
    (b : Boolean.Bits) :
    value (coordinates (conjugatePolynomials i)) (valuation b) =
      conjugateTest (boolValue b) (some i) :=
  value_selectedConjugate collectedConjugates i hi b

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.AbstractCatalogue.Localization.GroupTests
