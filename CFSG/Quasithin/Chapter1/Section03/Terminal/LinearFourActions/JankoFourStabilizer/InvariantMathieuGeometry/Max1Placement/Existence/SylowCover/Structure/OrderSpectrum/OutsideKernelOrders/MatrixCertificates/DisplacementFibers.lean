module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.Coordinates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Span
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.RepresentativeRanks

/-!
# Orders of the five complete displacement-fiber spans

Checked conjugacy trees cover every coordinate of the actual subgroups.
The sixteen representative words have kernel-checked ranks in the original
ATLAS basis. Every selected fiber is supported on its displayed PC subgroup,
and checked products of fiber elements recover all the subgroup's generators.
Unique PC normal forms therefore give the exact orders 8, 16, 32, 64, and 32.

This supplies rows 0–4 of the parent's RankCertificates, with no extra rank,
coverage, realization, or order premise. Source context: Aschbacher–Smith
A.3.12, printed pp.47–48; Kleidman–Wilson (1988), pp.484–510.
ATLAS matrix attribution is preserved in Janko4.Model.Data.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates

/-- Exact generated subgroup orders for the five entire displacement fibers. -/
theorem displacement_span_orders (i : Fin 9) (hi : i.val < 5) :
    Nat.card (rankSpan (matrixFamily i) (candidateTest i)) = candidateSpanOrder i :=
  DisplacementFibers.span_order_of_table DisplacementFibers.displacementRank_point
    ⟨i.val, hi⟩

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates
