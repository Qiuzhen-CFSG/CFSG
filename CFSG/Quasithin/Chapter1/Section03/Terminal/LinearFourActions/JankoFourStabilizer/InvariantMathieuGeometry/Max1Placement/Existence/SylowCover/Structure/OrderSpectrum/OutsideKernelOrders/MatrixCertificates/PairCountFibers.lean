module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.Candidates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.Coordinates
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.Counts
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.Plane
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.Sample
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeEight

/-!
# Pair-count fiber certificates in the literal matrix subgroups

The checked representative ranks and conjugation coverage give the complete
rank-16 partner counts, including identity, in candidate rows 5–8. The fibers
at counts 34, 66, 58, 58 generate the literal coordinate subgroups of orders
4, 4, 2, 8. Thus `pairCount_span_orders` discharges these four span-order
clauses of `RankCertificates` without any remaining numerical premise.
Source context: Aschbacher–Smith A.3.12, printed pp.47–48;
Kleidman–Wilson (1988), pp.484–510.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates

namespace PairCountFibers

/-- The full original-coordinate table counts every rank-16 partner in the
actual subgroup. The representative ranks and all orbit steps are proved. -/
theorem countsCorrect : CountsCorrect :=
  countsCorrect_of_representativeRanks representativeRanks6 representativeRanks8

/-- The selected count fiber generates exactly the certified coordinate subgroup. -/
theorem rankSpan_eq_spanSubgroup (r : Fin 4) :
    rankSpan (matrixFamily (row r)) (candidateTest (row r)) = spanSubgroup r :=
  rankSpan_eq_spanSubgroup_of_counts countsCorrect r

end PairCountFibers

/-- The four pair-count fiber spans have orders 4, 4, 2, 8 in rows 5–8. -/
theorem pairCount_span_orders (i : Fin 9) (hi : 5 ≤ i.val) :
    Nat.card (rankSpan (matrixFamily i) (candidateTest i)) = candidateSpanOrder i :=
  PairCountFibers.pairCount_span_orders_of_counts PairCountFibers.countsCorrect i hi

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates
