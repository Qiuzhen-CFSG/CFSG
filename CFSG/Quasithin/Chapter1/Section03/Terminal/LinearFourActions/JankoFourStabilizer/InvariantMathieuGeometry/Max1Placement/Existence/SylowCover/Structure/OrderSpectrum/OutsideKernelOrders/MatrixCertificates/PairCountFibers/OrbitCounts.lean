module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.Counts
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.Plane
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Tables6
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.OrbitCounts.Tables8

/-!
# Complete pair counts from the literal representative ranks

Checked PC conjugation maps and finite trees cover every binary plane. Binary
basis changes preserve pair rank, and dependent pairs have rank zero. The full
coordinate counts, including identity, then give the four original count tables;
rows 5 and 7 use the literal even-coordinate inclusions. The only hypotheses
are the separately produced representative ranks in rows 6 and 8.
Source: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988), pp.484–510.
-/

public section
open Janko4
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
attribute [local irreducible] modelGroup matrixA matrixB pairRank point

/-- Complete original-coordinate counts, conditional only on the two lists of
literal representative ranks. Every action, plane route and count is checked. -/
theorem countsCorrect_of_representativeRanks (h6 : RepresentativeRanks6)
    (h8 : RepresentativeRanks8) : CountsCorrect := by
  intro r
  fin_cases r
  · intro n
    let ranks : Fin 64 → Fin 64 → ℕ := fun a b =>
      orbitRanks6 ⟨2*a.val, by omega⟩ ⟨2*b.val, by omega⟩
    have hr (a b : Fin 64) : pairRank (point 5 a) (point 5 b) = ranks a b := by
      exact (pairRank_five_six a b).trans (pairRank_eq_orbitRanks6 h6 _ _)
    exact (pairRankCount_eq_filter 5 ranks hr n 16).trans (orbitCount5 n)
  · intro n
    exact (pairRankCount_eq_filter 6 orbitRanks6 (pairRank_eq_orbitRanks6 h6) n 16).trans
      (orbitCount6 n)
  · intro n
    let ranks : Fin 128 → Fin 128 → ℕ := fun a b =>
      orbitRanks8 ⟨2*a.val, by omega⟩ ⟨2*b.val, by omega⟩
    have hr (a b : Fin 128) : pairRank (point 7 a) (point 7 b) = ranks a b := by
      exact (pairRank_seven_eight a b).trans (pairRank_eq_orbitRanks8 h8 _ _)
    exact (pairRankCount_eq_filter 7 ranks hr n 16).trans (orbitCount7 n)
  · intro n
    exact (pairRankCount_eq_filter 8 orbitRanks8 (pairRank_eq_orbitRanks8 h8) n 16).trans
      (orbitCount8 n)
end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
