module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.OrbitTable
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PC15Rank
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W15_17
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W16
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W18
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W19
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W20
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W14_15
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W17
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W16_17
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W17_18
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W9_15
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W14
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W14_16
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W14_18
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.DisplacementFibers.Ranks.W11_13
import Mathlib.Tactic.FinCases

/-!
# Ranks of all orbit representatives

These are the sixteen literal original-basis words consumed by OrbitTable.
The identity has rank zero; PC15 reuses the published certificate; every
remaining rank comes from checked row expansions and a pivot minor.
Source context: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988),
pp.484–510. The ATLAS attribution is retained in Janko4.Model.Data.
-/

public section
open Janko4 Janko4.LocalStructure.SylowNormalEights
open Janko4.LocalStructure.SylowNormalEights.Presentation.Profiles
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.DisplacementFibers
attribute [local irreducible] modelGroup matrixA matrixB

/-- All representative rank premises of the complete orbit transport are discharged. -/
theorem representative_ranks (r : Fin 16) :
    displacementRank (realization (wordValue (representativeWords r))) =
      representativeRank r := by
  fin_cases r
  · simp [representativeWords, representativeRank, displacementRank]
  · exact rank_word_15_17
  · exact rank_word_16
  · exact rank_word_18
  · exact rank_word_19
  · exact rank_word_20
  · change displacementRank (realization (wordValue [15])) = 50
    simpa only [wordValue_cons, wordValue_nil, mul_one, realization_generator] using
      displacementRank_pc15
  · exact rank_word_14_15
  · exact rank_word_17
  · exact rank_word_16_17
  · exact rank_word_17_18
  · exact rank_word_9_15
  · exact rank_word_14
  · exact rank_word_14_16
  · exact rank_word_14_18
  · exact rank_word_11_13

/-- Complete displacement ranks on all five entire coordinate sets. -/
theorem displacementRank_point (i : Fin 5) (n : Fin (candidateOrder (row i))) :
    displacementRank (point (row i) n) = rankLabel i n.val :=
  displacementRank_point_of_representatives representative_ranks i n

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.DisplacementFibers
