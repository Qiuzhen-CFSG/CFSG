module
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeData
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.Sample
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left01Part0
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left01Part1
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left01Part2
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left01Part3
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left02Part0
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left02Part1
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left02Part2
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left04Part0
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left04Part1
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left05Part0
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left05Part1
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left08Part0
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left10Part0
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left12Part0
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left16Part0
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left24Part0
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeSix.Left32Part0
import Mathlib.Tactic.FinCases

/-!
# All 51 row-six representative ranks

Each entry is a checked displacement-product rank in the literal ATLAS model.
Shared original-basis word evaluations feed row-span and pivot-minor certificates.
Entry 14 reuses the previously checked sample. This discharges exactly
`RepresentativeRanks6`; the parent separately owns orbit coverage and counting.
Source context: Aschbacher–Smith A.3.12, printed pp.47–48;
Kleidman–Wilson (1988), pp.484–510. ATLAS attribution is in Janko4.Model.Data.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers

attribute [local irreducible] Janko4.modelGroup Janko4.matrixA Janko4.matrixB

/-- Every row-six representative premise of the pair-count reduction is proved. -/
theorem representativeRanks6 : RepresentativeRanks6 := by
  intro k
  fin_cases k
  · exact RepresentativeSix.rank0
  · exact RepresentativeSix.rank1
  · exact RepresentativeSix.rank2
  · exact RepresentativeSix.rank3
  · exact RepresentativeSix.rank4
  · exact RepresentativeSix.rank5
  · exact RepresentativeSix.rank6
  · exact RepresentativeSix.rank7
  · exact RepresentativeSix.rank8
  · exact RepresentativeSix.rank9
  · exact RepresentativeSix.rank10
  · exact RepresentativeSix.rank11
  · exact RepresentativeSix.rank12
  · exact RepresentativeSix.rank13
  · exact representativeRanks6_sample
  · exact RepresentativeSix.rank15
  · exact RepresentativeSix.rank16
  · exact RepresentativeSix.rank17
  · exact RepresentativeSix.rank18
  · exact RepresentativeSix.rank19
  · exact RepresentativeSix.rank20
  · exact RepresentativeSix.rank21
  · exact RepresentativeSix.rank22
  · exact RepresentativeSix.rank23
  · exact RepresentativeSix.rank24
  · exact RepresentativeSix.rank25
  · exact RepresentativeSix.rank26
  · exact RepresentativeSix.rank27
  · exact RepresentativeSix.rank28
  · exact RepresentativeSix.rank29
  · exact RepresentativeSix.rank30
  · exact RepresentativeSix.rank31
  · exact RepresentativeSix.rank32
  · exact RepresentativeSix.rank33
  · exact RepresentativeSix.rank34
  · exact RepresentativeSix.rank35
  · exact RepresentativeSix.rank36
  · exact RepresentativeSix.rank37
  · exact RepresentativeSix.rank38
  · exact RepresentativeSix.rank39
  · exact RepresentativeSix.rank40
  · exact RepresentativeSix.rank41
  · exact RepresentativeSix.rank42
  · exact RepresentativeSix.rank43
  · exact RepresentativeSix.rank44
  · exact RepresentativeSix.rank45
  · exact RepresentativeSix.rank46
  · exact RepresentativeSix.rank47
  · exact RepresentativeSix.rank48
  · exact RepresentativeSix.rank49
  · exact RepresentativeSix.rank50

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
