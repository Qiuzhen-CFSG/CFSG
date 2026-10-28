module

public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeData
public import Theory.SpecificGroups.Janko4.Model.LocalStructure.SylowNormalEights.MatrixRealization.WordEvaluation
public import CFSG.Quasithin.Chapter1.Section03.Terminal.LinearFourActions.JankoFourStabilizer.InvariantMathieuGeometry.Max1Placement.Existence.SylowCover.Structure.OrderSpectrum.OutsideKernelOrders.MatrixCertificates.PairCountFibers.RepresentativeEight.Pairs58
import Mathlib.Tactic.FinCases

/-!
# The 118 row-eight pair ranks

All representative ranks are calculated in the original ATLAS basis. Shared
word evaluations identify the actual candidate points. Each displacement
product has two checked row expansions and an identity pivot minor, proving
its rank. The import chain bounds simultaneous certificate compilation to
two pairs per module. No orbit completeness or counting premise is used.

Source context: Aschbacher–Smith A.3.12, pp.47–48; Kleidman–Wilson (1988),
pp.484–510. Matrix attribution is retained in Janko4.Model.Data. The witness
generator is RepresentativeEight/source/generate.py; its output is untrusted
until checked by Lean.
-/

public section
namespace CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers

/-- All 118 representative ranks, for the literal original-basis matrices. -/
theorem representativeRanks8 : RepresentativeRanks8 := by
  intro k
  fin_cases k
  · exact RepresentativeEight.Case0.rank
  · exact RepresentativeEight.Case1.rank
  · exact RepresentativeEight.Case2.rank
  · exact RepresentativeEight.Case3.rank
  · exact RepresentativeEight.Case4.rank
  · exact RepresentativeEight.Case5.rank
  · exact RepresentativeEight.Case6.rank
  · exact RepresentativeEight.Case7.rank
  · exact RepresentativeEight.Case8.rank
  · exact RepresentativeEight.Case9.rank
  · exact RepresentativeEight.Case10.rank
  · exact RepresentativeEight.Case11.rank
  · exact RepresentativeEight.Case12.rank
  · exact RepresentativeEight.Case13.rank
  · exact RepresentativeEight.Case14.rank
  · exact RepresentativeEight.Case15.rank
  · exact RepresentativeEight.Case16.rank
  · exact RepresentativeEight.Case17.rank
  · exact RepresentativeEight.Case18.rank
  · exact RepresentativeEight.Case19.rank
  · exact RepresentativeEight.Case20.rank
  · exact RepresentativeEight.Case21.rank
  · exact RepresentativeEight.Case22.rank
  · exact RepresentativeEight.Case23.rank
  · exact RepresentativeEight.Case24.rank
  · exact RepresentativeEight.Case25.rank
  · exact RepresentativeEight.Case26.rank
  · exact RepresentativeEight.Case27.rank
  · exact RepresentativeEight.Case28.rank
  · exact RepresentativeEight.Case29.rank
  · exact RepresentativeEight.Case30.rank
  · exact RepresentativeEight.Case31.rank
  · exact RepresentativeEight.Case32.rank
  · exact RepresentativeEight.Case33.rank
  · exact RepresentativeEight.Case34.rank
  · exact RepresentativeEight.Case35.rank
  · exact RepresentativeEight.Case36.rank
  · exact RepresentativeEight.Case37.rank
  · exact RepresentativeEight.Case38.rank
  · exact RepresentativeEight.Case39.rank
  · exact RepresentativeEight.Case40.rank
  · exact RepresentativeEight.Case41.rank
  · exact RepresentativeEight.Case42.rank
  · exact RepresentativeEight.Case43.rank
  · exact RepresentativeEight.Case44.rank
  · exact RepresentativeEight.Case45.rank
  · exact RepresentativeEight.Case46.rank
  · exact RepresentativeEight.Case47.rank
  · exact RepresentativeEight.Case48.rank
  · exact RepresentativeEight.Case49.rank
  · exact RepresentativeEight.Case50.rank
  · exact RepresentativeEight.Case51.rank
  · exact RepresentativeEight.Case52.rank
  · exact RepresentativeEight.Case53.rank
  · exact RepresentativeEight.Case54.rank
  · exact RepresentativeEight.Case55.rank
  · exact RepresentativeEight.Case56.rank
  · exact RepresentativeEight.Case57.rank
  · exact RepresentativeEight.Case58.rank
  · exact RepresentativeEight.Case59.rank
  · exact RepresentativeEight.Case60.rank
  · exact RepresentativeEight.Case61.rank
  · exact RepresentativeEight.Case62.rank
  · exact RepresentativeEight.Case63.rank
  · exact RepresentativeEight.Case64.rank
  · exact RepresentativeEight.Case65.rank
  · exact RepresentativeEight.Case66.rank
  · exact RepresentativeEight.Case67.rank
  · exact RepresentativeEight.Case68.rank
  · exact RepresentativeEight.Case69.rank
  · exact RepresentativeEight.Case70.rank
  · exact RepresentativeEight.Case71.rank
  · exact RepresentativeEight.Case72.rank
  · exact RepresentativeEight.Case73.rank
  · exact RepresentativeEight.Case74.rank
  · exact RepresentativeEight.Case75.rank
  · exact RepresentativeEight.Case76.rank
  · exact RepresentativeEight.Case77.rank
  · exact RepresentativeEight.Case78.rank
  · exact RepresentativeEight.Case79.rank
  · exact RepresentativeEight.Case80.rank
  · exact RepresentativeEight.Case81.rank
  · exact RepresentativeEight.Case82.rank
  · exact RepresentativeEight.Case83.rank
  · exact RepresentativeEight.Case84.rank
  · exact RepresentativeEight.Case85.rank
  · exact RepresentativeEight.Case86.rank
  · exact RepresentativeEight.Case87.rank
  · exact RepresentativeEight.Case88.rank
  · exact RepresentativeEight.Case89.rank
  · exact RepresentativeEight.Case90.rank
  · exact RepresentativeEight.Case91.rank
  · exact RepresentativeEight.Case92.rank
  · exact RepresentativeEight.Case93.rank
  · exact RepresentativeEight.Case94.rank
  · exact RepresentativeEight.Case95.rank
  · exact RepresentativeEight.Case96.rank
  · exact RepresentativeEight.Case97.rank
  · exact RepresentativeEight.Case98.rank
  · exact RepresentativeEight.Case99.rank
  · exact RepresentativeEight.Case100.rank
  · exact RepresentativeEight.Case101.rank
  · exact RepresentativeEight.Case102.rank
  · exact RepresentativeEight.Case103.rank
  · exact RepresentativeEight.Case104.rank
  · exact RepresentativeEight.Case105.rank
  · exact RepresentativeEight.Case106.rank
  · exact RepresentativeEight.Case107.rank
  · exact RepresentativeEight.Case108.rank
  · exact RepresentativeEight.Case109.rank
  · exact RepresentativeEight.Case110.rank
  · exact RepresentativeEight.Case111.rank
  · exact RepresentativeEight.Case112.rank
  · exact RepresentativeEight.Case113.rank
  · exact RepresentativeEight.Case114.rank
  · exact RepresentativeEight.Case115.rank
  · exact RepresentativeEight.Case116.rank
  · exact RepresentativeEight.Case117.rank

end CFSG.Quasithin.Chapter1.Terminal.LinearFourActions.JankoFourStabilizer.Max1Placement.SylowCover.OutsideKernelOrders.MatrixCertificates.PairCountFibers
