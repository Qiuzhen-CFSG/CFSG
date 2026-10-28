module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition

/-!
# Source recognition in the first-factor assembly

The full orbit-span recognition supplies the literal marked quotient and
starred index 64. Only the independent identification of the moving subgroup's
intersection with Z_alpha as U_alpha remains in this first-step constructor.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12), printed pp.910--912.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- The completed source recognition discharges the quotient and dimension
input of FirstStep. Its exact U_alpha-kernel input remains independently owned. -/
theorem firstStep_of_source_recognition_and_movingKernel
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (hker : RankOne.MovingKernelControl source common) :
    FirstStep source common :=
  firstStep_of_recognition_and_movingKernel source common radius hb
    (RankOne.source_spanRecognition common radius hb) hker

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
