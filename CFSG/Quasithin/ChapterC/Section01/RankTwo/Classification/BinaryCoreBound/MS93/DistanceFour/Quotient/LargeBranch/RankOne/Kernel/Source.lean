module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Kernel.CoverSource
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Source

/-!
# The source moving kernel and first core factor

The opposite midpoint core supplies an involution whose displacement meets
Z_alpha only inside U_alpha. Applying the central-cover exclusion to the
actual moving quotient proves its exact U_alpha kernel. The completed span
recognition then constructs FirstStep without an additional kernel premise.

All groups, projections and actions retain the original source marking.
Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.12)(3),(5) and its final paragraph, printed pp.910--912.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

namespace RankOne

/-- The canonical moving span has exactly the source U_alpha kernel. -/
theorem source_movingKernelControl
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) : MovingKernelControl source common := by
  intro s hs hspan q _hindex
  obtain ⟨m, hm, hdis⟩ := Kernel.source_displacement_separated common radius hb s hs hspan
  exact Kernel.moving_kernel_of_separated_displacement common radius
    s.middle s.first_distance q m hm hdis

end RankOne

/-- Both recognition and the exact moving kernel are supplied by the source geometry. -/
theorem source_firstStep
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) : FirstStep source common :=
  firstStep_of_source_recognition_and_movingKernel common radius hb
    (RankOne.source_movingKernelControl common radius hb)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
