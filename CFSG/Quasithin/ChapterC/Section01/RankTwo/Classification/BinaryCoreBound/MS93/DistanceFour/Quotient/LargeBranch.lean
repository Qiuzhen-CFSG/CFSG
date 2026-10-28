module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Requirements
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Generation
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.Shift
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Source

/-!
# Assembly of the large branch of MS93 (4.6.12)

The completed algebra and geometry select a noncommuting second vertex,
separate the two factors, remove the extra Z_alpha from the source star
identity by residual commutator idempotence, and construct `OrbitFactors`.
The critical-shift API also realizes the selected vertex as a midpoint.

The theorem below is conditional on the two explicitly named source steps.
Their constructors are still required: `FirstStep` now has its full source span recognition; its separate
U_alpha-kernel identification remains explicit in
`firstStep_of_source_recognition_and_movingKernel`. `SecondStep` supplies
the reapplication and two-span identity. This module does not yet prove (4.6.12) from the source hypotheses.
Source: original Meierfrankenfeld--Stellmacher (1993), pp.910--912.
-/

public section

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  {common : CommonFacts R source geometry}

/-- Final assembly once both missing source constructions have been proved. -/
theorem orbitFactors_of_steps (radius : RadiusFacts R geometry)
    (first : FirstStep source common) (second : SecondStep source common)
    (s : CriticalSegment geometry) (hs : ¬ s.SmallIntersection) :
    Nonempty (OrbitFactors source common s.middle) := by
  obtain ⟨⟨f⟩, _hindex⟩ := first s hs
  obtain ⟨rho, hnu, hadj, hcomm⟩ := f.exists_second_seed radius
  obtain ⟨⟨g⟩, hstar⟩ := second first s hs f rho hnu hadj hcomm
  exact f.orbitFactors_of_star_generation g radius hcomm hstar

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch
