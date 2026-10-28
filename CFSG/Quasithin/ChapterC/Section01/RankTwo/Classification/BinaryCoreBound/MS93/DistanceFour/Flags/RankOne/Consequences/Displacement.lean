module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Reduction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Selection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Displacement.Cardinalities

/-!
# The local displacement step of MS93 (4.6.9)

A noncentral critical path retains the genuine critical endpoint and both
midpoint distances. The marked natural action gives displacement index four
and trivial intersection with the intrinsic vertex center. The index exhausts
the edge quotient, giving V_alpha joined with Q_c equal to Q_beta and hence
the local covering. Central disjointness puts the literal quotient centralizer
Bzero in Q_c; the critical endpoint and the marked simple quotient then give
Bzero = B_alpha.

The theorem assembles these deductions from the supplied early facts and
FlagControl, discharging the path and displacement-calculation premises.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.9), printed p.908.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The first local displacement calculation of MS93 (4.6.9), including
the genuine critical-path covering and the literal quotient centralizer. -/
theorem localDisplacement_and_Bzero [Finite M] (source : LocalSource L R)
    (geometry : Geometry R) (common : CommonFacts R source geometry)
    (hb : geometry.b R = 4) (early : EarlyFacts R geometry)
    (control : FlagControl source) :
    LocalDisplacement R geometry ∧
      Bzero geometry (alpha R) = B R (alpha R) (geometry.Z_normal (alpha R)) := by
  obtain ⟨p⟩ := exists_noncentralCriticalPath source geometry common hb early control
  obtain ⟨_, hdisjoint, _, hindex⟩ :=
    displacement_cardinalities source geometry common hb early control p.middle
      p.first_distance p.edge p.noncentral
  exact localDisplacement_and_Bzero_of_calculation source geometry common early p
    hindex hdisjoint

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
