module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.Obstruction
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.DerivedFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Initial.Center.FailureOffender

/-!
# Radius-center containment in MS93 (4.6.1)

The radius center lies in every M-kernel at distance at most two. Its
literal central quotient is elementary abelian with the full stabilizer
conjugation action. Displacement passes from that quotient to the moving
central quotient, where residual-invariant commutator forms exclude a
projected offender whenever the radius-derived subgroup is residual-fixed.

Failure of the source center containment gives both the central-quotient
offender from the first paragraph on p.900 and the residual-fixed derived
bound from the simultaneous conjugate-escape argument on pp.900--901.
The binary obstruction contradicts their conjunction, proving Z(V_a) ≤ B_a
from the common local facts at critical distance four. Here V_a is the
radius-two group, distinct from the core [Q_a,Ltilde_a] in the main (4.6).

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.1), printed pp.900--901.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph

namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- MS93 (4.6.1) in the binary specialization: the center of the radius-two
group lies in B. Both geometric consequences of its failure are proved from
the common local facts, so no later initial-factorization fact is assumed. -/
theorem radius_center_le_B
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (a : Vertex R) (ha : color R a = false) :
    (center (V R a)).map (V R a).subtype ≤ B R a (geometry.Z_normal a) := by
  by_contra hfail
  exact not_radiusCenterOffender_of_derived_fixed common hb a ha
    (radius_derived_le_fixed_of_center_failure source geometry common hb a ha hfail)
    (radiusCenterOffender_of_center_failure common hb a ha hfail)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Early.Initial
