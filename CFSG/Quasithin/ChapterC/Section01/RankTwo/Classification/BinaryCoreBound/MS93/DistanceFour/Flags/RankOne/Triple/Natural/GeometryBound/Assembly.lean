module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.Quotient
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Natural.GeometryBound.Symmetry

/-!
# The geometric order bound for the literal flag fixed quotient

Under the contrary triple hypothesis, the fixed quotient of V_beta by the
preimage of the residual fixed space on V_beta/Z_alpha has order at most four.
If its index exceeded four, the displacement argument would give both strict
midpoint displacement inequalities. Critical endpoint replacement and the
actual coset incidence then put the midpoint edge commutator in the local
center, contradicting the selected noncentral triple.

The assembly discharges both geometric premises of the incidence reduction.
It uses the source data, common geometry, b = 4 and the earlier distance-four
facts; no natural flag section or later radius conclusion is an input.
Recognition of the resulting quotient action remains a separate step.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), the geometric argument for (4.6.8), claim (1), printed p.905.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The literal residual fixed quotient in MS93 (4.6.8), claim (1), has
order at most four in the binary case. Both displacement cases and the
symmetry contradiction are supplied by the source geometry. -/
theorem flagFixedPreimage_relIndex_le_four
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4)
    (early : EarlyFacts R geometry) (i : Bool)
    (hkernel : flagKernel source i = Q R (beta R))
    (hbad : ¬ ⁅⁅V R (beta R), flagResidual source i⁆, V R (alpha R)⁆ ≤
      (center (stabilizer R (alpha R))).map (stabilizer R (alpha R)).subtype) :
    (flagFixedPreimage source i).relIndex (V R (beta R)) ≤ 4 :=
  flagFixedPreimage_relIndex_le_four_of_displacement_and_symmetry
    source geometry common hb i hbad
    (flagP905Displacement_of_fixedIndex_gt_four source geometry common hb early i hkernel hbad)
    (flagP905_symmetry source geometry common hb early i hkernel hbad)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
