module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Assembly
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Noncentral.Transfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Early.Center.Placement

/-!
# The early source facts in the binary distance-four branch

The proved initial and edge calculations construct their source records. The
relative-normalizer midpoint argument supplies the moving-kernel transfer,
which forces derived noncentrality. The selected seed's fixed-quotient
calculation supplies edge placement and hence the radius-center equality.
Thus every early source clause follows from CommonFacts and b = 4.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.1)--(4.6.7), printed pp.900--904.
-/

public section
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}

/-- The complete early distance-four source package, including derived
noncentrality and the radius-center equality, with both local steps discharged. -/
theorem earlyFacts (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (hb : geometry.b R = 4) :
    EarlyFacts R geometry := by
  exact earlyFacts_of_local_steps source geometry common hb
    (fun initial edge => Early.moving_kernel_fixed_of_derived_central common hb initial edge)
    (fun initial edge => Early.edge_placement_of_noncentral_seed common hb initial edge)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour
