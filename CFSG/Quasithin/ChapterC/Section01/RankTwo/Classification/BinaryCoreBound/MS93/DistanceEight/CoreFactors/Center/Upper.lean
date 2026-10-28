module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Center.CommutatorRows
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.CoreFactors.Higher.Quotients.MovingLayer.ThirdBound

/-!
# The reverse core-center containment

The actual moving quotient has order at most 64 by the involution fixed-index
bound. The commutator rows have image of order 64, so their kernel is exactly
the intersection with the second hat. Its center calculation then places the
core center inside the original Z-layer.

Source: Meierfrankenfeld--Stellmacher (1993), (4.5), printed pp.895,899.
-/

public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement IsMulCommutative Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
open NormalizerTransfer PathCentrality Higher DistanceFour.Linear
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {geometry : Geometry R} {source : LocalSource L R}

private theorem first_centralizer_eq_second_of_index_bound (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (hindex : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).relIndex
      (core R (alpha R)) ≤ 64) :
    core R (alpha R) ⊓ centralizer
      (hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) =
    core R (alpha R) ⊓ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) := by
  let K := core R (alpha R)
  let A := hatV R (alpha R) (p.walk.getVert 6)
  let W := hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)
  let C := K ⊓ centralizer (A : Set (FreeAmalgam R))
  have hWC : K ⊓ W ≤ C := le_inf inf_le_left
    (inf_le_right.trans (le_centralizer_iff.mp
      (Quotients.SecondLayer.Recognition.denominator_centralizes_second earlier
        (Early.Orbit.SourceApplications.higherPath geometry p))))
  apply le_antisymm ?_ hWC
  have hmul := relIndex_mul_relIndex (K ⊓ W) C K hWC inf_le_left
  have hc := first_centralizer_relIndex_eq_sixtyFour common earlier p
  change C.relIndex K = 64 at hc
  rw [hc,inf_relIndex_left] at hmul
  let : Finite K := DistanceTwo.finite_core (alpha R)
  have hn : W.relIndex K ≠ 0 := index_ne_zero_of_finite
  exact relIndex_eq_one.mp (by change W.relIndex K ≤ 64 at hindex; omega :
    (K ⊓ W).relIndex C = 1)

private theorem core_center_le_Z_of_index_bound (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (hindex : (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).relIndex
      (core R (alpha R)) ≤ 64) :
    (center (core R (alpha R))).map (core R (alpha R)).subtype ≤ Z R (alpha R) := by
  have hD : (center (core R (alpha R))).map (core R (alpha R)).subtype ≤
      core R (alpha R) ⊓ centralizer
        (hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) := by
    apply le_inf (map_subtype_le _)
    exact (core_center_centralizes_second common earlier p).trans
      (centralizer_le (Quotients.SecondLayer.lower_le_second
        (Early.Orbit.SourceApplications.higherPath geometry p)))
  rw [first_centralizer_eq_second_of_index_bound common earlier p hindex] at hD
  exact (le_inf le_rfl (hD.trans inf_le_right)).trans
    (core_center_inf_second_le_Z common earlier p)
/-- The actual source involution estimate bounds the moving quotient of the core. -/
theorem core_second_relIndex_le_sixtyFour (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).relIndex
      (core R (alpha R)) ≤ 64 := by
  rw [core_eq_third_residual common earlier p]
  exact Quotients.MovingLayer.third_residual_relIndex_le_sixtyFour common earlier p

/-- The first-layer centralizer in the core is exactly its second-layer intersection. -/
theorem first_centralizer_eq_second (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    core R (alpha R) ⊓ centralizer
      (hatV R (alpha R) (p.walk.getVert 6) : Set (FreeAmalgam R)) =
    core R (alpha R) ⊓ hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8) :=
  first_centralizer_eq_second_of_index_bound common earlier p
    (core_second_relIndex_le_sixtyFour common earlier p)

/-- The reverse-center step uses the original source path and no model witness. -/
theorem core_center_le_Z (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R)) :
    (center (core R (alpha R))).map (core R (alpha R)).subtype ≤ Z R (alpha R) :=
  core_center_le_Z_of_index_bound common earlier p
    (core_second_relIndex_le_sixtyFour common earlier p)

variable [IsMulCommutative (H R (alpha R))]

/-- The literal row has the exact second-hat kernel. -/
theorem coreCommutatorRow_kernel (common : CommonFacts R source geometry)
    (earlier : Earlier R geometry) (p : Early.SourcePath R (alpha R))
    (s : MarkedDualSection source common
      (hatV R (alpha R) (p.walk.getVert 6)) (Z R (alpha R))) :
    (coreCommutatorRow common earlier p s).ker =
      (hatW R (alpha R) (p.walk.getVert 6) (p.walk.getVert 8)).subgroupOf
        (core R (alpha R)) := by
  ext x
  rw [coreCommutatorRow_mem_ker_iff]
  have he := congrArg (fun A : Subgroup (FreeAmalgam R) => (x : FreeAmalgam R) ∈ A)
    (first_centralizer_eq_second common earlier p)
  simpa only [mem_inf, x.property, true_and, mem_subgroupOf] using (iff_of_eq he)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.CoreFactors.Center
