module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRadiusDerived
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.ShiftedPaths
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# All critical images in the fixed-radius distance-four branch

A hypothetical large critical image has an actual two-edge forward shift.
The original path is then a compatible backward path for that shifted path.
Radius fixedness transports to its actual center, and the full-radius derived
argument bounds this original image by q. This excludes every large image,
without prescribing an endpoint orbit or assuming a forward extension.
Source: the fixed-radius case of MS93 (5.12)(2), printed p.926.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Fixedness at one original-group vertex forces both critical indices
to have field order for every original distance-four critical path. -/
theorem Input.replacement_distance_four_fixed_critical_indices
    {geometry : Geometry d.radical} (hb : geometry.b d.radical=4)
    {v a z : Vertex d.radical} (hv : color d.radical v=false)
    (hfixed : ⁅V d.radical v,Q d.radical v⁆ ≤ fixedCore d.radical v)
    (path : CriticalPath d.radical geometry a z) :
    (Q d.radical z).relIndex (Z d.radical a)=Nat.card F ∧
      (Q d.radical a).relIndex (Z d.radical z)=Nat.card F := by
  by_cases hs : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2
  · exact h.replacement_small_critical_indices_eq_field d path (by omega) hs
  let p : CriticalSegment geometry := ⟨a,z,path⟩
  obtain ⟨⟨c,w,next⟩,hfirst,hover,_⟩ :=
    h.replacement_large_critical_forward_path d p (by omega) (le_of_not_gt hs)
  have hc : c=path.walk.getVert 2 := hfirst
  have hmid : next.walk.getVert 2=z := by
    have hh := hover 2 (by omega)
    change next.walk.getVert 2=path.walk.getVert (2+2) at hh
    rw [show 2+2=path.walk.length by rw [path.length_eq_b,hb]] at hh
    simpa only [SimpleGraph.Walk.getVert_length] using hh
  let back : CriticalPath d.radical geometry a (next.walk.getVert 2) := {
    start_color := path.start_color
    walk := path.walk.copy rfl hmid.symm
    shortest := by rw [SimpleGraph.Walk.length_copy,hmid]; exact path.shortest
    critical := by simpa only [hmid] using path.critical }
  have hback : back.walk.getVert 2=c := by
    change (path.walk.copy rfl hmid.symm).getVert 2=c
    rw [SimpleGraph.Walk.getVert_copy]
    exact hc.symm
  have hf := radius_fixed_at d hv next.start_color hfixed
  have hi := h.replacement_distance_four_fixed_backward_indices d next hb back hback hf
  simpa only [hmid] using hi

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
