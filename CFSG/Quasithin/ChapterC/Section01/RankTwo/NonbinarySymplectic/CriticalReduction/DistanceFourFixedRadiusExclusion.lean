module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourOriginalKernelDerivedFixed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourLargeCoherentPaths
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# The general fixed-radius distance-four branch is impossible

The already constructed coherent second path has its endpoints in the
orbit of its own actual midpoint stabilizer. Its original selector supplies
the inverse orbit element, without any new selection or transitivity premise.
The proved original-Q0 derived-kernel contradiction therefore excludes the
fixed-radius branch on every original distance-four critical path.
Source: MS93 (3.10)(i) and the fixed-radius endgame of (5.12), pp.880–881,927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- No original distance-four critical path is in the fixed-radius branch.
Its existing coherent selector supplies the actual midpoint orbit internally. -/
theorem Input.replacement_distance_four_fixed_radius_false
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) : False := by
  obtain ⟨c,hc,g,hg,x,hx,u,w,hchoose,haw,huw,back,hfirst,hover,
    v,s,y,hy,hya,hys,hus,hvs,hn,next,hnext,hovernext⟩ :=
    h.replacement_distance_four_coherent_paths d path hb
  have hlen : back.walk.length=4 := back.length_eq_b.trans hb
  have hmid : next.walk.getVert 2=u := by
    have hh := hovernext 0 (by omega)
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hh
  have hyS : y⁻¹ ∈ stabilizer d.radical (next.walk.getVert 2) := by
    rw [hmid]
    exact (stabilizer d.radical u).inv_mem (Ltilde_le_stabilizer u hy)
  have hyv : act d.radical y⁻¹ v=a := by
    rw [←hya,←act_mul,mul_inv_cancel,act_one]
  exact h.replacement_distance_four_fixed_same_orbit_false d next hb y⁻¹ hyS hyv
    (radius_fixed_at d path.start_color next.start_color hfixed)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
