module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFixedComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourLargeCoherentPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedUnequalComparison

/-!
# Actual compared paths in the fixed-radius branch

The unconditional coherent-path producer supplies both original selectors
and both literal backward paths. Radius fixedness then proves the comparison
on precisely those witnesses. Neither a prescribed first endpoint orbit nor
a movement bound, mover equality, or strict-neighbor alternative is needed.
Source: the comparison (5.12)(1) in the fixed-radius case, printed pp.925–926.
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

/-- The original fixed-radius branch supplies two actual compared backward
paths, retaining the same two source markings and all overlap vertices. -/
theorem Input.replacement_distance_four_fixed_compared_paths
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    ∃ c, Adjacent d.radical c (path.walk.getVert 1) ∧
      distanceFourComparedPaths path c (path.walk.getVert 1) := by
  obtain ⟨c,hc,g,hg,x,hx,u,w,hchoose,haw,huw,back,hfirst,hover,
    v,s,y,hy,hya,hys,hus,hvs,hn,next,hnext,hovernext⟩ :=
    h.replacement_distance_four_coherent_paths d path hb
  have hl := path.length_eq_b
  have hmid : back.walk.getVert 2=a := by
    have hh := hover 0 (by omega)
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hh
  have hcompare := h.replacement_distance_four_fixed_comparison d path hb back hmid
    hus hvs y (Ltilde_le_stabilizer u hy) hya hfixed
  exact ⟨c,hc,g,hg,x,hx,u,w,hchoose,haw,huw,back,hfirst,hover,
    v,s,y,hy,hya,hys,hus,hvs,hn,hcompare,next,hnext,hovernext⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
