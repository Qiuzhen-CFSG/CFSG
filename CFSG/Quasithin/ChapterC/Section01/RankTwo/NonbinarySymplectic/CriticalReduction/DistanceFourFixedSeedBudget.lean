module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedSeedExclusion
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPointFixedBudget
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans

/-!
# The original first moving seed has exactly field-sized B-index

Reverse, extend and reverse the actual path to make it the literal backward
path in the proved strict-mover comparison. Its first edge is unchanged.
The prescribed strict-branch contradiction therefore removes the extra mover
equality and own-index assumptions. The original path lower bound gives
exactly q, with no transitivity assumption on arbitrary two-step paths.
Source: MS93 (5.12)(3), printed p.927.
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

private def fixed_seed_reverse {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4) :
    CriticalPath d.radical geometry z a where
  start_color := path.end_color
  walk := path.walk.reverse
  shortest := by rw [SimpleGraph.Walk.length_reverse,path.shortest,SimpleGraph.dist_comm]
  critical := critical_reverse d.radical geometry
    (MSCentralOrbit.edgeCentralizerCondition d.radical (h.replacement_two_group d)
      (h.replacement_core_le d) (h.replacement_omegaOrbit_centralizer d))
    a path.start_color
    (by rw [geometry.distance_constant a path.start_color]; change 0 < geometry.b d.radical; omega)
    z path.end_color path.critical

/-- The exact original first moving seed budget, without mover premises. -/
theorem Input.replacement_distance_four_fixed_path_seed_index
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2))=Nat.card F := by
  apply le_antisymm ?_ (h.replacement_path_moving_index_ge_field d path (by omega))
  by_contra! hmove
  let rev := fixed_seed_reverse h d path hb
  have hlen : path.walk.length=4 := path.length_eq_b.trans hb
  have hrlen : rev.walk.length=4 := by
    change path.walk.reverse.length=4
    rwa [SimpleGraph.Walk.length_reverse]
  obtain ⟨u,ext,hover⟩ := h.replacement_critical_backward_extension d rev (by omega)
  have he : rev.walk.getVert (rev.walk.length-2)=path.walk.getVert 2 := by
    change path.walk.reverse.getVert (path.walk.reverse.length-2)=_
    rw [SimpleGraph.Walk.length_reverse,SimpleGraph.Walk.getVert_reverse,hlen]
  have hextmid : ext.walk.getVert 2=z := by
    have hh := hover 0 (by omega)
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hh
  let revext := fixed_seed_reverse h d ext hb
  let outer : CriticalPath d.radical geometry (path.walk.getVert 2) u := {
    start_color := by simpa only [he] using revext.start_color
    walk := revext.walk.copy he rfl
    shortest := by
      rw [SimpleGraph.Walk.length_copy]
      exact revext.shortest.trans (congrArg
        (fun t => (cosetGraph d.radical).dist t u) he)
    critical := by simpa only [he] using revext.critical }
  have homid : outer.walk.getVert 2=z := by
    change (ext.walk.reverse.copy he rfl).getVert 2=z
    rw [SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_reverse,
      ext.length_eq_b,hb]
    exact hextmid
  let back : CriticalPath d.radical geometry a (outer.walk.getVert 2) := {
    start_color := path.start_color
    walk := path.walk.copy rfl homid.symm
    shortest := by rw [SimpleGraph.Walk.length_copy,homid]; exact path.shortest
    critical := by simpa only [homid] using path.critical }
  have hback (i : ℕ) : back.walk.getVert i=path.walk.getVert i := by
    change (path.walk.copy rfl homid.symm).getVert i=_
    rw [SimpleGraph.Walk.getVert_copy]
  have hfixede := radius_fixed_at d path.start_color outer.start_color hfixed
  obtain ⟨hJ,hown⟩ := h.replacement_distance_four_strict_fixed_seed_mover d outer hb back
    (hback 2) hfixede hmove
  have hJ' := hJ
  have hown' := hown
  simp only [hback] at hJ' hown'
  exact h.replacement_distance_four_prescribed_strict_seed_false d path hb hfixed hmove hJ' hown'

/-- The original reciprocal seed also has exactly field-sized index. -/
theorem Input.replacement_distance_four_fixed_path_reciprocal_seed_index
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical a)=Nat.card F := by
  have hlen : path.walk.length=4 := path.length_eq_b.trans hb
  obtain ⟨u,ext,hover⟩ := h.replacement_critical_backward_extension d path (by omega)
  have he : path.walk.getVert (path.walk.length-2)=path.walk.getVert 2 := by rw [hlen]
  have hextmid : ext.walk.getVert 2=a := by
    have hh := hover 0 (by omega)
    simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hh
  let revext := fixed_seed_reverse h d ext hb
  let outer : CriticalPath d.radical geometry (path.walk.getVert 2) u := {
    start_color := by simpa only [he] using revext.start_color
    walk := revext.walk.copy he rfl
    shortest := by
      rw [SimpleGraph.Walk.length_copy]
      exact revext.shortest.trans (congrArg
        (fun t => (cosetGraph d.radical).dist t u) he)
    critical := by simpa only [he] using revext.critical }
  have homid : outer.walk.getVert 2=a := by
    change (ext.walk.reverse.copy he rfl).getVert 2=a
    rw [SimpleGraph.Walk.getVert_copy,SimpleGraph.Walk.getVert_reverse,ext.length_eq_b,hb]
    exact hextmid
  have hfixede := radius_fixed_at d path.start_color outer.start_color hfixed
  have hi := h.replacement_distance_four_fixed_path_seed_index d outer hb hfixede
  simpa only [homid] using hi

/-- The actual terminal seed supplies the other oriented source (3.10)
budget on this very path, so the two required budgets need no premises. -/
theorem Input.replacement_distance_four_fixed_path_terminal_seed_index
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    (B d.radical (path.walk.getVert 2) (geometry.Z_normal _)).relIndex
      (U d.radical z)=Nat.card F := by
  let rev := fixed_seed_reverse h d path hb
  have hmid : rev.walk.getVert 2=path.walk.getVert 2 := by
    change path.walk.reverse.getVert 2=path.walk.getVert 2
    rw [SimpleGraph.Walk.getVert_reverse,path.length_eq_b,hb]
  have hfixedz := radius_fixed_at d path.start_color path.end_color hfixed
  have hi := h.replacement_distance_four_fixed_path_reciprocal_seed_index d rev hb hfixedz
  simpa only [hmid] using hi

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
