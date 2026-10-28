module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourDerivedEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPointNonfixedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPairedNonfixedPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourPrescribedComparison

/-!
# An actual critical path with root image at distance four

For a large original critical image the point and paired selectors give
an actual backward path in the literal midpoint orbit. In the nonfixed
branch, the normalizer obstruction gives root image. In the fixed branch,
the natural-section derived bound and the full commutator order do so.
All first mover sizes are exhausted, with no generation or orbit callback.

Consequently any distance-four critical path supplies a critical path
whose two reciprocal images have the original field order. This is an
existence reduction toward MS93 (5.12)(3); it does not assert a uniform
bound for all critical pairs and does not exclude distance four.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic

private theorem selected_midpoint_orbit
    {M : Type*} [Group M] {R : Subgroup M} {a e u : Vertex R}
    (g x : FreeAmalgam R) (hg : g ∈ Ltilde R a) (hx : x ∈ Ltilde R a)
    (hu : u=act R g⁻¹ e ∨ u=act R x (act R g⁻¹ e)) :
    ∃ r ∈ stabilizer R a, act R r e=u := by
  have hgS := (stabilizer R a).inv_mem (Ltilde_le_stabilizer a hg)
  rcases hu with hu | hu
  · exact ⟨g⁻¹,hgS,hu.symm⟩
  · refine ⟨g⁻¹*x,(stabilizer R a).mul_mem hgS (Ltilde_le_stabilizer a hx),?_⟩
    rw [act_mul,←hu]

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Every large original critical image at distance four has an actual
overlapping backward path in the midpoint orbit with both root indices. -/
theorem Input.replacement_distance_four_large_root_backward_path
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z)) :
    ∃ u w, ∃ r ∈ stabilizer d.radical a,
      act d.radical r (path.walk.getVert 2)=u ∧
      Adjacent d.radical a w ∧ Adjacent d.radical u w ∧
      ∃ back : CriticalPath d.radical geometry u (path.walk.getVert 2),
        back.walk.getVert 1=w ∧
        (∀ i ≤ 2, back.walk.getVert (i+2)=path.walk.getVert i) ∧
        (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
        (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F := by
  have hlen : path.walk.length-2=2 := by have hl := path.length_eq_b; omega
  by_cases hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a
  · obtain ⟨g,hg,x,hx,u,w,hchoose,haw,huw,back,hfirst,hover,_⟩ :=
      h.replacement_distance_four_large_prescribed_comparison d path hb hlarge
    obtain ⟨r,hr,hru⟩ := selected_midpoint_orbit g x hg hx (hchoose.imp And.left And.left)
    have hmid : back.walk.getVert 2=a := by
      simpa only [Nat.zero_add,SimpleGraph.Walk.getVert_zero] using hover 0 (by omega)
    have hi := h.replacement_distance_four_fixed_orbit_backward_indices
      d path hb back hmid r hr hru hfixed
    exact ⟨u,w,r,hr,hru,haw,huw,back,hfirst,by simpa only [hlen] using hover,hi⟩
  by_cases hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical a) ≤ Nat.card F^2
  · obtain ⟨g,hg,x,hx,haw,hvw,haw',hvw',_,_,_,_,_,u,w,hchoose,back,hfirst,hover,hi,hi'⟩ :=
      h.replacement_distance_four_paired_nonfixed_root_backward_path d path hb hlarge hJm hfixed
    obtain ⟨r,hr,hru⟩ := selected_midpoint_orbit g x hg hx (hchoose.imp And.left And.left)
    have hadj : Adjacent d.radical a w ∧ Adjacent d.radical u w := by
      rcases hchoose with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ⟨haw,hvw⟩
      · exact ⟨haw',hvw'⟩
    exact ⟨u,w,r,hr,hru,hadj.1,hadj.2,back,hfirst,hover,hi,hi'⟩
  · have hat : Adjacent d.radical a (path.walk.getVert 1) := by
      simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
        (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
    have hq : Nat.card F < Nat.card F^2 := by
      have hq : 1 < Nat.card F := Finite.one_lt_card
      nlinarith
    obtain ⟨c,hc,_,g,hg,haw,hvw,_,_,_,_,_,back,hfirst,hover,hresult⟩ :=
      h.replacement_distance_four_point_backward_fixed_or_root d path hb hat rfl
        (hq.trans_le hlarge) (lt_of_not_ge hJm)
    have hi := hresult.resolve_left hfixed
    refine ⟨act d.radical g⁻¹ c,act d.radical g⁻¹ (path.walk.getVert 1),g⁻¹,
      (stabilizer d.radical a).inv_mem (Ltilde_le_stabilizer a hg),?_,haw,hvw,
      back,hfirst,hover,hi⟩
    rw [hc]

/-- The actual distance-four geometry has a critical path with both
reciprocal images of the original field order. -/
theorem Input.replacement_distance_four_exists_root_critical_path
    (geometry : Geometry d.radical) (hb : geometry.b d.radical=4) :
    ∃ u e, ∃ _back : CriticalPath d.radical geometry u e,
      (Q d.radical e).relIndex (Z d.radical u)=Nat.card F ∧
      (Q d.radical u).relIndex (Z d.radical e)=Nat.card F := by
  let a := alpha d.radical
  obtain ⟨z,⟨path⟩⟩ := CriticalPath.exists_from (R := d.radical) (geometry := geometry)
    (a := a) rfl
  by_cases hsmall : (Q d.radical z).relIndex (Z d.radical a) < Nat.card F^2
  · exact ⟨a,z,path,h.replacement_small_critical_indices_eq_field d path (by omega) hsmall⟩
  have hi := h.replacement_critical_indices_equal d path (by omega)
  have hlarge : Nat.card F^2 ≤ (Q d.radical a).relIndex (Z d.radical z) := by
    rw [←hi]
    exact le_of_not_gt hsmall
  obtain ⟨u,_,_,_,_,_,_,back,_,_,hi,hi'⟩ :=
    h.replacement_distance_four_large_root_backward_path d path hb hlarge
  exact ⟨u,path.walk.getVert 2,back,hi,hi'⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
