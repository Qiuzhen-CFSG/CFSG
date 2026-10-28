module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.RootEscape
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.MovingRadius

/-!
# The literal obstruction when the radius has no backward escape

An endpoint actor containing the full critical root cannot have the same
image order as that root while moving the full endpoint intersection:
matching images leaves an element of the exact endpoint kernel, so both
factors centralize the intersection. Thus its image order is greater than q.

Apply this to the original radius when it is contained in the penultimate
kernel. `RootEscape` excludes its backward-path alternative under precisely
that containment and supplies field-sized critical indices and movement
on the full endpoint intersection. The same radius acts quadratically,
and its quotient by the full fixed preimage has order at least q⁴.
These constrain the remaining source root case; they do not exclude it
or supply the final distance-two replacement witness.
Source: MS93 (3.3), (5.2)(iii), and the root case of (5.7)--(5.9),
printed pp.867, 915, 919--922.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.RankTwo.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- A local actor containing the full critical root and moving the full
endpoint intersection has strictly more images than that root. -/
theorem Input.replacement_critical_actor_image_gt_field
    {geometry : Geometry d.radical} {a z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (Y : Subgroup (FreeAmalgam d.radical))
    (hYS : Y ≤ stabilizer d.radical z) (hZY : Z d.radical a ≤ Y)
    (hroot : (Q d.radical z).relIndex (Z d.radical a) = Nat.card F)
    (hmove : Nat.card F ≤ (centralizer (Y : Set (FreeAmalgam d.radical))).relIndex
      (Z d.radical z ⊓ Q d.radical a)) :
    Nat.card F < (Q d.radical z).relIndex Y := by
  obtain ⟨E,hE,f,hf,hfQ,π,hπ,hker,hact⟩ :=
    h.replacement_inner_natural_action d geometry hb path.end_color
  let g := f.comp (inclusion (hZY.trans hYS))
  let k := f.comp (inclusion hYS)
  have hg : Nat.card g.range = Nat.card F :=
    (quotient_image_card _ _ _ (hZY.trans hYS) f hfQ).trans hroot
  have hk : Nat.card k.range = (Q d.radical z).relIndex Y :=
    quotient_image_card _ _ _ hYS f hfQ
  by_contra! hsmall
  have hr : g.range = k.range := eq_of_le_of_card_ge
    (by rintro _ ⟨x,rfl⟩; exact ⟨inclusion hZY x,rfl⟩) (by rw [hg,hk]; exact hsmall)
  have hfixed : Z d.radical z ⊓ Q d.radical a ≤ centralizer (Y : Set (FreeAmalgam d.radical)) := by
    intro v hv y hy
    have hky : k ⟨y,hy⟩ ∈ g.range := hr ▸ (show k ⟨y,hy⟩ ∈ k.range from ⟨_,rfl⟩)
    obtain ⟨x,hx⟩ := hky
    let t : stabilizer d.radical z := (inclusion (hZY.trans hYS) x)⁻¹ * inclusion hYS ⟨y,hy⟩
    have htf : t ∈ f.ker := by
      change f t = 1
      simp only [t,map_mul,map_inv]
      change (g x)⁻¹ * k ⟨y,hy⟩ = 1
      rw [hx,inv_mul_cancel]
    have htQ : t.val ∈ Q d.radical z := hfQ ▸ mem_map_of_mem (stabilizer d.radical z).subtype htf
    have hvx : Commute v x.val :=
      ((le_centralizer_iff.mp (commutator_eq_bot_iff_le_centralizer.mp
        (geometry.centralizes a path.start_color))) hv.2 x.val x.property).symm
    have hvt : Commute v t.val :=
      ((commutator_eq_bot_iff_le_centralizer.mp (geometry.centralizes z path.end_color)) hv.1 t.val htQ).symm
    have he : y = x.val*t.val := by simp [t]
    rw [he]
    exact (hvx.mul_right hvt).symm
  rw [relIndex_eq_one.mpr hfixed] at hmove
  have hq : 1 < Nat.card F := by
    rw [h.field_card]
    exact one_lt_pow₀ (by decide) (by have := h.nonbinary; omega)
  omega

/-- If the full radius is trapped in the penultimate kernel, the same
original radius gives a quadratic, moving root obstruction. In particular
its endpoint image is strictly larger than q, and its quotient by the full
fixed preimage still has order at least q⁴. -/
theorem Input.replacement_trapped_radius_obstruction
    {geometry : Geometry d.radical} {a t z : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : 4 ≤ geometry.b d.radical)
    (hat : Adjacent d.radical a t)
    (htrap : V d.radical a ≤ Q d.radical (path.walk.getVert (path.walk.length-2))) :
    (Q d.radical z).relIndex (Z d.radical a) = Nat.card F ∧
      (Q d.radical a).relIndex (Z d.radical z) = Nat.card F ∧
      Nat.card F < (Q d.radical z).relIndex (V d.radical a) ∧
      Nat.card F ≤ (centralizer (V d.radical a : Set (FreeAmalgam d.radical))).relIndex
        (Z d.radical z ⊓ Q d.radical a) ∧
      ⁅⁅X d.radical z ⊓ Q d.radical a,V d.radical a⁆,V d.radical a⁆ = ⊥ ∧
      Nat.card F ^ 4 ≤ (B d.radical a (geometry.Z_normal a)).relIndex (V d.radical a) := by
  obtain ⟨u,x,hut,hx,hatx,hutx,hcases⟩ := h.replacement_backward_path_or_root_escape d path hb hat
  have hYV : Z d.radical (act d.radical x u) ≤ V d.radical a :=
    le_sup_left.trans (neighbor_seed_join_le_radius hatx hutx)
  have hVS : V d.radical a ≤ stabilizer d.radical z :=
    (le_inf le_rfl htrap).trans (truncated_radius_le_endpoint_stabilizer path (by omega))
  rcases hcases with ⟨back,_,_⟩ | ⟨hk,hn,hi,hi',_,_,_⟩
  · exact (back.critical.2 (hYV.trans htrap)).elim
  · have hindex := h.replacement_seed_actor_centralizer_index_ge_field d path (by omega)
      (Z d.radical (act d.radical x u)) (hYV.trans hVS)
      (hYV.trans (geometry.V_le_Q (by omega) a path.start_color)) hn
      (V d.radical a) hYV hVS
    have htrip := (h.replacement_radius_commutator_bounds d geometry hb path.start_color z
      (path.walk.getVert (path.walk.length-2))).2
    rw [inf_eq_left.mpr htrap] at htrip
    exact ⟨hi,hi',h.replacement_critical_actor_image_gt_field d path hb (V d.radical a)
      hVS (Z_le_VBall d.radical a 2) hi hindex,hindex,htrip,
      h.replacement_moving_radius_index_ge_fourth_power d geometry (by omega) path.start_color hat⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
