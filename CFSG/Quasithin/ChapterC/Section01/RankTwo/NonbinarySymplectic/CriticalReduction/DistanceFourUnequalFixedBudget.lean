module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullKernelNormality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.IndividualPaths

/-!
# The actual unequal-mover seed budget in the fixed-radius branch

On the backward critical path u to e with midpoint a, suppose the movers
at u and a on its first edge differ. A hypothetical B_u-index above q
makes their seed join nonnormal. The actual unequal selector then supplies
individual residual generation and a backward path or its trapped alternative.
The full Q_a comparison excludes the trapped alternative on the same selector.

The resulting path v to a makes Z_v intersect Q_a an actual critical
kernel. Its first mover and Z_e normalize that full kernel joined with Z_u;
the proved individual generation makes L_u normalize it. Its index below
q to the fourth power forces the join into B_u. The critical image has
order q, so the retained selector gives the claimed original U_a-index bound.
No individual-generation, comparison, or selected-path premise is supplied.
Source: the unequal-mover part of MS93 (5.12)(3), printed pp.926--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- An unequal neighboring mover forces the literal reciprocal seed budget
in the fixed-radius branch, using the actual source selector internally. -/
theorem Input.replacement_distance_four_unequal_fixed_seed_budget
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hne : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) ≠
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2)) :
    (B d.radical u (geometry.Z_normal u)).relIndex (U d.radical a) ≤ Nat.card F := by
  by_contra! hmove
  let e := path.walk.getVert 2
  let t := back.walk.getVert 1
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hb2 : 2 < geometry.b d.radical := by omega
  have hbl : back.walk.length=4 := back.length_eq_b.trans hb
  have hut : Adjacent d.radical u t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by omega : 0<back.walk.length))
  have hat : Adjacent d.radical a t := by
    rw [←hmid]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by omega : 1<back.walk.length)))
  have hpen : back.walk.getVert (back.walk.length-2)=a := by rw [hbl]; exact hmid
  have hroot := (h.replacement_distance_four_fixed_critical_indices d hb
    path.start_color hfixed back).2
  have hsmall : (Q d.radical u).relIndex (Z d.radical e)<Nat.card F^2 := by
    rw [hroot]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  have hnormal : ¬ stabilizer d.radical u ≤ normalizer
      ((Z d.radical a ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    intro hn
    have hidx := (neighbor_seed_join_index_le geometry (by omega) back.start_color hut hat).trans
      (h.replacement_root_neighbor_seed_index_le_cube d back hb4 hut hat hsmall)
    have hq : 1<Nat.card F := Finite.one_lt_card
    have hYB := h.replacement_small_radius_le_B d geometry hb2 back.start_color
      (Z d.radical a ⊔ Z d.radical u) (neighbor_seed_join_le_radius hut hat)
      ((Ltilde_le_stabilizer u).trans hn)
      (hidx.trans_lt (Nat.pow_lt_pow_right hq (by decide : 3<4)))
    have hone := relIndex_eq_one.mpr (((U_le_Z a).trans le_sup_left).trans hYB)
    rw [hone] at hmove
    exact (not_lt_of_ge hq.le) hmove
  obtain ⟨g,hg,hus,hvs,hindex,hJmap,hgen,hres,hfixedJ,hfixedJa,hquadJa,hquadEc,
    hEcindex,hQnot,hEcimage,hn,hcases⟩ :=
    h.replacement_unequal_individual_generation_root_at_neighbor d back hb4 hut rfl hat
      hnormal hsmall hne
  let v := act d.radical g⁻¹ a
  let s := act d.radical g⁻¹ t
  have hy : g⁻¹ ∈ stabilizer d.radical u :=
    (stabilizer d.radical u).inv_mem (Ltilde_le_stabilizer u hg)
  have nextData : ∃ next : CriticalPath d.radical geometry v a, next.walk.getVert 1=s := by
    rcases hcases with ⟨next,hfirst,hover⟩ | ⟨htrap,_⟩
    · let next' : CriticalPath d.radical geometry v a := {
        start_color := next.start_color
        walk := next.walk.copy rfl hpen
        shortest := by simpa only [SimpleGraph.Walk.length_copy,hpen] using next.shortest
        critical := by simpa only [hpen] using next.critical }
      refine ⟨next',?_⟩
      change (next.walk.copy rfl hpen).getVert 1=s
      simpa only [SimpleGraph.Walk.getVert_copy] using hfirst
    · have hnfull := h.replacement_distance_four_full_fixed_kernel_normalized d path hb back
        hmid hus hvs g⁻¹ hy rfl hfixed
      rw [hpen] at htrap
      rw [inf_eq_left.mpr htrap] at hnfull
      exact (hn hnfull).elim
  obtain ⟨next,hfirst⟩ := nextData
  let W := Z d.radical v ⊓ Q d.radical a
  let Y := W ⊔ Z d.radical u
  have hLN : Ltilde d.radical u ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    hres.trans (h.replacement_distance_four_fixed_full_kernel_normalized d path hb back
      hmid hus hvs g⁻¹ hy rfl hfixed next hfirst)
  have hSV : Z d.radical v ⊔ Z d.radical u ≤ V d.radical u :=
    neighbor_seed_join_le_radius hus hvs
  let := finite_stabilizer d.radical u
  let : Finite (Z d.radical v ⊔ Z d.radical u : Subgroup (FreeAmalgam d.radical)) :=
    Finite.of_injective (inclusion (hSV.trans
      ((geometry.V_le_Q hb2 u back.start_color).trans (fun _ hx => hx.1))))
      (inclusion_injective _)
  have hbound := h.replacement_root_neighbor_seed_index_le_cube d back hb4 hus hvs hsmall
  have hiY : (Z d.radical u).relIndex Y ≤ Nat.card F^3 :=
    (relIndex_le_of_le_right (sup_le_sup inf_le_left le_rfl) index_ne_zero_of_finite).trans
      ((neighbor_seed_join_index_le geometry (by omega) back.start_color hus hvs).trans hbound)
  have hYB := h.replacement_small_radius_le_B d geometry hb2 back.start_color Y
    ((sup_le_sup inf_le_left le_rfl).trans hSV) hLN
    (hiY.trans_lt (Nat.pow_lt_pow_right (by exact Finite.one_lt_card) (by decide : 3<4)))
  have hWB : W ≤ B d.radical u (geometry.Z_normal u) := le_sup_left.trans hYB
  let := finite_Z d.radical v
  have hsmallZ := relIndex_le_of_le_left hWB (L := Z d.radical v) index_ne_zero_of_finite
  rw [inf_relIndex_left,
    (h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed next).1] at hsmallZ
  have hsmallU := ((B d.radical u (geometry.Z_normal u)).relIndex_le_of_le_right
    (U_le_Z v) index_ne_zero_of_finite).trans hsmallZ
  rw [hindex] at hsmallU
  exact hmove.not_ge hsmallU

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
