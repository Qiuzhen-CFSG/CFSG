module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullKernelNormality
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.PointRootPaths
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourUnequalFixedBudget

/-!
# The actual point-mover seed budget in the fixed-radius branch

A hypothetical B_u-index above q supplies the actual point-mover backward
selector. Its individual generation and literal second critical path are
proved by the existing point construction. Full source-kernel normalization
then makes the vertex residual normalize the selected kernel joined with Z_u.
The small-radius bound puts that join in B_u; the field-sized critical image
contradicts the preserved original seed index.

This proves the point-mover part of the source seed-budget duty without
an equality-of-movers hypothesis or supplied selector/generation premises.
The equal/small-mover case remains separate.
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

/-- A point mover forces the literal reciprocal seed budget under
radius fixedness; its actual individual selector is constructed internally. -/
theorem Input.replacement_distance_four_point_fixed_seed_budget
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hJm : Nat.card F^2 < (centralizer (Subgroup.SmallMover.join (U d.radical u)
      (Q d.radical u) (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) :
        Set (FreeAmalgam d.radical))).relIndex (U d.radical u)) :
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
  obtain ⟨g,hg,hus,hvs,hindex,htransport,hgen,hfixedJ,hn,next,hfirst,hover⟩ :=
    h.replacement_large_movement_root_backward_path d back hb4 hut rfl hat
      hmove hsmall hJm
  let v := act d.radical g⁻¹ a
  let s := act d.radical g⁻¹ t
  have hy : g⁻¹ ∈ stabilizer d.radical u :=
    (stabilizer d.radical u).inv_mem (Ltilde_le_stabilizer u hg)
  have hres : Ltilde d.radical u ≤
      Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
        (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical e := by
    rw [←htransport,hgen]
    exact Ltilde_le_stabilizer u
  let next' : CriticalPath d.radical geometry v a := {
    start_color := next.start_color
    walk := next.walk.copy rfl hpen
    shortest := by simpa only [SimpleGraph.Walk.length_copy,hpen] using next.shortest
    critical := by simpa only [hpen] using next.critical }
  have hfirst' : next'.walk.getVert 1=s := by
    simpa only [next',SimpleGraph.Walk.getVert_copy] using hfirst
  let W := Z d.radical v ⊓ Q d.radical a
  let Y := W ⊔ Z d.radical u
  have hLN : Ltilde d.radical u ≤ normalizer (Y : Set (FreeAmalgam d.radical)) :=
    hres.trans (h.replacement_distance_four_fixed_full_kernel_normalized d path hb back
      hmid hus hvs g⁻¹ hy rfl hfixed next' hfirst')
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
    (h.replacement_distance_four_fixed_critical_indices d hb path.start_color hfixed next').1] at hsmallZ
  have hsmallU := ((B d.radical u (geometry.Z_normal u)).relIndex_le_of_le_right
    (U_le_Z v) index_ne_zero_of_finite).trans hsmallZ
  rw [hindex] at hsmallU
  exact hmove.not_ge hsmallU

/-- A strict seed budget in the fixed-radius branch can occur only at
equal small movers; the unequal and point alternatives are excluded here. -/
theorem Input.replacement_distance_four_strict_fixed_seed_mover
    {geometry : Geometry d.radical} {a z u : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hfixed : ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hmove : Nat.card F < (B d.radical u (geometry.Z_normal u)).relIndex (U d.radical a)) :
    Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) ∧
      (centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) :
          Set (FreeAmalgam d.radical))).relIndex (U d.radical u) ≤ Nat.card F^2 := by
  constructor
  · by_contra hne
    exact hmove.not_ge (h.replacement_distance_four_unequal_fixed_seed_budget d
      path hb back hmid hfixed hne)
  · by_contra! hlarge
    exact hmove.not_ge (h.replacement_distance_four_point_fixed_seed_budget d
      path hb back hmid hfixed hlarge)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
