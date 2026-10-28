module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootCommutator
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalComparison

/-!
# Placement of the distance-four comparison commutator

In the failure branch of MS93 (5.12)(1), retain the actual backward
path u to e and its literal midpoint a. The full R1 lies in all three
seeds Z_u, Z_a, Z_e and in the selected moving group U_v. Its intersection
with the entire endpoint residual fixed subgroup is trivial. In particular,
no fixed attachment has been discarded from the comparison commutator.

These are consequences of the failed comparison. The selected-source
normality argument excluding that failure is a separate obligation.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction.LargeDistance
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The full intersection commutator has trivial intersection with the
entire residual fixed subgroup at the endpoint, already before using the
overlap of the two paths. -/
theorem Input.replacement_distance_four_root_fixed_disjoint_of_failure
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (hbad : ¬ ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) :
    Disjoint ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆
      (centralizer (Ltilde d.radical (path.walk.getVert 2) : Set (FreeAmalgam d.radical))) := by
  let e := path.walk.getVert 2
  let D := ⁅U d.radical v ⊓ Q d.radical z,X d.radical e ⊓ Q d.radical u⁆
  let C := centralizer (Ltilde d.radical e : Set (FreeAmalgam d.radical))
  obtain ⟨hD,hcard⟩ := h.replacement_distance_four_root_comparison_of_failure d path hb back hut hvt hbad
  change Nat.card D=Nat.card F at hcard
  obtain ⟨hi,_,_⟩ := h.replacement_distance_four_comparison_failure d path hb back hut hvt hbad
  obtain ⟨_,hWS,_,_,_⟩ := h.replacement_distance_four_comparison_actor d path hb back hut hvt
  have hDZ : D ≤ Z d.radical e := hD.trans (critical_commutator_le_endpoint ⟨u,e,back⟩)
  let := finite_Z d.radical e
  let : Finite D := Finite.of_injective (inclusion hDZ) (inclusion_injective _)
  have hsmall : (Q d.radical e).relIndex (Z d.radical u) < Nat.card F^2 := by
    rw [hi]
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  have hn : D ≠ ⊥ := by
    intro hh
    have hc : Nat.card D=1 := card_eq_one.mpr hh
    have hq : 1 < Nat.card F := Finite.one_lt_card
    omega
  have hlo := h.replacement_root_intersection_central_index_ge_field d back (by omega)
    hsmall (U d.radical v ⊓ Q d.radical z) hWS hn
  have hidx : C.relIndex D=Nat.card D := Nat.le_antisymm
    (Nat.le_of_dvd (Nat.card_pos (α := D)) (relIndex_dvd_card C D)) (by rwa [hcard])
  have hmul := relIndex_mul_relIndex (⊥ : Subgroup (FreeAmalgam d.radical)) (D ⊓ C) D
    bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_left,hidx] at hmul
  have hc : Nat.card (D ⊓ C : Subgroup (FreeAmalgam d.radical))=1 := by
    apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := D))
    simpa only [one_mul] using hmul
  exact disjoint_iff.mpr (card_eq_one.mp hc)

/-- The literal midpoint overlap places the full comparison commutator in
the original seed as well as both backward endpoint seeds and U_v. -/
theorem Input.replacement_distance_four_root_seed_placement_of_failure
    {geometry : Geometry d.radical} {a z u v t : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hmid : back.walk.getVert 2=a)
    (hut : Adjacent d.radical u t) (hvt : Adjacent d.radical v t)
    (hbad : ¬ ⁅U d.radical v ⊓ Q d.radical z,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆) :
    ⁅U d.radical v ⊓ Q d.radical z,X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ ≤
      (Z d.radical u ⊓ Z d.radical a) ⊓ Z d.radical (path.walk.getVert 2) ⊓ U d.radical v := by
  let e := path.walk.getVert 2
  obtain ⟨hD,_⟩ := h.replacement_distance_four_root_comparison_of_failure d path hb back hut hvt hbad
  obtain ⟨_,hi',_⟩ := h.replacement_distance_four_comparison_failure d path hb back hut hvt hbad
  obtain ⟨_,_,_,_,hnorm⟩ := h.replacement_distance_four_comparison_actor d path hb back hut hvt
  have hfour : 4 ≤ geometry.b d.radical := by omega
  have hsmall : (Q d.radical u).relIndex (Z d.radical e) < Nat.card F^2 := by
    rw [hi']
    have hq : 1 < Nat.card F := Finite.one_lt_card
    nlinarith
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical back.start_color
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical path.start_color
  let y := g⁻¹*j
  have hy : act d.radical y u=a := by
    rw [hg,act_mVertex]
    dsimp only [y]
    rw [mul_inv_cancel_left,←hj]
  have hsmallAct : (Q d.radical (act d.radical y u)).relIndex
      (Z d.radical (act d.radical y e)) < Nat.card F^2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj y⁻¹).injective]
    exact hsmall
  have hat : Adjacent d.radical a (path.walk.getVert 1) := by
    simpa using (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by rw [path.length_eq_b]; omega : 0 < path.walk.length))
  have hXa : X d.radical a=Z d.radical a := by
    have hh := h.replacement_root_X_eq_Z d (back.act y) hfour (by rw [hy]; exact hat) hsmallAct
    simpa only [hy] using hh
  have huV : Z d.radical u ≤ V d.radical a := by
    apply le_iSup_of_le u
    apply le_iSup_of_le (show (cosetGraph d.radical).dist u a ≤ 2 from ?_)
    · exact le_rfl
    · rw [←hmid,back.dist_start (by rw [back.length_eq_b]; omega)]
  have heV : Z d.radical e ≤ V d.radical a := by
    apply le_iSup_of_le e
    apply le_iSup_of_le (show (cosetGraph d.radical).dist e a ≤ 2 from ?_)
    · exact le_rfl
    · rw [SimpleGraph.dist_comm,path.dist_start (by rw [path.length_eq_b]; omega)]
  have hRZa : ⁅Z d.radical u,Z d.radical e⁆ ≤ Z d.radical a :=
    ((commutator_mono huV heV).trans
      (h.replacement_radius_commutator_bounds d geometry hfour path.start_color e z).1).trans_eq hXa
  exact le_inf
    (le_inf (le_inf (hD.trans (critical_commutator_le_start_seed back)) (hD.trans hRZa))
      (hD.trans (critical_commutator_le_endpoint ⟨u,e,back⟩)))
    ((le_normalizer_iff_commutator_le_left.mp hnorm).trans inf_le_left)

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
