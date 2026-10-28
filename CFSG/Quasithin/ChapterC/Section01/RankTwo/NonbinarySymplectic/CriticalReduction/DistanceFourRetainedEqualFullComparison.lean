module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullRootFailure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourEqualSmallCriticalFixed
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootCommutator
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourKernelNormality

/-!
# Full comparison from the two retained equal-small fixed identities

A failed full comparison puts the kernel commutator inside the actual critical
commutator. The first retained fixed identity centralizes it at the original
vertex; the second centralizes it at the backward start. The same second
selector transports this fixedness to the full far seed, where natural-cover
vanishing contradicts its field-sized order. No radius-fixed or generating-
pair hypothesis is assumed, and both original full kernels are retained.
Source: MS93 (5.12)(1), printed pp.924--925, equal-small case.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
open ChapterB.QuasisimpleSource
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

set_option maxHeartbeats 800000 in
/-- The two retained equal-small selectors prove comparison for the entire
source kernel, including its full central attachment, without radius fixedness. -/
theorem Input.replacement_distance_four_retained_equal_full_comparison
    {geometry : Geometry d.radical} {a z u w v s : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (r : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a)
    (hru : act d.radical r (path.walk.getVert 2)=u)
    (hrw : act d.radical r (path.walk.getVert 1)=w)
    (hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1))
        (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) :
          Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F^2)
    (hfixa : (Z d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hfirst : back.walk.getVert 1=w)
    (hmid : back.walk.getVert 2=a)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical u)
    (hya : act d.radical y a=v) (hys : act d.radical y w=s)
    (hfixu : (Z d.radical u ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
          (Q d.radical s) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical u ⊓ centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical))) :
    ⁅Z d.radical v ⊓ Q d.radical a,Z d.radical (path.walk.getVert 2)⁆ ≤
      ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ⊔
        ⁅Z d.radical v ⊓ Q d.radical a,
          X d.radical (path.walk.getVert 2) ⊓ Q d.radical u⁆ := by
  by_contra hbad
  let e := path.walk.getVert 2
  let W := Z d.radical v ⊓ Q d.radical a
  let A := X d.radical e ⊓ Q d.radical u
  let D := ⁅W,A⁆
  let C := ⁅Z d.radical u,Z d.radical e⁆
  let J := Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
    (Q d.radical w) (Nat.card F^2)
  let E := Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
    (Q d.radical s) (Nat.card F^2)
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hl : back.walk.length=4 := back.length_eq_b.trans hb
  have huw : Adjacent d.radical u w := by
    rw [←hfirst]
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by omega : 0<back.walk.length))
  have haw : Adjacent d.radical a w := by
    rw [←hmid,←hfirst]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by omega : 1<back.walk.length)))
  have hra : act d.radical r a=a := hr
  have hbackequal : Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical w) (Nat.card F^2)=J := by
    have hh := congrArg (Subgroup.map (MulAut.conj r⁻¹).toMonoidHom) hequal
    rw [←mover_act,←mover_act,hru,hrw,hra] at hh
    exact hh.symm
  have hbackmove : (centralizer (J : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical u) ≤ Nat.card F^2 := by
    have hh := own_index_act (Nat.card F^2) r a (path.walk.getVert 1)
    rw [hra,hrw] at hh
    have he := own_index_neighbors (R := d.radical) (Nat.card F^2) huw haw
    exact he.symm.trans_le (hh.trans_le hJm)
  have hyu : act d.radical y u=u := hy
  have hus : Adjacent d.radical u s := by
    rw [←hyu,←hys]
    exact (adjacent_act_iff d.radical y _ _).mpr huw
  have hvs : Adjacent d.radical v s := by
    rw [←hya,←hys]
    exact (adjacent_act_iff d.radical y _ _).mpr haw
  obtain ⟨hDC,hcard⟩ := h.replacement_distance_four_full_root_comparison_of_failure
    d path hb back hus hvs hbad
  change D ≤ C at hDC
  change Nat.card D=Nat.card F at hcard
  obtain ⟨_,hWS,hcent,_,_⟩ := full_comparison_actor h d path hb back hus hvs
  have hsmall : (Q d.radical e).relIndex (Z d.radical u)<Nat.card F^2 := by
    apply h.replacement_critical_index_lt_square_of_escape d back (by omega) W hWS hcent
    intro hc
    apply hbad
    rw [commutator_comm]
    exact hc.trans le_sup_left
  have hsmall' : (Q d.radical u).relIndex (Z d.radical e)<Nat.card F^2 := by
    rw [(h.replacement_small_critical_indices_eq_field d back (by omega) hsmall).2]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  have hCJa : C ≤ fixedCore d.radical a :=
    h.replacement_distance_four_equal_small_critical_fixed d path hb r hr hru hrw
      hequal hJm hfixa
  have hCJ : C ≤ centralizer (J : Set (FreeAmalgam d.radical)) := by
    have hh := h.replacement_root_critical_commutator_fixed_by_first_mover d back hb4 hsmall'
    simpa only [hfirst] using hh
  have hEeq : E=Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical s) (Nat.card F^2) := by
    have hh := congrArg (Subgroup.map (MulAut.conj y⁻¹).toMonoidHom) hbackequal
    rw [←mover_act,←mover_act,hya,hys,hyu] at hh
    exact hh
  have hEsmall : (centralizer (Subgroup.SmallMover.join (U d.radical u)
      (Q d.radical u) (Q d.radical s) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
        (U d.radical u) ≤ Nat.card F^2 := by
    have hh := own_index_act (Nat.card F^2) y u w
    rw [hyu,hys] at hh
    exact hh.trans_le hbackmove
  have hDE : D ≤ centralizer (E : Set (FreeAmalgam d.radical)) := by
    have hcomm := (h.replacement_equal_root_neighbor_commutator d back hb4
      hus hvs hsmall' hEsmall hEeq).2
    rw [←hEeq] at hcomm
    have hQE : Q d.radical u ≤ E := by
      rw [hEeq]
      exact core_le_mover h d back.start_color hus
    have hd : D ≤ omegaCenter E :=
      (commutator_mono inf_le_left (inf_le_right.trans hQE)).trans hcomm
    intro x hx b hb
    exact (mem_omegaCenter_iff.mp (hd hx)).2.2 b hb
  have hDZu : D ≤ Z d.radical u := hDC.trans (critical_commutator_le_start_seed back)
  have hDu : D ≤ centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical)) :=
    ((le_inf (le_inf hDZu (hDC.trans hCJ)) hDE).trans_eq hfixu).trans inf_le_right
  have hCa : D ≤ centralizer (Ltilde d.radical a : Set (FreeAmalgam d.radical)) :=
    (hDC.trans hCJa).trans inf_le_right
  have hDy : D.map (MulAut.conj y⁻¹).toMonoidHom=D :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hDu ((stabilizer d.radical u).inv_mem hy)))
  have hCv : D ≤ centralizer (Ltilde d.radical v : Set (FreeAmalgam d.radical)) := by
    have hh := (map_mono (f := (MulAut.conj y⁻¹).toMonoidHom) hCa).trans
      (map_centralizer_le_centralizer_image _ _)
    change D.map (MulAut.conj y⁻¹).toMonoidHom ≤ centralizer
      ((Ltilde d.radical a).map (MulAut.conj y⁻¹).toMonoidHom : Set (FreeAmalgam d.radical)) at hh
    rwa [hDy,←Ltilde_act,hya] at hh
  have hv : color d.radical v=false := by
    rw [←hya,action_preserves_color]
    exact path.start_color
  have hAS : A ≤ stabilizer d.radical v := inf_le_right.trans
    (Q_le_stabilizer_of_dist_le_two u v back.start_color hv
      (by rw [SimpleGraph.dist_comm]; exact neighbor_distance_le_two hus hvs))
  have hz : D=⊥ := by
    rw [show D=⁅A,W⁆ from commutator_comm W A]
    exact (full_seed_commutator_fixed_iff h d geometry hb4 hv A W hAS inf_le_left).mp
      (by rw [commutator_comm]; exact hCv)
  have hcardone : Nat.card D=1 := Subgroup.card_eq_one.mpr hz
  have hq : 1<Nat.card F := Finite.one_lt_card
  omega

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
