module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourEqualSmallSeedIntersection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootPath
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootCommutator

/-!
# The mixed full kernels for the retained twist

The equal-small source relations put the mixed commutator in both original
mover centers. Normalization of the full two-seed intersection by the actual
twist transfers the terminal relation back to the original midpoint. The
retained fixed-space identities at both centers then let the original selector
transport fixedness to the selected full seed. Natural-cover vanishing kills
the commutator without a radius-fixed premise. The midpoint identity is the
actual reciprocal-selection certificate and remains explicit.
Source: MS93 (5.12)(3), printed pp.926--927.
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

private theorem equal_small_commutator_at
    (geometry : Geometry d.radical) (hb : geometry.b d.radical=4)
    {a t c : Vertex d.radical} (ha : color d.radical a=false)
    (hat : Adjacent d.radical a t) (hct : Adjacent d.radical c t)
    (hequal : Subgroup.SmallMover.join (U d.radical c) (Q d.radical c)
        (Q d.radical t) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical a) ≤ Nat.card F^2) :
    ⁅Z d.radical c,Q d.radical a⁆ ≤ Z d.radical a ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical t) (Nat.card F^2) : Set (FreeAmalgam d.radical)) := by
  obtain ⟨u,e,root,_,hi⟩ := h.replacement_distance_four_exists_root_critical_path d geometry hb
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical root.start_color
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical ha
  let r := g⁻¹*j
  have hra : act d.radical r u=a := by
    rw [hg,act_mVertex]
    dsimp only [r]
    rw [mul_inv_cancel_left,←hj]
  have hroot : (Q d.radical (act d.radical r u)).relIndex
      (Z d.radical (act d.radical r e))<Nat.card F^2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj r⁻¹).injective,hi]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  obtain ⟨hOmega,hcomm⟩ := h.replacement_equal_root_neighbor_commutator d (root.act r)
    (by omega) (by rw [hra]; exact hat) hct hroot
    (by simpa only [hra] using hJm) (by simpa only [hra] using hequal)
  rw [hra] at hOmega hcomm
  have hbound := (commutator_mono le_rfl (core_le_mover h d ha hat)).trans hcomm
  exact le_inf (hbound.trans hOmega) (fun x hx => (mem_omegaCenter_iff.mp (hbound hx)).2.2)

set_option maxHeartbeats 800000 in
/-- The original twist kills the mixed full-kernel commutator when the two
actual reciprocal fixed-space certificates are retained. -/
theorem Input.replacement_distance_four_retained_twisted_kernel_vanishing
    {geometry : Geometry d.radical} {a z u w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (r k : FreeAmalgam d.radical) (hr : r ∈ stabilizer d.radical a)
    (hk : k ∈ stabilizer d.radical a)
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
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)))
    (hfixa : (Z d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (hterminal : Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
        (Q d.radical (path.walk.getVert 3)) (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 3))
        (Nat.card F^2))
    (hterminalmove : (centralizer (Subgroup.SmallMover.join
        (U d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 3)) (Nat.card F^2) : Set (FreeAmalgam d.radical))).relIndex
      (U d.radical (path.walk.getVert 2)) ≤ Nat.card F^2)
    (hfixe : (Z d.radical (path.walk.getVert 2) ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
          (Q d.radical (path.walk.getVert 3)) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical (path.walk.getVert 2) ⊓ centralizer
        (stabilizer d.radical (path.walk.getVert 2) : Set (FreeAmalgam d.radical)))
    (hkn : k ∈ normalizer ((Z d.radical a ⊓ Z d.radical (path.walk.getVert 2) :
      Subgroup (FreeAmalgam d.radical)) : Set _)) :
    ⁅Z d.radical u ⊓ Q d.radical (act d.radical k (path.walk.getVert 2)),
      Z d.radical (act d.radical k z) ⊓ Q d.radical a⁆=⊥ := by
  let e := path.walk.getVert 2
  let t := path.walk.getVert 1
  let l := path.walk.getVert 3
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E := Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
    (Q d.radical w) (Nat.card F^2)
  let L := Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
    (Q d.radical l) (Nat.card F^2)
  let W := Z d.radical u ⊓ Q d.radical (act d.radical k e)
  let A := Z d.radical (act d.radical k z) ⊓ Q d.radical a
  let D := ⁅W,A⁆
  let fk := (MulAut.conj k⁻¹).toMonoidHom
  let fr := (MulAut.conj r⁻¹).toMonoidHom
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hl : path.walk.length=4 := path.length_eq_b.trans hb
  have he : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have hat : Adjacent d.radical a t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0<path.walk.length))
  have het : Adjacent d.radical e t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (path.walk.adj_getVert_succ (by omega : 1<path.walk.length)))
  have hel : Adjacent d.radical e l := (cosetGraph_adj d.radical _ _).mp
    (path.walk.adj_getVert_succ (by omega : 2<path.walk.length))
  have hzl : Adjacent d.radical z l := by
    have hz : path.walk.getVert 4=z := by rw [←hl,SimpleGraph.Walk.getVert_length]
    rw [←hz]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 3<path.walk.length)))
  have hra : act d.radical r a=a := hr
  have hka : act d.radical k a=a := hk
  have hQr : (Q d.radical a).map fr=Q d.radical a := by rw [←Q_act,hra]
  have hZr : (Z d.radical a).map fr=Z d.radical a := by rw [←Z_act,hra]
  have hJr : J.map fr=E := by
    change (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).map fr=E
    rw [←hequal,Subgroup.SmallMover.join_map _ (MulAut.conj r⁻¹).injective,
      ←U_act,←Q_act,←Q_act,hru,hrw]
  have hbase := equal_small_commutator_at h d geometry hb path.start_color hat het hequal hJm
  have hselected : ⁅Z d.radical u,Q d.radical a⁆ ≤ Z d.radical a ⊓ centralizer
      (E : Set (FreeAmalgam d.radical)) := by
    have hh := map_mono (f := fr) hbase
    rw [map_commutator,←Z_act,hru,hQr,
      map_inf _ _ _ (MulAut.conj r⁻¹).injective,hZr,
      Theory.GroupTheory.map_centralizer_equiv] at hh
    change ⁅Z d.radical u,Q d.radical a⁆ ≤ Z d.radical a ⊓ centralizer
      ((J.map fr : Subgroup (FreeAmalgam d.radical)) : Set _) at hh
    rwa [hJr] at hh
  have hDE : D ≤ Z d.radical a ⊓ centralizer (E : Set (FreeAmalgam d.radical)) :=
    (commutator_mono inf_le_left inf_le_right).trans hselected
  have hterm : ⁅Z d.radical z,Q d.radical e⁆ ≤ Z d.radical e ⊓ centralizer
      (L : Set (FreeAmalgam d.radical)) := by
    have hh := equal_small_commutator_at h d geometry hb he hel hzl hterminal hterminalmove
    change ⁅Z d.radical z,Q d.radical e⁆ ≤ Z d.radical e ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical e) (Q d.radical e)
        (Q d.radical l) (Nat.card F^2) : Set _) at hh
    change ⁅Z d.radical z,Q d.radical e⁆ ≤ Z d.radical e ⊓ centralizer
      (Subgroup.SmallMover.join (U d.radical z) (Q d.radical z)
        (Q d.radical (path.walk.getVert 3)) (Nat.card F^2) : Set _)
    rw [hterminal]
    exact hh
  have hDterm : D ≤ Z d.radical (act d.radical k e) ⊓ centralizer
      ((L.map fk : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    have hh := map_mono (f := fk) hterm
    rw [map_commutator,←Z_act,←Q_act,map_inf _ _ _ (MulAut.conj k⁻¹).injective,
      ←Z_act,Theory.GroupTheory.map_centralizer_equiv] at hh
    rw [show D=⁅A,W⁆ from commutator_comm W A]
    exact (commutator_mono inf_le_left inf_le_right).trans hh
  have hI : Z d.radical a ⊓ Z d.radical e=Z d.radical a ⊓ centralizer
      (J : Set (FreeAmalgam d.radical)) :=
    h.replacement_distance_four_equal_small_seed_intersection d geometry hb path.start_color
      hat het hequal hmove hJm
  have hIk : Z d.radical a ⊓ Z d.radical (act d.radical k e)=
      Z d.radical a ⊓ Z d.radical e := by
    have hn : k⁻¹ ∈ normalizer ((Z d.radical a ⊓ Z d.radical e :
        Subgroup (FreeAmalgam d.radical)) : Set _) := (normalizer _).inv_mem hkn
    have hh := mem_normalizer_iff_map_conj_eq.mp hn
    change (Z d.radical a ⊓ Z d.radical e).map fk=Z d.radical a ⊓ Z d.radical e at hh
    rwa [map_inf _ _ _ (MulAut.conj k⁻¹).injective,←Z_act,←Z_act,hka] at hh
  have hDI : D ≤ Z d.radical a ⊓ Z d.radical e :=
    (le_inf (hDE.trans inf_le_left) (hDterm.trans inf_le_left)).trans_eq hIk
  have hDJ : D ≤ centralizer (J : Set (FreeAmalgam d.radical)) :=
    (hDI.trans_eq hI).trans inf_le_right
  have hDa : D ≤ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) :=
    ((le_inf (le_inf (hDI.trans inf_le_left) hDJ) (hDE.trans inf_le_right)).trans_eq hfixa).trans
      inf_le_right
  have hDk : D.map (MulAut.conj k).toMonoidHom=D :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hDa hk))
  have hDL : D ≤ centralizer (L : Set (FreeAmalgam d.radical)) := by
    have hh := map_mono (f := (MulAut.conj k).toMonoidHom) (hDterm.trans inf_le_right)
    rw [hDk,Theory.GroupTheory.map_centralizer_equiv] at hh
    change D ≤ centralizer (((L.map fk).map (MulAut.conj k).toMonoidHom :
      Subgroup (FreeAmalgam d.radical)) : Set _) at hh
    rw [Subgroup.map_map] at hh
    have hc : (MulAut.conj k).toMonoidHom.comp fk=MonoidHom.id _ := by
      apply MonoidHom.ext
      intro x
      change k*(k⁻¹*x*(k⁻¹)⁻¹)*k⁻¹=x
      group
    rwa [hc,Subgroup.map_id] at hh
  have hDe : D ≤ centralizer (stabilizer d.radical e : Set (FreeAmalgam d.radical)) :=
    ((le_inf (le_inf (hDI.trans inf_le_right) hDJ) hDL).trans_eq hfixe).trans inf_le_right
  have hDr : D.map fr=D :=
    mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _
      (le_centralizer_iff.mp hDa ((stabilizer d.radical a).inv_mem hr)))
  have hDu : D ≤ centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical)) := by
    have hh := map_mono (f := fr) hDe
    rw [hDr,Theory.GroupTheory.map_centralizer_equiv] at hh
    change D ≤ centralizer (((stabilizer d.radical e).map fr :
      Subgroup (FreeAmalgam d.radical)) : Set _) at hh
    rw [←stabilizer_act,hru] at hh
    exact hh
  have hu : color d.radical u=false := by rw [←hru,action_preserves_color]; exact he
  have hua : (cosetGraph d.radical).dist u a=2 := by
    have hh := dist_act d.radical r e a
    rw [hru,hra] at hh
    rw [hh,SimpleGraph.dist_comm,path.dist_start (by omega)]
  have hAS : A ≤ stabilizer d.radical u := inf_le_right.trans
    (Q_le_stabilizer_of_dist_two d.radical a u path.start_color (by rwa [SimpleGraph.dist_comm]))
  have hz := (full_seed_commutator_fixed_iff h d geometry hb4 hu A W hAS inf_le_left).mp
    (by rw [commutator_comm]; exact hDu.trans (centralizer_le (Ltilde_le_stabilizer u)))
  change D=⊥
  rw [show D=⁅A,W⁆ from commutator_comm W A,hz]

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
