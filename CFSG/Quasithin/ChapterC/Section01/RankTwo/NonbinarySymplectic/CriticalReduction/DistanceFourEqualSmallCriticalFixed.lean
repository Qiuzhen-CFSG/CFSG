module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRootPath
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourSeedFixedTransfer
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootCommutator
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.EqualRootCommutator

/-!
# The original equal-small selector fixes the actual critical commutator

The internally constructed root path transports the equal-mover calculation
to the original vertex. The commutators of the original and selected full
seeds with Q lie in the two corresponding mover centers. Their actual
critical commutator therefore lies in both full-Z fixed subgroups. The
retained original-versus-selected fixed equality makes it vertex-central.
For an actual backward image at least q squared, escaping-actor control
then fixes the midpoint seed and hence the whole original radius.

All selectors and full central attachments are retained. The large-image
premise concerns the actual backward path; no root image is treated as large.
Source: MS93 (5.12)(2), printed p.925, the equal-small-mover subcase.
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

/-- The same equal-small selector and its retained full fixed-space equality
make the actual critical commutator fixed at the original vertex. -/
theorem Input.replacement_distance_four_equal_small_critical_fixed
    {geometry : Geometry d.radical} {a z u w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical a)
    (hyu : act d.radical y (path.walk.getVert 2)=u)
    (hyw : act d.radical y (path.walk.getVert 1)=w)
    (hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1))
        (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) :
          Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F^2)
    (hfixers : (Z d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical))) :
    ⁅Z d.radical u,Z d.radical (path.walk.getVert 2)⁆ ≤ fixedCore d.radical a := by
  let e := path.walk.getVert 2
  let t := path.walk.getVert 1
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let E := Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
    (Q d.radical w) (Nat.card F^2)
  have hb4 : 4 ≤ geometry.b d.radical := by omega
  have hl : path.walk.length=4 := path.length_eq_b.trans hb
  have hat : Adjacent d.radical a t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using
      (cosetGraph_adj d.radical _ _).mp (path.walk.adj_getVert_succ (by omega : 0<path.walk.length))
  have het : Adjacent d.radical e t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (path.walk.adj_getVert_succ (by omega : 1<path.walk.length)))
  obtain ⟨c,b,root,_,hi⟩ := h.replacement_distance_four_exists_root_critical_path d geometry hb
  obtain ⟨g,hg⟩ := exists_mVertex_of_color d.radical root.start_color
  obtain ⟨j,hj⟩ := exists_mVertex_of_color d.radical path.start_color
  let r := g⁻¹*j
  have hra : act d.radical r c=a := by
    rw [hg,act_mVertex]
    dsimp only [r]
    rw [mul_inv_cancel_left,←hj]
  have hroot : (Q d.radical (act d.radical r c)).relIndex
      (Z d.radical (act d.radical r b))<Nat.card F^2 := by
    rw [Q_act,Z_act,relIndex_map_map_of_injective _ _ (MulAut.conj r⁻¹).injective,hi]
    have hq : 1<Nat.card F := Finite.one_lt_card
    nlinarith
  obtain ⟨hOmega,hcomm⟩ := h.replacement_equal_root_neighbor_commutator d (root.act r)
    hb4 (by rw [hra]; exact hat) het hroot
    (by simpa only [hra] using hJm) (by simpa only [hra] using hequal)
  rw [hra] at hOmega hcomm
  have hCQ : ⁅Z d.radical e,Q d.radical a⁆ ≤ Z d.radical a ⊓ centralizer (J : Set _) := by
    have hh := (commutator_mono le_rfl (core_le_mover h d path.start_color hat)).trans hcomm
    refine le_inf (hh.trans hOmega) ?_
    intro x hx b hb
    exact (mem_omegaCenter_iff.mp (hh hx)).2.2 b hb
  let f := (MulAut.conj y⁻¹).toMonoidHom
  have hya : act d.radical y a=a := hy
  have hQmap : (Q d.radical a).map f=Q d.radical a := by rw [←Q_act,hya]
  have hZmap : (Z d.radical a).map f=Z d.radical a := by rw [←Z_act,hya]
  have hJmap : J.map f=E := by
    change (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).map f=E
    rw [←hequal,Subgroup.SmallMover.join_map _ (MulAut.conj y⁻¹).injective,
      ←U_act,←Q_act,←Q_act,hyu,hyw]
  have hUQ : ⁅Z d.radical u,Q d.radical a⁆ ≤ Z d.radical a ⊓ centralizer (E : Set _) := by
    have hh := map_mono (f := f) hCQ
    rw [map_commutator,←Z_act,hyu,hQmap,
      map_inf _ _ _ (MulAut.conj y⁻¹).injective,hZmap,
      Theory.GroupTheory.map_centralizer_equiv] at hh
    change ⁅Z d.radical u,Q d.radical a⁆ ≤ Z d.radical a ⊓
      centralizer ((J.map f : Subgroup (FreeAmalgam d.radical)) : Set _) at hh
    rwa [hJmap] at hh
  have hecolor : color d.radical e=false := (path.vertex_color (by omega)).mpr (by decide)
  have heQa : Z d.radical e ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt _ e (geometry.exists_critical e hecolor)
    rw [geometry.distance_constant e hecolor]
    change (cosetGraph d.radical).dist e a < geometry.b d.radical
    rw [SimpleGraph.dist_comm,path.dist_start (by omega),hb]
    decide
  have huQa : Z d.radical u ≤ Q d.radical a := by
    have hh := map_mono (f := f) heQa
    rwa [←Z_act,hyu,hQmap] at hh
  have hCfirst : ⁅Z d.radical u,Z d.radical e⁆ ≤ Z d.radical a ⊓ centralizer (J : Set _) := by
    rw [commutator_comm]
    exact (commutator_mono le_rfl huQa).trans hCQ
  have hCsecond : ⁅Z d.radical u,Z d.radical e⁆ ≤ centralizer (E : Set _) :=
    ((commutator_mono le_rfl heQa).trans hUQ).trans inf_le_right
  have hCcenter := (le_inf hCfirst hCsecond).trans_eq hfixers
  have hZaQ : Z d.radical a ≤ Q d.radical a := by
    apply Z_le_Q_of_dist_lt _ a (geometry.exists_critical a path.start_color)
    rw [SimpleGraph.dist_self,geometry.distance_constant a path.start_color]
    change 0 < geometry.b d.radical
    omega
  exact le_inf (hCcenter.trans (inf_le_left.trans hZaQ))
    ((hCcenter.trans inf_le_right).trans (centralizer_le (Ltilde_le_stabilizer a)))

/-- A genuinely large actual backward image in this same equal-small
configuration forces fixedness of the original radius. -/
theorem Input.replacement_distance_four_equal_small_large_radius_fixed
    {geometry : Geometry d.radical} {a z u w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical a)
    (hyu : act d.radical y (path.walk.getVert 2)=u)
    (hyw : act d.radical y (path.walk.getVert 1)=w)
    (hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1))
        (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) :
          Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F^2)
    (hfixers : (Z d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hlarge : Nat.card F^2 ≤ (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)) :
    ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a := by
  let e := path.walk.getVert 2
  let C := ⁅Z d.radical u,Z d.radical e⁆
  have hCD := h.replacement_distance_four_equal_small_critical_fixed d path hb
    y hy hyu hyw hequal hJm hfixers
  have hl : path.walk.length=4 := path.length_eq_b.trans hb
  have hae : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hea : (cosetGraph d.radical).dist e a=2 := by rw [SimpleGraph.dist_comm,hae]
  have hya : act d.radical y a=a := hy
  have hua : (cosetGraph d.radical).dist u a=2 := by
    calc
      (cosetGraph d.radical).dist u a =
          (cosetGraph d.radical).dist (act d.radical y e) (act d.radical y a) := by
        rw [hya,hyu]
      _ = (cosetGraph d.radical).dist e a := dist_act d.radical y e a
      _ = 2 := hea
  have huV : Z d.radical u ≤ V d.radical a :=
    le_iSup_of_le u (le_iSup_of_le hua.le le_rfl)
  have heV : Z d.radical e ≤ V d.radical a :=
    le_iSup_of_le e (le_iSup_of_le hea.le le_rfl)
  have hCX : C ≤ X d.radical a := (commutator_mono huV heV).trans
    (h.replacement_radius_commutator_bounds d geometry (by omega) path.start_color u e).1
  have hQC : Q d.radical a ≤ centralizer (C : Set (FreeAmalgam d.radical)) :=
    (Q_le_centralizer_X d.radical a).trans (centralizer_le hCX)
  have hseed : ⁅Z d.radical e,Q d.radical a⁆ ≤ C := by
    by_contra hbad
    have hs := h.replacement_critical_index_lt_square_of_escape d back (by omega)
      (Q d.radical a) (Q_le_stabilizer_of_dist_two d.radical a e path.start_color hae)
      hQC hbad
    exact (not_lt_of_ge hlarge) hs
  exact (h.replacement_distance_four_midpoint_fixed_iff_radius_fixed_of_large_path
    d path hb back hlarge).mp (hseed.trans hCD)

/-- In the nonfixed branch the actual equal-small selector has reciprocal
root images. The retained actor and both full seed indices are unchanged. -/
theorem Input.replacement_distance_four_equal_small_nonfixed_backward_root
    {geometry : Geometry d.radical} {a z u w : Vertex d.radical}
    (path : CriticalPath d.radical geometry a z) (hb : geometry.b d.radical=4)
    (y : FreeAmalgam d.radical) (hy : y ∈ stabilizer d.radical a)
    (hyu : act d.radical y (path.walk.getVert 2)=u)
    (hyw : act d.radical y (path.walk.getVert 1)=w)
    (hequal : Subgroup.SmallMover.join (U d.radical (path.walk.getVert 2))
        (Q d.radical (path.walk.getVert 2)) (Q d.radical (path.walk.getVert 1))
        (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2))
    (hJm : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) :
          Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F^2)
    (hfixers : (Z d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (path.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)))
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hnot : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a) :
    (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
      (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F := by
  have hsmall : (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)<Nat.card F^2 := by
    by_contra hlarge
    exact hnot (h.replacement_distance_four_equal_small_large_radius_fixed d path hb
      y hy hyu hyw hequal hJm hfixers back (Nat.le_of_not_gt hlarge))
  exact h.replacement_small_critical_indices_eq_field d back (by omega) hsmall

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
