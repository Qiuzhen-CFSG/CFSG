module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRetainedEqualFullComparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourEqualSmallSeedIntersection
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalizedRootBudget
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourFullFixedComparison
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourKernelNormality
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourNormalSpans
import all CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.UnequalTerminalPaths

/-!
# Normalization of the full far kernel by the retained root actors

The two actual equal-small fixed identities imply full comparison. The same
comparison normalizes the full kernel join under its original endpoint.
Transport through the retained twist preserves the original fixed identity
because the literal two-seed intersection is normalized. Thus both prescribed
endpoints normalize one unchanged full kernel join. The actual far mover and
the retained two-root generation then give its seed budget without radius
fixedness, a strict backward image, or deletion of an endpoint generator.

Source: MS93 (5.12)(1), (3), printed pp.924--927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
open CFSG.Quasithin.ChapterC.Sp4Four.DistanceReduction
open CFSG.Quasithin.ChapterC.Sp4Four.SourceComparison
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- The literal endpoint normalizes the full selected kernel join using both
retained original-versus-selected fixed identities. -/
theorem Input.replacement_distance_four_retained_equal_kernel_normalized
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
    Z d.radical (path.walk.getVert 2) ≤ normalizer
      (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
  have hl : back.walk.length=4 := back.length_eq_b.trans hb
  have huw : Adjacent d.radical u w := by
    rw [←hfirst]
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by omega : 0<back.walk.length))
  have haw : Adjacent d.radical a w := by
    rw [←hmid,←hfirst]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by omega : 1<back.walk.length)))
  have hyu : act d.radical y u=u := hy
  have hus : Adjacent d.radical u s := by
    rw [←hyu,←hys]
    exact (adjacent_act_iff d.radical y _ _).mpr huw
  have hvs : Adjacent d.radical v s := by
    rw [←hya,←hys]
    exact (adjacent_act_iff d.radical y _ _).mpr haw
  let W := Z d.radical v ⊓ Q d.radical a
  let e := path.walk.getVert 2
  have hcompare := h.replacement_distance_four_retained_equal_full_comparison d path hb
    r hr hru hrw hequal hJm hfixa back hfirst hmid y hy hya hys hfixu
  have hAn := (full_comparison_actor h d path hb back hus hvs).2.2.2.2
  have hAW : ⁅W,X d.radical e ⊓ Q d.radical u⁆ ≤ W :=
    le_normalizer_iff_commutator_le_left.mp hAn
  have hR : ⁅Z d.radical u,Z d.radical e⁆ ≤ Z d.radical u :=
    critical_commutator_le_start_seed back
  have hEW : ⁅Z d.radical e,W⁆ ≤ W ⊔ Z d.radical u := by
    rw [commutator_comm]
    exact hcompare.trans (sup_le (hR.trans le_sup_right) (hAW.trans le_sup_left))
  have hEu : ⁅Z d.radical e,Z d.radical u⁆ ≤ W ⊔ Z d.radical u := by
    rw [commutator_comm]
    exact hR.trans le_sup_right
  exact normalizes_join_of_commutators (Z d.radical e) W (Z d.radical u) hEW hEu

/-- Both retained endpoints and the same far mover normalize the full kernel
join. The actual far critical root index gives the original full-seed budget. -/
theorem Input.replacement_distance_four_retained_root_pair_kernel_budget
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
      Z d.radical u ⊓ centralizer (stabilizer d.radical u : Set (FreeAmalgam d.radical)))
    (k : FreeAmalgam d.radical) (hk : k ∈ stabilizer d.radical a)
    (hmove : Nat.card F < (B d.radical a (geometry.Z_normal a)).relIndex
      (U d.radical (path.walk.getVert 2)))
    (hkn : k ∈ normalizer ((Z d.radical a ⊓ Z d.radical (path.walk.getVert 2) :
      Subgroup (FreeAmalgam d.radical)) : Set _))
    (companion : CriticalPath d.radical geometry u (act d.radical k (path.walk.getVert 2)))
    (hcfirst : companion.walk.getVert 1=w) (hcmid : companion.walk.getVert 2=a)
    (next : CriticalPath d.radical geometry v a) (hnextfirst : next.walk.getVert 1=s)
    (hnot : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hgen : (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical s) (Nat.card F^2) ⊔ Z d.radical (path.walk.getVert 2)) ⊔
        Z d.radical (act d.radical k (path.walk.getVert 2))=stabilizer d.radical u) :
    stabilizer d.radical u ≤ normalizer
      (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _) ∧
    (Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u ≤
      B d.radical u (geometry.Z_normal u) ∧
    (B d.radical u (geometry.Z_normal u)).relIndex (Z d.radical a) ≤ Nat.card F := by
  have hka : act d.radical k a=a := hk
  have hra : act d.radical r a=a := hr
  have hl : path.walk.length=4 := path.length_eq_b.trans hb
  let e := path.walk.getVert 2
  let t := path.walk.getVert 1
  have hE := h.replacement_distance_four_retained_equal_kernel_normalized d path hb
    r hr hru hrw hequal hJm hfixa back hfirst hmid y hy hya hys hfixu
  let p₀ := path.act k
  let p : CriticalPath d.radical geometry a (act d.radical k z) := {
    start_color := path.start_color
    walk := p₀.walk.copy hka rfl
    shortest := by
      rw [SimpleGraph.Walk.length_copy]
      exact p₀.shortest.trans (congrArg
        (fun b => (cosetGraph d.radical).dist b (act d.radical k z)) hka)
    critical := by simpa only [hka] using p₀.critical }
  have hp (i : ℕ) : p.walk.getVert i=act d.radical k (path.walk.getVert i) := by
    change (p₀.walk.copy hka rfl).getVert i=_
    rw [SimpleGraph.Walk.getVert_copy]
    exact actWalk_getVert d.radical k path.walk i
  let rk := k⁻¹*r
  have hrk : rk ∈ stabilizer d.radical a :=
    (stabilizer d.radical a).mul_mem ((stabilizer d.radical a).inv_mem hk) hr
  have hrku : act d.radical rk (p.walk.getVert 2)=u := by
    rw [hp]
    dsimp only [rk]
    rw [←act_mul,mul_inv_cancel_left]
    exact hru
  have hrkw : act d.radical rk (p.walk.getVert 1)=w := by
    rw [hp]
    dsimp only [rk]
    rw [←act_mul,mul_inv_cancel_left]
    exact hrw
  have hequalK : Subgroup.SmallMover.join (U d.radical (p.walk.getVert 2))
        (Q d.radical (p.walk.getVert 2)) (Q d.radical (p.walk.getVert 1))
        (Nat.card F^2) =
      Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (p.walk.getVert 1)) (Nat.card F^2) := by
    rw [hp,hp,mover_act,hequal]
    have hh := mover_act (Nat.card F^2) k a (path.walk.getVert 1)
    simpa only [hka] using hh.symm
  have hJmK : (centralizer (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
        (Q d.radical (p.walk.getVert 1)) (Nat.card F^2) :
          Set (FreeAmalgam d.radical))).relIndex (U d.radical a) ≤ Nat.card F^2 := by
    rw [hp]
    have hh := own_index_act (Nat.card F^2) k a (path.walk.getVert 1)
    rw [hka] at hh
    rw [hh]
    exact hJm
  let J := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical t) (Nat.card F^2)
  let Jk := Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
    (Q d.radical (p.walk.getVert 1)) (Nat.card F^2)
  let f := (MulAut.conj k⁻¹).toMonoidHom
  have hat : Adjacent d.radical a t := by
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (path.walk.adj_getVert_succ (by omega : 0<path.walk.length))
  have het : Adjacent d.radical e t := adjacent_symm d.radical
    ((cosetGraph_adj d.radical _ _).mp (path.walk.adj_getVert_succ (by omega : 1<path.walk.length)))
  have hI : Z d.radical a ⊓ Z d.radical e=Z d.radical a ⊓ centralizer
      (J : Set (FreeAmalgam d.radical)) :=
    h.replacement_distance_four_equal_small_seed_intersection d geometry hb path.start_color
      hat het hequal hmove hJm
  have hImap : (Z d.radical a ⊓ Z d.radical e).map f=Z d.radical a ⊓ Z d.radical e :=
    mem_normalizer_iff_map_conj_eq.mp ((normalizer _).inv_mem hkn)
  have hZmap : (Z d.radical a).map f=Z d.radical a := by rw [←Z_act,hka]
  have hJmap : J.map f=Jk := by
    change (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
      (Q d.radical t) (Nat.card F^2)).map f=Jk
    dsimp only [Jk]
    rw [hp]
    have hh := mover_act (Nat.card F^2) k a t
    simpa only [hka] using hh.symm
  have hfixedK : Z d.radical a ⊓ centralizer (Jk : Set (FreeAmalgam d.radical))=
      Z d.radical a ⊓ centralizer (J : Set (FreeAmalgam d.radical)) := by
    have hh := congrArg (Subgroup.map f) hI
    rw [hImap,map_inf _ _ _ (MulAut.conj k⁻¹).injective,hZmap,
      Theory.GroupTheory.map_centralizer_equiv] at hh
    change Z d.radical a ⊓ Z d.radical e=Z d.radical a ⊓ centralizer
      ((J.map f : Subgroup (FreeAmalgam d.radical)) : Set _) at hh
    rw [hJmap] at hh
    exact hh.symm.trans hI
  have hfixaK : (Z d.radical a ⊓ centralizer
        (Subgroup.SmallMover.join (U d.radical a) (Q d.radical a)
          (Q d.radical (p.walk.getVert 1)) (Nat.card F^2) : Set (FreeAmalgam d.radical))) ⊓
        centralizer (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
          (Q d.radical w) (Nat.card F^2) : Set (FreeAmalgam d.radical)) =
      Z d.radical a ⊓ centralizer (stabilizer d.radical a : Set (FreeAmalgam d.radical)) := by
    change (Z d.radical a ⊓ centralizer (Jk : Set (FreeAmalgam d.radical))) ⊓ _=_
    rw [hfixedK]
    exact hfixa
  let companion' : CriticalPath d.radical geometry u (p.walk.getVert 2) := {
    start_color := companion.start_color
    walk := companion.walk.copy rfl (hp 2).symm
    shortest := by rw [SimpleGraph.Walk.length_copy,hp]; exact companion.shortest
    critical := by simpa only [hp] using companion.critical }
  have hcfirst' : companion'.walk.getVert 1=w := by
    change (companion.walk.copy rfl (hp 2).symm).getVert 1=w
    rwa [SimpleGraph.Walk.getVert_copy]
  have hcmid' : companion'.walk.getVert 2=a := by
    change (companion.walk.copy rfl (hp 2).symm).getVert 2=a
    rwa [SimpleGraph.Walk.getVert_copy]
  have hEk := h.replacement_distance_four_retained_equal_kernel_normalized d p hb
    rk hrk hrku hrkw hequalK hJmK hfixaK companion' hcfirst' hcmid'
    y hy hya hys hfixu
  rw [hp] at hEk
  have hbl : back.walk.length=4 := back.length_eq_b.trans hb
  have huw : Adjacent d.radical u w := by
    rw [←hfirst]
    simpa only [SimpleGraph.Walk.getVert_zero] using (cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by omega : 0<back.walk.length))
  have haw : Adjacent d.radical a w := by
    rw [←hmid,←hfirst]
    exact adjacent_symm d.radical ((cosetGraph_adj d.radical _ _).mp
      (back.walk.adj_getVert_succ (by omega : 1<back.walk.length)))
  have hyu : act d.radical y u=u := hy
  have hus : Adjacent d.radical u s := by
    rw [←hyu,←hys]
    exact (adjacent_act_iff d.radical y _ _).mpr huw
  have hvs : Adjacent d.radical v s := by
    rw [←hya,←hys]
    exact (adjacent_act_iff d.radical y _ _).mpr haw
  have hbackequal : Subgroup.SmallMover.join (U d.radical (back.walk.getVert 2))
      (Q d.radical (back.walk.getVert 2)) (Q d.radical (back.walk.getVert 1))
      (Nat.card F^2)=Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
        (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) := by
    rw [hmid,hfirst]
    have hh := congrArg (Subgroup.map (MulAut.conj r⁻¹).toMonoidHom) hequal
    rw [←mover_act,←mover_act,hru,hrw,hra] at hh
    exact hh.symm
  have hbackmove : (centralizer (Subgroup.SmallMover.join (U d.radical u)
      (Q d.radical u) (Q d.radical (back.walk.getVert 1)) (Nat.card F^2) :
      Set (FreeAmalgam d.radical))).relIndex (U d.radical u) ≤ Nat.card F^2 := by
    rw [hfirst]
    have hh := own_index_act (Nat.card F^2) r a (path.walk.getVert 1)
    rw [hra,hrw] at hh
    exact (own_index_neighbors (Nat.card F^2) huw haw).symm.trans_le (hh.trans_le hJm)
  have hnotu : ¬ ⁅V d.radical u,Q d.radical u⁆ ≤ fixedCore d.radical u := by
    intro hfu
    exact hnot (radius_fixed_at d back.start_color path.start_color hfu)
  let next' : CriticalPath d.radical geometry v (back.walk.getVert 2) := {
    start_color := next.start_color
    walk := next.walk.copy rfl hmid.symm
    shortest := by rw [SimpleGraph.Walk.length_copy,hmid]; exact next.shortest
    critical := by simpa only [hmid] using next.critical }
  have hroot := (h.replacement_distance_four_equal_small_nonfixed_backward_root d (u := v) (w := s) back hb
    y hy (by rw [hmid]; exact hya) (by rw [hfirst]; exact hys)
    hbackequal hbackmove (by simpa only [hfirst] using hfixu) next' hnotu).1
  rw [hmid] at hroot
  have hJ : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical s) (Nat.card F^2)=Subgroup.SmallMover.join (U d.radical u)
        (Q d.radical u) (Q d.radical s) (Nat.card F^2) := by
    have hh := congrArg (Subgroup.map (MulAut.conj y⁻¹).toMonoidHom) hbackequal
    rw [hmid,hfirst,←mover_act,←mover_act,hya,hys,hyu] at hh
    exact hh
  have hJW : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical s) (Nat.card F^2) ≤ normalizer
      ((Z d.radical v ⊓ Q d.radical a : Subgroup (FreeAmalgam d.radical)) : Set _) := by
    have hh := unequal_first_mover_normalizes_critical_kernel h d next (by omega) hroot
    simpa only [hnextfirst] using hh
  have hJS : Subgroup.SmallMover.join (U d.radical v) (Q d.radical v)
      (Q d.radical s) (Nat.card F^2) ≤ stabilizer d.radical u :=
    (Subgroup.SmallMover.join_le _ _ _ _).trans
      (fun _ hx => hx.2 u (adjacent_symm _ hus))
  have hJn := (le_inf hJW (hJS.trans (Z_normalized d.radical u))).trans
    (normalizer_inf_normalizer_le_normalizer_sup _ _)
  rw [hJ] at hJn
  have hn : stabilizer d.radical u ≤ normalizer
      (((Z d.radical v ⊓ Q d.radical a) ⊔ Z d.radical u :
        Subgroup (FreeAmalgam d.radical)) : Set _) := by
    rw [←hgen]
    exact sup_le (sup_le hJn hE) hEk
  have hbudget := h.replacement_distance_four_normalized_neighbor_kernel_budget d
    geometry hb back.start_color hus hvs ((Ltilde_le_stabilizer u).trans hn)
  have hselected := h.replacement_distance_four_normalized_selected_seed_budget d
    geometry hb back.start_color hus hvs y hy hya ((Ltilde_le_stabilizer u).trans hn)
  exact ⟨hn,hbudget.1,hselected.trans_eq hroot⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
