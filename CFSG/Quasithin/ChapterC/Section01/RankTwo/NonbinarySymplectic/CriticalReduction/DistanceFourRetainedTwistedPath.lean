module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.CriticalReduction.DistanceFourRetainedTwistedEscape

/-!
# The actual companion path for the retained twist

Directed escape makes the same selected full seed critical against the
midpoint transported by the retained twist. Triangle bounds give distance
four. The full two-seed intersection normalized by this twist transports
the original fixed-space certificate, while the selected mover is unchanged.
Nonfixedness then gives reciprocal field-sized indices on the companion,
as on the original backward path. No additional selector is chosen.
Source: MS93 (5.12)(3), printed p.927.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
private theorem mover_act {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (y : FreeAmalgam R) (v t : Vertex R) :
    Subgroup.SmallMover.join (U R (act R y v)) (Q R (act R y v))
        (Q R (act R y t)) q =
      (Subgroup.SmallMover.join (U R v) (Q R v) (Q R t) q).map
        (MulAut.conj y⁻¹).toMonoidHom := by
  rw [U_act,Q_act,Q_act,←Subgroup.SmallMover.join_map _ (MulAut.conj y⁻¹).injective]

private theorem own_index_act {M : Type*} [Group M] [Finite M] {R : Subgroup M}
    (q : ℕ) (y : FreeAmalgam R) (v t : Vertex R) :
    (centralizer (Subgroup.SmallMover.join (U R (act R y v)) (Q R (act R y v))
      (Q R (act R y t)) q : Set (FreeAmalgam R))).relIndex (U R (act R y v)) =
      (centralizer (Subgroup.SmallMover.join (U R v) (Q R v)
        (Q R t) q : Set (FreeAmalgam R))).relIndex (U R v) := by
  rw [mover_act,U_act,Subgroup.SmallMover.centralizer_index_map _ (MulAut.conj y⁻¹).injective]

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} (h : Input K R n F)
variable (d : CharacteristicReduction K R)
include h

/-- Directed escape yields an actual companion for the same twist, with
both original and twisted reciprocal full-seed indices equal to the field
order. No first-edge or overlapping-walk clause is imposed on this companion. -/
theorem Input.replacement_distance_four_retained_twisted_path
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
      Subgroup (FreeAmalgam d.radical)) : Set _))
    (back : CriticalPath d.radical geometry u (path.walk.getVert 2))
    (hfirst : back.walk.getVert 1=w)
    (hnot : ¬ ⁅V d.radical a,Q d.radical a⁆ ≤ fixedCore d.radical a)
    (hgen : (Subgroup.SmallMover.join (U d.radical u) (Q d.radical u)
      (Q d.radical w) (Nat.card F^2) ⊔ Z d.radical z) ⊔
        Z d.radical (act d.radical k z)=stabilizer d.radical a) :
    (¬ Z d.radical u ⊓ Q d.radical (path.walk.getVert 2) ≤
      Z d.radical u ⊓ Q d.radical (act d.radical k (path.walk.getVert 2))) ∧
    (Q d.radical (path.walk.getVert 2)).relIndex (Z d.radical u)=Nat.card F ∧
    (Q d.radical u).relIndex (Z d.radical (path.walk.getVert 2))=Nat.card F ∧
    ∃ _companion : CriticalPath d.radical geometry u
      (act d.radical k (path.walk.getVert 2)),
      (Q d.radical (act d.radical k (path.walk.getVert 2))).relIndex
        (Z d.radical u)=Nat.card F ∧
      (Q d.radical u).relIndex
        (Z d.radical (act d.radical k (path.walk.getVert 2)))=Nat.card F := by
  have hescape := h.replacement_distance_four_retained_twisted_kernel_not_le d path hb
    r k hr hk hru hrw hequal hJm hmove hfixa hterminal hterminalmove hfixe hkn
    back hfirst hnot hgen
  obtain ⟨hroot,hroot'⟩ := h.replacement_distance_four_equal_small_nonfixed_backward_root d
    path hb r hr hru hrw hequal hJm hfixa back hnot
  let e := path.walk.getVert 2
  let t := path.walk.getVert 1
  have hka : act d.radical k a=a := hk
  have hra : act d.radical r a=a := hr
  have hl : path.walk.length=4 := path.length_eq_b.trans hb
  have hcritical : ¬ Z d.radical u ≤ Q d.radical (act d.radical k e) := by
    intro hh
    exact hescape (le_inf inf_le_left (inf_le_left.trans hh))
  have hmin := criticalDistance_le d.radical u
    (geometry.exists_critical u back.start_color) hcritical
  have hae : (cosetGraph d.radical).dist a e=2 := path.dist_start (by omega)
  have hua : (cosetGraph d.radical).dist u a=2 := by
    calc
      (cosetGraph d.radical).dist u a =
          (cosetGraph d.radical).dist (act d.radical r e) (act d.radical r a) := by
        rw [hra,hru]
      _ = (cosetGraph d.radical).dist e a := dist_act d.radical r e a
      _ = 2 := by rw [SimpleGraph.dist_comm]; exact hae
  have hake : (cosetGraph d.radical).dist a (act d.radical k e)=2 := by
    rw [←hka,dist_act]
    exact hae
  have hupper := (cosetGraph_connected d.radical).dist_triangle (u:=u) (v:=a)
    (w:=act d.radical k e)
  rw [hua,hake] at hupper
  have hd : (cosetGraph d.radical).dist u (act d.radical k e)=
      criticalDistance d.radical u (geometry.exists_critical u back.start_color) := by
    rw [geometry.distance_constant u back.start_color] at hmin ⊢
    change geometry.b d.radical ≤ _ at hmin
    change _=geometry.b d.radical
    omega
  let companion : CriticalPath d.radical geometry u (act d.radical k e) :=
    CriticalPath.ofPair back.start_color ⟨hd,hcritical⟩
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
  let y := k⁻¹*r
  have hy : y ∈ stabilizer d.radical a :=
    (stabilizer d.radical a).mul_mem ((stabilizer d.radical a).inv_mem hk) hr
  have hyu : act d.radical y (p.walk.getVert 2)=u := by
    rw [hp]
    dsimp only [y]
    rw [←act_mul,mul_inv_cancel_left]
    exact hru
  have hyw : act d.radical y (p.walk.getVert 1)=w := by
    rw [hp]
    dsimp only [y]
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
  obtain ⟨htwist,htwist'⟩ := h.replacement_distance_four_equal_small_nonfixed_backward_root d
    p hb y hy hyu hyw hequalK hJmK hfixaK companion' hnot
  rw [hp] at htwist htwist'
  exact ⟨hescape,hroot,hroot',companion,htwist,htwist'⟩

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic
