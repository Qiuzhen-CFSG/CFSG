module

public import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
public import Mathlib.Data.Fintype.EquivFin

/-!
# Five pairs around a point of the 27-point quadrangle

Adjacent vertices have a unique common neighbor. Consequently the ten
neighbors of a fixed point split into five disjoint pairs. A chosen
nonneighbor orients these pairs; every other nonneighbor selects exactly
one endpoint of each pair. The unique common-neighbor operation constructs
an adjacent nonneighbor with exactly four choices reversed.

This is the structural coordinate step for the SRG(27,10,1,5) recognition
used by Aschbacher–Smith F.4.24 in the U₄(2) branch. No graph-classification
or coordinate certificate is assumed.
-/

public section

open SimpleGraph
namespace Theory.Combinatorics.QuadrangleTwentySeven
variable {V:Type*} [Fintype V] (Γ:SimpleGraph V) [DecidableRel Γ.Adj]

abbrev Near (x:V) := Γ.neighborSet x
abbrev Far (x:V) := Γᶜ.neighborSet x

variable {Γ}

theorem near_card (h:Γ.IsSRGWith 27 10 1 5) (x:V) : Fintype.card (Near Γ x)=10 := by
  rw [card_neighborSet_eq_degree,h.regular.degree_eq]

theorem far_card [DecidableEq V] (h:Γ.IsSRGWith 27 10 1 5) (x:V) : Fintype.card (Far Γ x)=16 := by
  classical
  rw [card_neighborSet_eq_degree,h.compl.regular.degree_eq]

theorem common_unique (h:Γ.IsSRGWith 27 10 1 5) {a b c d:V} (hab:Γ.Adj a b)
    (hac:Γ.Adj a c) (hbc:Γ.Adj b c) (had:Γ.Adj a d) (hbd:Γ.Adj b d) : c=d := by
  obtain ⟨z,hz⟩ := Fintype.card_eq_one_iff.mp (h.of_adj a b hab)
  exact congrArg Subtype.val ((hz ⟨c,hac,hbc⟩).trans (hz ⟨d,had,hbd⟩).symm)

theorem exists_common (h:Γ.IsSRGWith 27 10 1 5) {a b:V} (hab:Γ.Adj a b) :
    ∃c,Γ.Adj a c ∧Γ.Adj b c := by
  obtain ⟨z,_⟩ := Fintype.card_eq_one_iff.mp (h.of_adj a b hab)
  exact ⟨z,z.property⟩

private noncomputable def mate (h:Γ.IsSRGWith 27 10 1 5) {x:V} (u:Near Γ x) : Near Γ x :=
  ⟨Classical.choose (exists_common h u.property),
    (Classical.choose_spec (exists_common h u.property)).1⟩

private theorem mate_adj (h:Γ.IsSRGWith 27 10 1 5) {x:V} (u:Near Γ x) :
    Γ.Adj u.val (mate h u).val := (Classical.choose_spec (exists_common h u.property)).2

private theorem mate_involutive (h:Γ.IsSRGWith 27 10 1 5) {x:V} : Function.Involutive (@mate V _ Γ _ h x) := by
  intro u
  apply Subtype.ext
  exact common_unique h (mate h u).property (mate h (mate h u)).property
    (mate_adj h (mate h u)) u.property (mate_adj h u).symm

private theorem mate_not_adj (h:Γ.IsSRGWith 27 10 1 5) {x y:V} (hy:Γᶜ.Adj x y)
    (u:Near Γ x) (huy:Γ.Adj y u.val) : ¬Γ.Adj y (mate h u).val := by
  intro hh
  have he := common_unique h (mate_adj h u) u.property.symm (mate h u).property.symm huy.symm hh.symm
  exact hy.1 he

structure Frame (x y:V) where
  equiv : (Fin 5 × Bool) ≃ Near Γ x
  selected : ∀i,Γ.Adj y (equiv (i,false)).val
  paired : ∀i,Γ.Adj (equiv (i,false)).val (equiv (i,true)).val

noncomputable def frame (h:Γ.IsSRGWith 27 10 1 5) {x y:V} (hy:Γᶜ.Adj x y) : Frame (Γ:=Γ) x y := by
  classical
  let e:Fin 5≃Γ.commonNeighbors x y := (Fintype.equivFinOfCardEq (h.of_not_adj hy.1 hy.2)).symm
  let c (i:Fin 5):Near Γ x := ⟨(e i).val,(e i).property.1⟩
  let f:Fin 5×Bool→Near Γ x := fun (i,b)=>if b then mate h (c i) else c i
  have hc (i:Fin 5) : Γ.Adj y (c i).val := (e i).property.2
  have hi:Function.Injective f := by
    rintro ⟨i,b⟩ ⟨j,d⟩ he
    have hcinj : Function.Injective c := by
      intro i j hij
      apply e.injective
      exact Subtype.ext (congrArg (fun v:Near Γ x=>v.val) hij)
    cases b <;> cases d
    · have hij : i=j := hcinj he
      exact Prod.ext hij rfl
    · have hh : Γ.Adj y (mate h (c j)).val := (congrArg Subtype.val he) ▸ hc i
      exact (mate_not_adj h hy (c j) (hc j) hh).elim
    · have hh : Γ.Adj y (mate h (c i)).val := (congrArg Subtype.val he).symm ▸ hc j
      exact (mate_not_adj h hy (c i) (hc i) hh).elim
    · have hij : i=j := hcinj ((mate_involutive h).injective he)
      exact Prod.ext hij rfl
  have hb:Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hi,by rw [near_card h]; decide⟩
  exact ⟨Equiv.ofBijective f hb,hc,fun i=>mate_adj h (c i)⟩

namespace Frame
variable {x y:V} (D:Frame (Γ:=Γ) x y)
@[expose] def point (i:Fin 5) (b:Bool) : V := (D.equiv (i,b)).val

omit [Fintype V] [DecidableRel Γ.Adj] in
theorem near (i:Fin 5) (b:Bool) : Γ.Adj x (D.point i b) := (D.equiv (i,b)).property

omit [Fintype V] [DecidableRel Γ.Adj] in
theorem point_injective : Function.Injective (fun p:Fin 5×Bool=>D.point p.1 p.2) :=
  Subtype.val_injective.comp D.equiv.injective

omit [Fintype V] [DecidableRel Γ.Adj] in
theorem paired' (i:Fin 5) (b:Bool) : Γ.Adj (D.point i b) (D.point i (!b)) := by
  cases b
  · exact D.paired i
  · exact (D.paired i).symm

theorem adj_points_iff (h:Γ.IsSRGWith 27 10 1 5) (i j:Fin 5) (b c:Bool) :
    Γ.Adj (D.point i b) (D.point j c) ↔ i=j ∧ b≠c := by
  constructor
  · intro ha
    have he := common_unique h (D.near i b) (D.near j c) ha
      (D.near i (!b)) (D.paired' i b)
    have hp : (j,c)=(i,!b) := D.point_injective he
    have hi := congrArg Prod.fst hp
    have hc := congrArg Prod.snd hp
    change j=i at hi
    change c=(!b) at hc
    exact ⟨hi.symm,by rw [hc];cases b <;> decide⟩
  · rintro ⟨rfl,hb⟩
    cases b <;> cases c <;> first | contradiction | exact D.paired i | exact (D.paired i).symm

omit [Fintype V] [DecidableRel Γ.Adj] in
theorem near_cases {v:V} (hv:Γ.Adj x v) : ∃i b,D.point i b=v := by
  obtain ⟨⟨i,b⟩,he⟩ := D.equiv.surjective ⟨v,hv⟩
  exact ⟨i,b,congrArg Subtype.val he⟩

theorem not_both (h:Γ.IsSRGWith 27 10 1 5) (z:Far Γ x) (i:Fin 5) :
    ¬(Γ.Adj z.val (D.point i false) ∧Γ.Adj z.val (D.point i true)) := by
  rintro ⟨hz0,hz1⟩
  exact z.property.1 (common_unique h (D.paired i) (D.near i false).symm
    (D.near i true).symm hz0.symm hz1.symm)

theorem existsUnique_selected (h:Γ.IsSRGWith 27 10 1 5) (z:Far Γ x) (i:Fin 5) :
    ∃!b:Bool,Γ.Adj z.val (D.point i b) := by
  classical
  let C:=Γ.commonNeighbors x z.val
  let k:C→Fin 5 := fun w=>(D.equiv.symm ⟨w.val,w.property.1⟩).1
  have hk:Function.Injective k := by
    intro a b hab
    have ha := D.equiv.apply_symm_apply ⟨a.val,a.property.1⟩
    have hb := D.equiv.apply_symm_apply ⟨b.val,b.property.1⟩
    let qa := D.equiv.symm ⟨a.val,a.property.1⟩
    let qb := D.equiv.symm ⟨b.val,b.property.1⟩
    have hq : qa.1=qb.1 := hab
    by_cases he : qa.2=qb.2
    · apply Subtype.ext
      exact congrArg (fun w:Near Γ x=>w.val) (ha.symm.trans ((congrArg D.equiv (Prod.ext hq he)).trans hb))
    · have hadj : Γ.Adj a.val b.val := by
        rw [←congrArg Subtype.val ha,←congrArg Subtype.val hb]
        exact (D.adj_points_iff h _ _ _ _).mpr ⟨hq,he⟩
      exact (z.property.1 (common_unique h hadj a.property.1.symm b.property.1.symm
        a.property.2.symm b.property.2.symm)).elim
  have hs:Function.Surjective k := ((Fintype.bijective_iff_injective_and_card k).mpr
    ⟨hk,by change Fintype.card (Γ.commonNeighbors x z.val)=_;rw [h.of_not_adj z.property.1 z.property.2];rfl⟩).2
  obtain ⟨w,hw⟩ := hs i
  let q:=D.equiv.symm ⟨w.val,w.property.1⟩
  have hqi:q.1=i := hw
  have hqw:D.point i q.2=w.val := by
    rw [←hqi]
    exact congrArg Subtype.val (D.equiv.apply_symm_apply ⟨w.val,w.property.1⟩)
  have hqz : Γ.Adj z.val (D.point i q.2) := by rw [hqw];exact w.property.2
  refine ⟨q.2,hqz,?_⟩
  intro b hb
  by_contra he
  have hq := hqz
  have hn:=D.not_both h z i
  cases b <;> cases heq:q.2 <;> simp_all
noncomputable def label (h:Γ.IsSRGWith 27 10 1 5) (z:Far Γ x) : Fin 5→Bool :=
  fun i=>Classical.choose (D.existsUnique_selected h z i)

theorem label_adj (h:Γ.IsSRGWith 27 10 1 5) (z:Far Γ x) (i:Fin 5) :
    Γ.Adj z.val (D.point i (D.label h z i)) :=
  (Classical.choose_spec (D.existsUnique_selected h z i)).1

theorem label_eq_of_adj (h:Γ.IsSRGWith 27 10 1 5) (z:Far Γ x) (i:Fin 5) (b:Bool)
    (hb:Γ.Adj z.val (D.point i b)) : D.label h z i=b :=
  ((Classical.choose_spec (D.existsUnique_selected h z i)).2 b hb).symm

theorem adj_point_iff_label (h:Γ.IsSRGWith 27 10 1 5) (z:Far Γ x) (i:Fin 5) (b:Bool) :
    Γ.Adj z.val (D.point i b) ↔ D.label h z i=b := by
  constructor
  · exact D.label_eq_of_adj h z i b
  · intro hb;rw [←hb];exact D.label_adj h z i

theorem label_base (h:Γ.IsSRGWith 27 10 1 5) (hy:Γᶜ.Adj x y) :
    D.label h ⟨y,hy⟩=fun _=>false := by
  funext i
  exact D.label_eq_of_adj h ⟨y,hy⟩ i false (D.selected i)

theorem exists_flip_neighbor (h:Γ.IsSRGWith 27 10 1 5) (z:Far Γ x) (i:Fin 5) :
    ∃w:Far Γ x,Γ.Adj z.val w.val ∧
      D.label h w=fun j=>if j=i then D.label h z j else !(D.label h z j) := by
  classical
  let b:=D.label h z i
  obtain ⟨w,hzw,hpw⟩ := exists_common h (D.label_adj h z i)
  have hxw:x≠w := by
    intro he
    apply z.property.2
    exact he ▸ hzw.symm
  have hnw:¬Γ.Adj x w := by
    intro hw
    have he:w=D.point i (!b) := common_unique h (D.near i b) hw hpw
      (D.near i (!b)) (D.paired' i b)
    have hh:Γ.Adj z.val (D.point i (!b)) := he ▸ hzw
    have heq := D.label_eq_of_adj h z i (!b) hh
    change b=(!b) at heq
    exact (Bool.self_ne_not b) heq
  let q:Far Γ x:=⟨w,hxw,hnw⟩
  refine ⟨q,hzw,?_⟩
  funext j
  by_cases hj:j=i
  · subst j
    rw [if_pos rfl]
    exact D.label_eq_of_adj h q i b hpw.symm
  · rw [if_neg hj]
    have hn:D.label h q j≠D.label h z j := by
      intro heq
      have he:=common_unique h hzw (D.label_adj h z i) hpw.symm
        (D.label_adj h z j) (by rw [←heq];exact D.label_adj h q j)
      have hp : (i,D.label h z i)=(j,D.label h z j) := D.point_injective he
      have hij : i=j := congrArg Prod.fst hp
      exact hj hij.symm
    cases hq:D.label h q j <;> cases hz:D.label h z j <;> simp_all
end Frame
end Theory.Combinatorics.QuadrangleTwentySeven
