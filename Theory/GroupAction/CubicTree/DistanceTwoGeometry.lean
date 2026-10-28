module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Distance-two forests in a tree

Suppose every neighbor of a vertex in a set `S` has exactly one other neighbor
in `S`. Joining vertices of `S` at distance two then gives a forest. Expand
each edge to its two-edge path in the original tree: unique pairing prevents
backtracking, so a reduced closed walk would give a nonempty tree path with
equal endpoints.

The same pairing and uniqueness of tree paths give a bijection of neighbor
sets. Thus cubic degree passes to this graph and each of its native connected
components. The source consumer is Goldschmidt's normalizer geometry in
*Automorphisms of trivalent graphs* (1980), Section 5, printed p.394.
-/

@[expose] public section
open SimpleGraph
namespace Theory.GroupAction.CubicTree.DistanceTwoGeometry
variable {V : Type*} (Γ : SimpleGraph V) (S : Set V)

noncomputable def graph : SimpleGraph S where
  Adj x y := Γ.dist x.val y.val = 2
  symm := ⟨fun x y h => (SimpleGraph.dist_comm (u := y.val) (v := x.val)).trans h⟩
  loopless := ⟨fun x => by simp⟩

variable {Γ S}

theorem dist_eq_two_iff (hΓ : Γ.IsTree) {x y : V} :
    Γ.dist x y = 2 ↔ x ≠ y ∧ ∃ m, Γ.Adj x m ∧ Γ.Adj m y := by
  constructor
  · intro h
    have hd : Γ.edist x y = 2 := by
      rw [← (hΓ.connected x y).coe_dist_eq_edist, h]
      rfl
    obtain ⟨hne, _, m, hm⟩ := SimpleGraph.edist_eq_two_iff.mp hd
    exact ⟨hne, m, hm.1, hm.2.symm⟩
  · rintro ⟨hne, m, hxm, hmy⟩
    let p : Γ.Walk x y := .cons hxm (.cons hmy .nil)
    have hp : p.IsPath := by
      simp [p, SimpleGraph.Walk.isPath_def, hne, hxm.ne, hmy.ne]
    obtain ⟨q, hq, hlen⟩ := (hΓ.connected x y).exists_path_of_dist
    have he : p = q := (hΓ.existsUnique_path x y).unique hp hq
    simpa [← he, p] using hlen.symm

private noncomputable def midpoint (hΓ : Γ.IsTree) {x y : S}
    (hxy : (graph Γ S).Adj x y) : V :=
  Classical.choose ((dist_eq_two_iff hΓ).mp hxy).2

private theorem midpoint_spec (hΓ : Γ.IsTree) {x y : S}
    (hxy : (graph Γ S).Adj x y) :
    Γ.Adj x.val (midpoint hΓ hxy) ∧ Γ.Adj (midpoint hΓ hxy) y.val :=
  Classical.choose_spec ((dist_eq_two_iff hΓ).mp hxy).2

private noncomputable def expand (hΓ : Γ.IsTree) :
    {x y : S} → (graph Γ S).Walk x y → Γ.Walk x.val y.val
  | _, _, .nil => .nil
  | _, _, .cons h p =>
    .cons (midpoint_spec hΓ h).1 (.cons (midpoint_spec hΓ h).2 (expand hΓ p))

private theorem expand_length (hΓ : Γ.IsTree) {x y : S}
    (p : (graph Γ S).Walk x y) : (expand hΓ p).length = 2 * p.length := by
  induction p with
  | nil => rfl
  | cons h p ih => simp [expand, ih]; omega

private theorem expand_isChain (hΓ : Γ.IsTree)
    (hpair : ∀ (x : S) (m : V), Γ.Adj x.val m →
      ∃! y : S, y.val ≠ x.val ∧ Γ.Adj m y.val)
    {x y : S} (p : (graph Γ S).Walk x y)
    (hp : List.IsChain (· ≠ ·) p.edges) :
    List.IsChain (· ≠ ·) (expand hΓ p).edges := by
  induction p with
  | nil => simp [expand]
  | @cons x y z h p ih =>
    have hxy := ((dist_eq_two_iff hΓ).mp h).1
    have hfirst : s(x.val, midpoint hΓ h) ≠ s(midpoint hΓ h, y.val) := by
      intro he
      rcases Sym2.eq_iff.mp he with he | he
      · exact (midpoint_spec hΓ h).1.ne he.1
      · exact hxy he.1
    cases p with
    | nil => simpa [expand] using hfirst
    | @cons y z w k p =>
      have hchain := List.isChain_cons_cons.mp hp
      have hmne : midpoint hΓ h ≠ midpoint hΓ k := by
        intro hm
        have he : x = z := (hpair y _ (midpoint_spec hΓ h).2.symm).unique
          ⟨hxy, (midpoint_spec hΓ h).1.symm⟩
          ⟨((dist_eq_two_iff hΓ).mp k).1.symm,
            hm.symm ▸ (midpoint_spec hΓ k).2⟩
        subst z
        exact hchain.1 Sym2.eq_swap
      have hjunction : s(midpoint hΓ h, y.val) ≠ s(y.val, midpoint hΓ k) := by
        intro he
        rcases Sym2.eq_iff.mp he with he | he
        · exact (midpoint_spec hΓ h).2.ne he.1
        · exact hmne he.1
      exact List.IsChain.cons_cons hfirst
        (List.IsChain.cons_cons hjunction (ih hchain.2))

theorem isAcyclic (hΓ : Γ.IsTree)
    (hpair : ∀ (x : S) (m : V), Γ.Adj x.val m →
      ∃! y : S, y.val ≠ x.val ∧ Γ.Adj m y.val) : (graph Γ S).IsAcyclic := by
  intro x p hp
  have hexp := (hΓ.isAcyclic.isPath_iff_isChain (expand hΓ p)).mpr
    (expand_isChain hΓ hpair p hp.isTrail.edges_nodup.isChain)
  have hlen := (hexp.nil_iff_eq.mpr rfl).length_eq_zero
  rw [expand_length] at hlen
  exact hp.not_nil (SimpleGraph.Walk.length_eq_zero_iff.mp (by omega))

theorem midpoint_unique (hΓ : Γ.IsAcyclic) {x y m n : V}
    (hxy : x ≠ y) (hxm : Γ.Adj x m) (hmy : Γ.Adj m y)
    (hxn : Γ.Adj x n) (hny : Γ.Adj n y) : m = n := by
  let p : Γ.Walk x y := .cons hxm (.cons hmy .nil)
  let q : Γ.Walk x y := .cons hxn (.cons hny .nil)
  have hp : p.IsPath := by
    simp [p, SimpleGraph.Walk.isPath_def, hxm.ne, hmy.ne, hxy]
  have hq : q.IsPath := by
    simp [q, SimpleGraph.Walk.isPath_def, hxn.ne, hny.ne, hxy]
  have hpq : p = q := Subtype.mk.inj ((hΓ.subsingleton_path x y).elim ⟨p, hp⟩ ⟨q, hq⟩)
  have he := congrArg (fun r : Γ.Walk x y => r.getVert 1) hpq
  simpa [p, q] using he

private noncomputable def neighborEquiv (hΓ : Γ.IsTree)
    (hpair : ∀ (x : S) (m : V), Γ.Adj x.val m →
      ∃! y : S, y.val ≠ x.val ∧ Γ.Adj m y.val) (x : S) :
    Γ.neighborSet x.val ≃ (graph Γ S).neighborSet x := by
  classical
  have hdist : ∀ x y : V, Γ.dist x y = 2 ↔
      x ≠ y ∧ ∃ m, Γ.Adj x m ∧ Γ.Adj m y := fun _ _ => dist_eq_two_iff hΓ
  let choose (m : Γ.neighborSet x.val) : S := (hpair x m.val m.property).choose
  have hchoose (m : Γ.neighborSet x.val) :
      (choose m).val ≠ x.val ∧ Γ.Adj m.val (choose m).val :=
    (hpair x m.val m.property).choose_spec.1
  let f (m : Γ.neighborSet x.val) : (graph Γ S).neighborSet x :=
    ⟨choose m, (hdist x.val (choose m).val).mpr
      ⟨(hchoose m).1.symm, m.val, m.property, (hchoose m).2⟩⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro m n hmn
    have he : choose m = choose n := congrArg Subtype.val hmn
    apply Subtype.ext
    exact midpoint_unique hΓ.isAcyclic (hchoose m).1.symm m.property
      (hchoose m).2 n.property (he.symm ▸ (hchoose n).2)
  · intro y
    obtain ⟨hxy, m, hxm, hmy⟩ := (hdist x.val y.val.val).mp y.property
    refine ⟨⟨m, hxm⟩, ?_⟩
    apply Subtype.ext
    exact ((hpair x m hxm).choose_spec.2 y.val ⟨hxy.symm, hmy⟩).symm

theorem card_neighborSet (hΓ : Γ.IsTree)
    (hpair : ∀ (x : S) (m : V), Γ.Adj x.val m →
      ∃! y : S, y.val ≠ x.val ∧ Γ.Adj m y.val) (x : S) :
    Nat.card ((graph Γ S).neighborSet x) = Nat.card (Γ.neighborSet x.val) :=
  Nat.card_congr (neighborEquiv hΓ hpair x).symm

theorem card_component_neighborSet (hΓ : Γ.IsTree)
    (hpair : ∀ (x : S) (m : V), Γ.Adj x.val m →
      ∃! y : S, y.val ≠ x.val ∧ Γ.Adj m y.val)
    (c : (graph Γ S).ConnectedComponent) (x : c.supp) :
    Nat.card (c.toSimpleGraph.neighborSet x) = Nat.card (Γ.neighborSet x.val.val) := by
  let e : c.toSimpleGraph.neighborSet x ≃ (graph Γ S).neighborSet x.val :=
    { toFun := fun y => ⟨y.val.val, y.property⟩
      invFun := fun y =>
        ⟨⟨y.val, c.mem_supp_of_adj_mem_supp x.property y.property⟩, y.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans (card_neighborSet hΓ hpair x.val)

end Theory.GroupAction.CubicTree.DistanceTwoGeometry
