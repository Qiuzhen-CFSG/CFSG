module

public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Hamiltonian
public import Mathlib.Data.Rat.Star
public import Mathlib.LinearAlgebra.RootSystem.BaseExists
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Theory.AlgebraicGroup.RootSystems.PositiveSubsystem

namespace Theory.AlgebraicGroup

open scoped SimpleGraph

/-! Passing to an induced subgraph can only remove neighbors. -/

public lemma simpleGraph_induce_degree_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Set V) [Fintype s] (v : s) :
    (G.induce s).degree v ≤ G.degree v := by
  classical
  let f : (G.induce s).neighborSet v → G.neighborSet v := fun w =>
    ⟨w.1.1, w.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : G.neighborSet v => (z : V)) hxy
  simpa only [SimpleGraph.card_neighborSet_eq_degree] using
    (Fintype.card_le_of_injective f hf)

open scoped SimpleGraph
open SimpleGraph

/-! Off-path leaves attached to opposite ends of a simple path cannot be
adjacent in an acyclic graph. -/

public lemma simpleGraph_isAcyclic_path_cross_offpath_nonadjacent
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v a b : V} {p : G.Walk u v} (hp : p.IsPath) (hpNil : ¬p.Nil)
    (hG : G.IsAcyclic) (ha : G.Adj u a) (hb : G.Adj v b)
    (haoff : a ∉ p.support) (hboff : b ∉ p.support) (hne : a ≠ b) :
    ¬ G.Adj a b := by
  intro hab
  have hq : (Walk.cons ha.symm (p.concat hb)).IsPath := by
    apply (Walk.cons_isPath_iff _ _).2
    refine ⟨hp.concat hboff hb, ?_⟩
    intro hmem
    simp only [Walk.support_concat, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact haoff hmem
    · exact hne (by simpa using hmem)
  let q : G.Walk a b := Walk.cons ha.symm (p.concat hb)
  have hq' : q.IsPath := by simpa [q] using hq
  have hnot : s(a, b) ∉ q.reverse.edges := by
    intro hmem
    have hmem' : s(a, b) ∈ q.edges := by
      rw [Walk.edges_reverse] at hmem
      simpa [List.mem_reverse, Sym2.eq_swap] using hmem
    have heq := hq'.eq_snd_of_mem_edges hmem'
    have hq_snd : q.snd = u := by simp [q, Walk.snd]
    have huv : b = u := by simpa [hq_snd] using heq
    exact hboff (huv ▸ p.start_mem_support)
  have hcyc : (Walk.cons hab q.reverse).IsCycle :=
    (Walk.cons_isCycle_iff q.reverse hab).2 ⟨hq'.reverse, hnot⟩
  exact hG _ hcyc

open scoped SimpleGraph
open SimpleGraph

/-! A chord of a simple path closes a cycle. -/

public lemma simpleGraph_isAcyclic_path_nonadjacent
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) (hG : G.IsAcyclic)
    {i j : Fin (p.length + 1)} (hij : i.val + 1 < j.val) :
    ¬ G.Adj (p.getVert i) (p.getVert j) := by
  intro hadj
  have hEq : (p.drop i.val).getVert (j.val - i.val) = p.getVert j.val := by
    rw [Walk.drop_getVert]
    congr 1
    omega
  let r0 := (p.drop i.val).take (j.val - i.val)
  let r : G.Walk (p.getVert i) (p.getVert j) := r0.copy rfl hEq
  have hr : r.IsPath := by
    simpa [r, r0] using (hp.drop i.val |>.take (j.val - i.val))
  have hrend : r.snd = p.getVert (i.val + 1) := by
    have hd : 1 ≤ j.val - i.val := by omega
    simp [r, r0, Walk.snd, Walk.take_getVert, Walk.drop_getVert,
      Nat.min_eq_right hd]
  have hnot : s(p.getVert i, p.getVert j) ∉ r.reverse.edges := by
    intro hmem
    have hmem' : s(p.getVert i, p.getVert j) ∈ r.edges := by
      rw [Walk.edges_reverse] at hmem
      simpa [List.mem_reverse, Sym2.eq_swap] using hmem
    have heq := hr.eq_snd_of_mem_edges hmem'
    have heq' : p.getVert j.val = p.getVert (i.val + 1) := by
      calc
        p.getVert j.val = r.snd := heq
        _ = p.getVert (i.val + 1) := hrend
    have hfalse : j.val = i.val + 1 := by
      have htmp := hp.getVert_injOn (show i.val + 1 ≤ p.length by omega)
        (show j.val ≤ p.length by omega) heq'.symm
      exact htmp.symm
    omega
  have hcyc : (Walk.cons hadj r.reverse).IsCycle :=
    (Walk.cons_isCycle_iff r.reverse hadj).2 ⟨hr.reverse, hnot⟩
  exact hG _ hcyc

open scoped SimpleGraph
open SimpleGraph

/-! An off-path neighbor of the start of a nonempty simple path cannot attach
to any later path vertex in an acyclic graph. -/

public lemma simpleGraph_isAcyclic_path_offpath_start_nonadjacent
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {u v a : V} {p : G.Walk u v} (hp : p.IsPath) (hpNil : ¬p.Nil)
    (hG : G.IsAcyclic) (ha : G.Adj u a) (haoff : a ∉ p.support)
    {j : Fin (p.length + 1)} (hj : j ≠ 0) :
    ¬ G.Adj a (p.getVert j) := by
  intro haj
  let q : G.Walk u (p.getVert j) := p.take j.val
  have hq : q.IsPath := hp.take _
  have hqend : q.getVert q.length = p.getVert j := by
    simp [q, Walk.take_getVert, show j.val ≤ p.length by omega]
  have hqj : G.Adj (p.getVert j) a := haj.symm
  have haq : a ∉ q.support := by
    intro h
    apply haoff
    have hsub : q.support ⊆ p.support := by
      intro x hx
      exact List.mem_of_mem_take (by simpa [q, Walk.support_take] using hx)
    exact hsub h
  have hqnil : ¬q.Nil := by
    intro hnil
    rcases (Walk.nil_take_iff p j.val).mp (by simpa [q] using hnil) with
      hpnil | hj0
    · exact hpNil hpnil
    · exact hj (Fin.ext hj0)
  let r : G.Walk u a := q.concat hqj
  have hr : r.IsPath := hq.concat haq hqj
  have hcyc : (Walk.cons ha.symm r).IsCycle := by
    apply (Walk.cons_isCycle_iff r ha.symm).2
    refine ⟨hr, ?_⟩
    intro hmem
    have hmem' : s(u, a) ∈ r.edges := by
      simpa [Sym2.eq_swap] using hmem
    have heq := hr.eq_snd_of_mem_edges hmem'
    have hqa : a = q.snd := by
      calc
        a = r.snd := heq
        _ = q.snd := by
          by_cases hq1 : q.length = 1
          · have hq_snd_end : q.snd = p.getVert j.val := by
              calc
                q.snd = q.getVert q.length := by simp [Walk.snd, hq1]
                _ = p.getVert j.val := hqend
            simp [r, Walk.concat_eq_append, Walk.getVert_append, hq1,
              Walk.snd, hq_snd_end]
          · have hqpos : 0 < q.length := Walk.not_nil_iff_lt_length.mp hqnil
            have hqgt : 1 < q.length := by omega
            simp [r, Walk.concat_eq_append, Walk.getVert_append, hqgt, Walk.snd]
    apply haq
    rw [hqa]
    simp [Walk.snd]
  exact hG _ hcyc

open SimpleGraph

/-- A path that spans all vertices and contains every graph edge gives a
path-graph numbering of the whole finite graph.  The premises are ordinary
spanning-path data; no Dynkin classification is stored in a structure. -/
public lemma simpleGraph_spanningPath_numbering
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (u v : V) (p : G.Walk u v)
    (hp : p.IsPath)
    (hspan : ∀ x : V, x ∈ p.support)
    (hedge : ∀ ⦃x y : V⦄, G.Adj x y → s(x, y) ∈ p.edges) :
    ∃ n : ℕ, ∃ e : Fin n ≃ V,
      ∀ i j, G.Adj (e i) (e j) ↔ (pathGraph n).Adj i j := by
  classical
  let hsurj : Function.Surjective (fun z : p.toSubgraph.verts => (z : V)) := by
    intro x
    exact ⟨⟨x, p.mem_verts_toSubgraph.mpr (hspan x)⟩, rfl⟩
  let eSub : p.toSubgraph.verts ≃ V :=
    Equiv.ofBijective (fun z : p.toSubgraph.verts => (z : V))
      ⟨fun _ _ h => Subtype.ext h, hsurj⟩
  let eGraph : p.toSubgraph.coe ≃g G :=
    ⟨eSub, by
      intro x y
      constructor
      · intro hxy
        exact (p.adj_toSubgraph_iff_mem_edges).2 (hedge hxy)
      · intro hxy
        exact p.toSubgraph.adj_sub hxy⟩
  let q : pathGraph (p.length + 1) ≃g G := hp.pathGraphIsoToSubgraph.trans eGraph
  refine ⟨p.length + 1, q.toEquiv, ?_⟩
  intro i j
  exact q.map_rel_iff

open SimpleGraph

/-- A finite tree of maximum degree at most two has a path spanning every
vertex and containing every edge. -/
public lemma simpleGraph_spanningPath_of_isTree_degree_le_two
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.IsTree)
    (hdegree : ∀ x, G.degree x ≤ 2) :
    ∃ (u v : V) (p : G.Walk u v),
      p.IsPath ∧
      (∀ x : V, x ∈ p.support) ∧
      ∀ ⦃x y : V⦄, G.Adj x y → s(x, y) ∈ p.edges := by
  classical
  let : Nonempty V := hG.connected.nonempty
  obtain ⟨u, v, p, hp, hmax⟩ :=
    Walk.exists_isPath_forall_isPath_length_le_length G
  have hspan : ∀ x : V, x ∈ p.support := by
    intro x
    by_contra hx
    obtain ⟨q, _⟩ := hG.connected.exists_isPath u x
    have hboundary :
        ∀ {a b : V} (q : G.Walk a b), a ∈ p.support → b ∉ p.support →
          ∃ y z : V, y ∈ p.support ∧ z ∉ p.support ∧ G.Adj y z := by
      intro a b q ha hb
      induction q with
      | nil => exact (hb ha).elim
      | @cons a c b hac q ih =>
          by_cases hc : c ∈ p.support
          · exact ih hc hb
          · exact ⟨a, c, ha, hc, hac⟩
    obtain ⟨y, z, hy, hz, hyz⟩ := hboundary q p.start_mem_support hx
    have hyend : y = u ∨ y = v := by
      rw [Walk.mem_support_iff_exists_getVert] at hy
      obtain ⟨i, hiy, hi⟩ := hy
      by_cases hi0 : i = 0
      · left
        simpa [hi0] using hiy.symm
      by_cases hil : i = p.length
      · right
        simpa [hil] using hiy.symm
      exfalso
      have hi_lt : i < p.length := by omega
      have hsubcard : (p.toSubgraph.neighborSet y).ncard = 2 := by
        rw [← hiy]
        exact hp.ncard_neighborSet_toSubgraph_internal_eq_two hi0 hi_lt
      have hsubset : p.toSubgraph.neighborSet y ⊂ G.neighborSet y := by
        refine Set.ssubset_iff_subset_ne.mpr
          ⟨p.toSubgraph.neighborSet_subset y, ?_⟩
        intro heq
        have hzsub : z ∈ p.toSubgraph.neighborSet y := heq.symm ▸ hyz
        exact hz (p.mem_verts_toSubgraph.mp
          (p.toSubgraph.neighborSet_subset_verts y hzsub))
      have hcardlt := Set.ncard_lt_ncard hsubset
      rw [hsubcard] at hcardlt
      have hdegree_le : (G.neighborSet y).ncard ≤ 2 := by
        rw [← (G.neighborSet y).fintypeCard_eq_ncard,
          G.card_neighborSet_eq_degree]
        exact hdegree y
      omega
    rcases hyend with rfl | rfl
    · have hp' : (p.cons hyz.symm).IsPath := hp.cons hz
      have hle := hmax z v (p.cons hyz.symm) hp'
      simp only [Walk.length_cons] at hle
      omega
    · have hp' : (p.concat hyz).IsPath := hp.concat hz hyz
      have hle := hmax u z (p.concat hyz) hp'
      rw [Walk.length_concat] at hle
      omega
  have htreeEdges := hG.card_edgeFinset
  have hham : p.IsHamiltonian := hp.isHamiltonian_of_mem hspan
  have hlength : p.length = G.edgeFinset.card := by
    have := hham.length_eq
    omega
  have hedgeFinset : p.edges.toFinset = G.edgeFinset := by
    apply Finset.eq_of_subset_of_card_le
    · intro e he
      rw [List.mem_toFinset] at he
      exact G.mem_edgeFinset.mpr (p.edges_subset_edgeSet he)
    · rw [List.toFinset_card_of_nodup hp.isTrail.edges_nodup,
        p.length_edges, hlength]
  refine ⟨u, v, p, hp, hspan, ?_⟩
  intro x y hxy
  rw [← List.mem_toFinset, hedgeFinset]
  exact G.mem_edgeFinset.mpr hxy

open SimpleGraph

/-- If all three arms contain at least two vertices, their first two vertices
and the center form the affine-`E₆` star. -/
public lemma simpleGraph_three_arm_affineE6_prefix_embedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V)
    {n0 n1 n2 : ℕ}
    (f0 : Fin (n0 + 1) → V) (f1 : Fin (n1 + 1) → V)
    (f2 : Fin (n2 + 1) → V)
    (hf0 : Function.Injective f0) (hf1 : Function.Injective f1)
    (hf2 : Function.Injective f2)
    (hc0 : ∀ j, c ≠ f0 j) (hc1 : ∀ j, c ≠ f1 j)
    (hc2 : ∀ j, c ≠ f2 j)
    (h01 : ∀ j l, f0 j ≠ f1 l) (h02 : ∀ j l, f0 j ≠ f2 l)
    (h12 : ∀ j l, f1 j ≠ f2 l)
    (hcenter0 : ∀ j, G.Adj c (f0 j) ↔ j = 0)
    (hcenter1 : ∀ j, G.Adj c (f1 j) ↔ j = 0)
    (hcenter2 : ∀ j, G.Adj c (f2 j) ↔ j = 0)
    (hpath0 : ∀ j l, G.Adj (f0 j) (f0 l) ↔ (pathGraph (n0 + 1)).Adj j l)
    (hpath1 : ∀ j l, G.Adj (f1 j) (f1 l) ↔ (pathGraph (n1 + 1)).Adj j l)
    (hpath2 : ∀ j l, G.Adj (f2 j) (f2 l) ↔ (pathGraph (n2 + 1)).Adj j l)
    (hcross01 : ∀ j l, ¬ G.Adj (f0 j) (f1 l))
    (hcross02 : ∀ j l, ¬ G.Adj (f0 j) (f2 l))
    (hcross12 : ∀ j l, ¬ G.Adj (f1 j) (f2 l))
    (hn0 : 0 < n0) (hn1 : 0 < n1) (hn2 : 0 < n2) :
    ∃ e : Fin 7 ↪ V, ∀ i j,
      G.Adj (e i) (e j) ↔
        ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
         (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
         (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
         (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
         (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
         (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5)) := by
  classical
  let e0 : Fin 7 → V :=
    ![c, f0 0, f0 ⟨1, by omega⟩, f1 0, f1 ⟨1, by omega⟩,
      f2 0, f2 ⟨1, by omega⟩]
  have hf0ne : f0 0 ≠ f0 ⟨1, by omega⟩ := by
    apply hf0.ne
    apply Fin.ne_of_val_ne
    simp
  have hf1ne : f1 0 ≠ f1 ⟨1, by omega⟩ := by
    apply hf1.ne
    apply Fin.ne_of_val_ne
    simp
  have hf2ne : f2 0 ≠ f2 ⟨1, by omega⟩ := by
    apply hf2.ne
    apply Fin.ne_of_val_ne
    simp
  have he0 : Function.Injective e0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [e0] at hij ⊢
    all_goals try exact False.elim ((hc0 _) hij)
    all_goals try exact False.elim ((hc0 _) hij.symm)
    all_goals try exact False.elim ((hc1 _) hij)
    all_goals try exact False.elim ((hc1 _) hij.symm)
    all_goals try exact False.elim ((hc2 _) hij)
    all_goals try exact False.elim ((hc2 _) hij.symm)
    all_goals try exact False.elim ((h01 _ _) hij)
    all_goals try exact False.elim ((h01 _ _) hij.symm)
    all_goals try exact False.elim ((h02 _ _) hij)
    all_goals try exact False.elim ((h02 _ _) hij.symm)
    all_goals try exact False.elim ((h12 _ _) hij)
    all_goals try exact False.elim ((h12 _ _) hij.symm)
    all_goals try exact False.elim (hf0ne hij)
    all_goals try exact False.elim (hf0ne hij.symm)
    all_goals try exact False.elim (hf1ne hij)
    all_goals try exact False.elim (hf1ne hij.symm)
    all_goals try exact False.elim (hf2ne hij)
    all_goals try exact False.elim (hf2ne hij.symm)
  let e : Fin 7 ↪ V := ⟨e0, he0⟩
  have hcross10 : ∀ j l, ¬ G.Adj (f1 l) (f0 j) := by
    intro j l
    rw [G.adj_comm]
    exact hcross01 j l
  have hcross20 : ∀ j l, ¬ G.Adj (f2 l) (f0 j) := by
    intro j l
    rw [G.adj_comm]
    exact hcross02 j l
  have hcross21 : ∀ j l, ¬ G.Adj (f2 l) (f1 j) := by
    intro j l
    rw [G.adj_comm]
    exact hcross12 j l
  refine ⟨e, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [e, e0, hcenter0, hcenter1, hcenter2, hpath0, hpath1, hpath2,
      hcross01, hcross02, hcross12, hcross10, hcross20, hcross21,
      pathGraph_adj, G.adj_comm]

open SimpleGraph

/-- One vertex on one arm and three vertices on each of the other two arms,
together with the center, form the affine-`E₇` support. -/
public lemma simpleGraph_three_arm_affineE7_prefix_embedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V)
    {n0 n1 n2 : ℕ}
    (f0 : Fin (n0 + 1) → V) (f1 : Fin (n1 + 1) → V)
    (f2 : Fin (n2 + 1) → V)
    (_hf0 : Function.Injective f0) (hf1 : Function.Injective f1)
    (hf2 : Function.Injective f2)
    (hc0 : ∀ j, c ≠ f0 j) (hc1 : ∀ j, c ≠ f1 j)
    (hc2 : ∀ j, c ≠ f2 j)
    (h01 : ∀ j l, f0 j ≠ f1 l) (h02 : ∀ j l, f0 j ≠ f2 l)
    (h12 : ∀ j l, f1 j ≠ f2 l)
    (hcenter0 : ∀ j, G.Adj c (f0 j) ↔ j = 0)
    (hcenter1 : ∀ j, G.Adj c (f1 j) ↔ j = 0)
    (hcenter2 : ∀ j, G.Adj c (f2 j) ↔ j = 0)
    (_hpath0 : ∀ j l, G.Adj (f0 j) (f0 l) ↔ (pathGraph (n0 + 1)).Adj j l)
    (hpath1 : ∀ j l, G.Adj (f1 j) (f1 l) ↔ (pathGraph (n1 + 1)).Adj j l)
    (hpath2 : ∀ j l, G.Adj (f2 j) (f2 l) ↔ (pathGraph (n2 + 1)).Adj j l)
    (hcross01 : ∀ j l, ¬ G.Adj (f0 j) (f1 l))
    (hcross02 : ∀ j l, ¬ G.Adj (f0 j) (f2 l))
    (hcross12 : ∀ j l, ¬ G.Adj (f1 j) (f2 l))
    (hn1 : 2 ≤ n1) (hn2 : 2 ≤ n2) :
    ∃ e : Fin 8 ↪ V, ∀ i j,
      G.Adj (e i) (e j) ↔
        ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
         (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
         (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
         (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
         (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
         (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
         (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6)) := by
  classical
  let e0 : Fin 8 → V :=
    ![c, f0 0, f1 0, f1 ⟨1, by omega⟩, f1 ⟨2, by omega⟩,
      f2 0, f2 ⟨1, by omega⟩, f2 ⟨2, by omega⟩]
  have he0 : Function.Injective e0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [e0] at hij ⊢
    all_goals try exact False.elim ((hc0 _) hij)
    all_goals try exact False.elim ((hc0 _) hij.symm)
    all_goals try exact False.elim ((hc1 _) hij)
    all_goals try exact False.elim ((hc1 _) hij.symm)
    all_goals try exact False.elim ((hc2 _) hij)
    all_goals try exact False.elim ((hc2 _) hij.symm)
    all_goals try exact False.elim ((h01 _ _) hij)
    all_goals try exact False.elim ((h01 _ _) hij.symm)
    all_goals try exact False.elim ((h02 _ _) hij)
    all_goals try exact False.elim ((h02 _ _) hij.symm)
    all_goals try exact False.elim ((h12 _ _) hij)
    all_goals try exact False.elim ((h12 _ _) hij.symm)
    all_goals try {
      have h := hf1 hij
      exact (Fin.ne_of_val_ne (by simp)) h }
    all_goals
      have h := hf2 hij
      exact (Fin.ne_of_val_ne (by simp)) h
  let e : Fin 8 ↪ V := ⟨e0, he0⟩
  have hcross10 : ∀ j l, ¬ G.Adj (f1 l) (f0 j) := by
    intro j l
    rw [G.adj_comm]
    exact hcross01 j l
  have hcross20 : ∀ j l, ¬ G.Adj (f2 l) (f0 j) := by
    intro j l
    rw [G.adj_comm]
    exact hcross02 j l
  have hcross21 : ∀ j l, ¬ G.Adj (f2 l) (f1 j) := by
    intro j l
    rw [G.adj_comm]
    exact hcross12 j l
  refine ⟨e, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [e, e0, hcenter0, hcenter1, hcenter2, hpath1, hpath2,
      hcross01, hcross02, hcross12, hcross10, hcross20, hcross21,
      pathGraph_adj, G.adj_comm]

open SimpleGraph

/-- Arm prefixes of lengths one, two, and five together with the center form
the affine-`E₈` support. -/
public lemma simpleGraph_three_arm_affineE8_prefix_embedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V)
    {n0 n1 n2 : ℕ}
    (f0 : Fin (n0 + 1) → V) (f1 : Fin (n1 + 1) → V)
    (f2 : Fin (n2 + 1) → V)
    (_hf0 : Function.Injective f0) (hf1 : Function.Injective f1)
    (hf2 : Function.Injective f2)
    (hc0 : ∀ j, c ≠ f0 j) (hc1 : ∀ j, c ≠ f1 j)
    (hc2 : ∀ j, c ≠ f2 j)
    (h01 : ∀ j l, f0 j ≠ f1 l) (h02 : ∀ j l, f0 j ≠ f2 l)
    (h12 : ∀ j l, f1 j ≠ f2 l)
    (hcenter0 : ∀ j, G.Adj c (f0 j) ↔ j = 0)
    (hcenter1 : ∀ j, G.Adj c (f1 j) ↔ j = 0)
    (hcenter2 : ∀ j, G.Adj c (f2 j) ↔ j = 0)
    (_hpath0 : ∀ j l, G.Adj (f0 j) (f0 l) ↔ (pathGraph (n0 + 1)).Adj j l)
    (hpath1 : ∀ j l, G.Adj (f1 j) (f1 l) ↔ (pathGraph (n1 + 1)).Adj j l)
    (hpath2 : ∀ j l, G.Adj (f2 j) (f2 l) ↔ (pathGraph (n2 + 1)).Adj j l)
    (hcross01 : ∀ j l, ¬ G.Adj (f0 j) (f1 l))
    (hcross02 : ∀ j l, ¬ G.Adj (f0 j) (f2 l))
    (hcross12 : ∀ j l, ¬ G.Adj (f1 j) (f2 l))
    (hn1 : 1 ≤ n1) (hn2 : 4 ≤ n2) :
    ∃ e : Fin 9 ↪ V, ∀ i j,
      G.Adj (e i) (e j) ↔
        ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
         (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
         (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
         (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
         (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨
         (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
         (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6) ∨
         (i = 7 ∧ j = 8) ∨ (i = 8 ∧ j = 7)) := by
  classical
  let e0 : Fin 9 → V :=
    ![c, f0 0, f1 0, f1 ⟨1, by omega⟩, f2 0,
      f2 ⟨1, by omega⟩, f2 ⟨2, by omega⟩, f2 ⟨3, by omega⟩,
      f2 ⟨4, by omega⟩]
  have he0 : Function.Injective e0 := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [e0] at hij ⊢
    all_goals try exact False.elim ((hc0 _) hij)
    all_goals try exact False.elim ((hc0 _) hij.symm)
    all_goals try exact False.elim ((hc1 _) hij)
    all_goals try exact False.elim ((hc1 _) hij.symm)
    all_goals try exact False.elim ((hc2 _) hij)
    all_goals try exact False.elim ((hc2 _) hij.symm)
    all_goals try exact False.elim ((h01 _ _) hij)
    all_goals try exact False.elim ((h01 _ _) hij.symm)
    all_goals try exact False.elim ((h02 _ _) hij)
    all_goals try exact False.elim ((h02 _ _) hij.symm)
    all_goals try exact False.elim ((h12 _ _) hij)
    all_goals try exact False.elim ((h12 _ _) hij.symm)
    all_goals try {
      have h := hf1 hij
      exact (Fin.ne_of_val_ne (by simp)) h }
    all_goals
      have h := hf2 hij
      exact (Fin.ne_of_val_ne (by simp)) h
  let e : Fin 9 ↪ V := ⟨e0, he0⟩
  have hcross10 : ∀ j l, ¬ G.Adj (f1 l) (f0 j) := by
    intro j l
    rw [G.adj_comm]
    exact hcross01 j l
  have hcross20 : ∀ j l, ¬ G.Adj (f2 l) (f0 j) := by
    intro j l
    rw [G.adj_comm]
    exact hcross02 j l
  have hcross21 : ∀ j l, ¬ G.Adj (f2 l) (f1 j) := by
    intro j l
    rw [G.adj_comm]
    exact hcross12 j l
  refine ⟨e, ?_⟩
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [e, e0, hcenter0, hcenter1, hcenter2, hpath1, hpath2,
      hcross01, hcross02, hcross12, hcross10, hcross20, hcross21,
      pathGraph_adj, G.adj_comm]

open SimpleGraph

/-- A positive prefix of one numbered arm, together with the center and the
roots of the other two arms, has the exact branch support used by the single-
heavy obstruction.  All disjointness and adjacency facts are ordinary
hypotheses; no certificate structure stores the conclusion. -/
public lemma simpleGraph_three_arm_prefix_branch_embedding
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (c : V)
    {n0 n1 n2 : ℕ}
    (f0 : Fin (n0 + 1) → V) (f1 : Fin (n1 + 1) → V)
    (f2 : Fin (n2 + 1) → V)
    (hf0 : Function.Injective f0) (_hf1 : Function.Injective f1)
    (_hf2 : Function.Injective f2)
    (hc0 : ∀ j, c ≠ f0 j) (hc1 : ∀ j, c ≠ f1 j)
    (hc2 : ∀ j, c ≠ f2 j)
    (h01 : ∀ j l, f0 j ≠ f1 l) (h02 : ∀ j l, f0 j ≠ f2 l)
    (h12 : ∀ j l, f1 j ≠ f2 l)
    (hcenter0 : ∀ j, G.Adj c (f0 j) ↔ j = 0)
    (hcenter1 : ∀ j, G.Adj c (f1 j) ↔ j = 0)
    (hcenter2 : ∀ j, G.Adj c (f2 j) ↔ j = 0)
    (hpath0 : ∀ j l, G.Adj (f0 j) (f0 l) ↔ (pathGraph (n0 + 1)).Adj j l)
    (_hpath1 : ∀ j l, G.Adj (f1 j) (f1 l) ↔ (pathGraph (n1 + 1)).Adj j l)
    (_hpath2 : ∀ j l, G.Adj (f2 j) (f2 l) ↔ (pathGraph (n2 + 1)).Adj j l)
    (hcross01 : ∀ j l, ¬ G.Adj (f0 j) (f1 l))
    (hcross02 : ∀ j l, ¬ G.Adj (f0 j) (f2 l))
    (hcross12 : ∀ j l, ¬ G.Adj (f1 j) (f2 l))
    {m : ℕ} (hm : 0 < m) (hmn : m ≤ n0) :
    ∃ e : Fin (m + 4) ↪ V,
      e 0 = f1 0 ∧ e 1 = f2 0 ∧ e 2 = c ∧
      (∀ j : Fin (m + 1),
        e ⟨j.val + 3, by omega⟩ = f0 (Fin.castLE (Nat.succ_le_succ hmn) j)) ∧
      (∀ i j : Fin (m + 4),
        G.Adj (e i) (e j) ↔
          ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
           (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
           (2 ≤ i.val ∧ i.val + 1 = j.val ∧ j.val ≤ m + 2) ∨
           (2 ≤ j.val ∧ j.val + 1 = i.val ∧ i.val ≤ m + 2) ∨
           (i.val = m + 2 ∧ j.val = m + 3) ∨
           (i.val = m + 3 ∧ j.val = m + 2))) := by
  classical
  let hsize : 3 + (m + 1) = m + 4 := by omega
  let hcast : Fin (m + 4) ≃ Fin (3 + (m + 1)) := finCongr hsize.symm
  let left : Fin 3 → V :=
    fun i => if i = 0 then f1 0 else if i = 1 then f2 0 else c
  let right : Fin (m + 1) → V :=
    fun j => f0 (Fin.castLE (Nat.succ_le_succ hmn) j)
  let g : Fin (3 + (m + 1)) → V := fun i =>
    if hi : i.val < 3 then left ⟨i.val, hi⟩
    else right ⟨i.val - 3, by omega⟩
  have hleft0 : left 0 = f1 0 := by rfl
  have hleft1 : left 1 = f2 0 := by simp [left]
  have hleft2 : left 2 = c := by simp [left]
  have hleft_inj : Function.Injective left := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [left] at hij ⊢
    all_goals try { exact False.elim ((h12 0 0) hij) }
    all_goals try { exact False.elim ((h12 0 0) hij.symm) }
    all_goals try { exact False.elim ((hc1 0) hij) }
    all_goals try { exact False.elim ((hc1 0) hij.symm) }
    all_goals try { exact False.elim ((hc2 0) hij) }
    all_goals try { exact False.elim ((hc2 0) hij.symm) }
  have hright_inj : Function.Injective right := by
    intro i j hij
    apply (Fin.castLE_injective (Nat.succ_le_succ hmn))
    apply hf0
    exact hij
  have hcross_left_right : ∀ i : Fin 3, ∀ j : Fin (m + 1),
      left i ≠ right j := by
    intro i j hij
    fin_cases i
    · exact (h01 _ _) hij.symm
    · exact (h02 _ _) hij.symm
    · have hijeq : c = f0 (Fin.castLE (Nat.succ_le_succ hmn) j) := by
        calc
          c = left 2 := hleft2.symm
          _ = right j := hij
          _ = f0 (Fin.castLE (Nat.succ_le_succ hmn) j) := rfl
      exact (hc0 _) hijeq
  have hg_inj : Function.Injective g := by
    intro i j hij
    by_cases hi : i.val < 3
    · by_cases hj : j.val < 3
      · let i' : Fin 3 := ⟨i.val, hi⟩
        let j' : Fin 3 := ⟨j.val, hj⟩
        have hij' : left i' = left j' := by
          simpa [g, i', j', hi, hj] using hij
        have heq : i' = j' := hleft_inj hij'
        apply Fin.ext
        simpa [i', j'] using congrArg Fin.val heq
      · exfalso
        let i' : Fin 3 := ⟨i.val, hi⟩
        let j' : Fin (m + 1) := ⟨j.val - 3, by omega⟩
        have hij' : left i' = right j' := by
          simpa [g, i', j', hi, hj] using hij
        exact hcross_left_right i' j' hij'
    · by_cases hj : j.val < 3
      · exfalso
        let i' : Fin (m + 1) := ⟨i.val - 3, by omega⟩
        let j' : Fin 3 := ⟨j.val, hj⟩
        have hij' : right i' = left j' := by
          simpa [g, i', j', hi, hj] using hij
        exact hcross_left_right j' i' hij'.symm
      · let i' : Fin (m + 1) := ⟨i.val - 3, by omega⟩
        let j' : Fin (m + 1) := ⟨j.val - 3, by omega⟩
        have hij' : right i' = right j' := by
          simpa [g, i', j', hi, hj] using hij
        have heq : i' = j' := hright_inj hij'
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simp [i', j'] at hv
        omega
  let e : Fin (m + 4) ↪ V :=
    ⟨fun i => g (hcast i), by
      intro i j hij
      apply hcast.injective
      exact hg_inj hij⟩
  have he0 : e 0 = f1 0 := by
    change g (hcast 0) = f1 0
    simp [hcast, g, left]
  have he1 : e 1 = f2 0 := by
    change g (hcast 1) = f2 0
    simp [hcast, g, left]
  have he2 : e 2 = c := by
    change g (hcast 2) = c
    have hz : hcast 2 = (⟨2, by omega⟩ : Fin (3 + (m + 1))) := by
      apply Fin.ext
      simp [hcast]
    rw [hz]
    simp [g, left]
  have hearm : ∀ j : Fin (m + 1),
      e ⟨j.val + 3, by omega⟩ = f0 (Fin.castLE (Nat.succ_le_succ hmn) j) := by
    intro j
    change g (hcast ⟨j.val + 3, by omega⟩) = _
    simp [hcast, g, right]
    congr 1
  let R : Fin (3 + (m + 1)) → Fin (3 + (m + 1)) → Prop := fun i j =>
    ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
     (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
     (2 ≤ i.val ∧ i.val + 1 = j.val ∧ j.val ≤ m + 2) ∨
     (2 ≤ j.val ∧ j.val + 1 = i.val ∧ i.val ≤ m + 2) ∨
     (i.val = m + 2 ∧ j.val = m + 3) ∨
     (i.val = m + 3 ∧ j.val = m + 2))
  have hleft_support : ∀ il jl : Fin 3,
      G.Adj (left il) (left jl) ↔
        ((il.val = 0 ∧ jl.val = 2) ∨ (il.val = 2 ∧ jl.val = 0) ∨
         (il.val = 1 ∧ jl.val = 2) ∨ (il.val = 2 ∧ jl.val = 1)) := by
    intro il jl
    fin_cases il <;> fin_cases jl <;>
      simp [left, hcenter1, hcenter2, hcross12, G.adj_comm]
  have hleft_right_support : ∀ il : Fin 3, ∀ jr : Fin (m + 1),
      G.Adj (left il) (right jr) ↔ il.val = 2 ∧ jr.val = 0 := by
    intro il jr
    fin_cases il
    · simp [left, right, hcross01, G.adj_comm]
    · simp [left, right, hcross02, G.adj_comm]
    · simp [left, right, hcenter0]
      constructor
      · intro h
        have hv := congrArg Fin.val h
        simp at hv
        simpa using hv
      · intro h
        subst jr
        rfl
  have hright_left_support : ∀ ir : Fin (m + 1), ∀ jl : Fin 3,
      G.Adj (right ir) (left jl) ↔ ir.val = 0 ∧ jl.val = 2 := by
    intro ir jl
    rw [G.adj_comm]
    simpa [and_comm] using hleft_right_support jl ir
  have hright_support : ∀ ir jr : Fin (m + 1),
      G.Adj (right ir) (right jr) ↔ ir.val + 1 = jr.val ∨ jr.val + 1 = ir.val := by
    intro ir jr
    change G.Adj (f0 (Fin.castLE (Nat.succ_le_succ hmn) ir))
      (f0 (Fin.castLE (Nat.succ_le_succ hmn) jr)) ↔ _
    rw [hpath0, pathGraph_adj]
    rfl
  have hsupport_g : ∀ i j : Fin (3 + (m + 1)),
      G.Adj (g i) (g j) ↔ R i j := by
    intro i j
    by_cases hi : i.val < 3
    · let il : Fin 3 := ⟨i.val, hi⟩
      by_cases hj : j.val < 3
      · let jl : Fin 3 := ⟨j.val, hj⟩
        have hgi : g i = left il := by simp [g, il, hi]
        have hgj : g j = left jl := by simp [g, jl, hj]
        rw [hgi, hgj]
        have hs := hleft_support il jl
        have hR : R i j ↔
            ((il.val = 0 ∧ jl.val = 2) ∨ (il.val = 2 ∧ jl.val = 0) ∨
             (il.val = 1 ∧ jl.val = 2) ∨ (il.val = 2 ∧ jl.val = 1)) := by
          simp [R, il, jl]
          omega
        rw [hR]
        exact hs
      · let jr : Fin (m + 1) := ⟨j.val - 3, by omega⟩
        have hgi : g i = left il := by simp [g, il, hi]
        have hgj : g j = right jr := by simp [g, jr, hj]
        rw [hgi, hgj]
        have hs := hleft_right_support il jr
        have hR : R i j ↔ il.val = 2 ∧ jr.val = 0 := by
          dsimp [R]
          change ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
            (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
            (2 ≤ i.val ∧ i.val + 1 = j.val ∧ j.val ≤ m + 2) ∨
            (2 ≤ j.val ∧ j.val + 1 = i.val ∧ i.val ≤ m + 2) ∨
            (i.val = m + 2 ∧ j.val = m + 3) ∨
            (i.val = m + 3 ∧ j.val = m + 2)) ↔
            i.val = 2 ∧ (j.val - 3 = 0)
          have hj_ge : 3 ≤ j.val := by omega
          omega
        rw [hR]
        exact hs
    · let ir : Fin (m + 1) := ⟨i.val - 3, by omega⟩
      by_cases hj : j.val < 3
      · let jl : Fin 3 := ⟨j.val, hj⟩
        have hgi : g i = right ir := by simp [g, ir, hi]
        have hgj : g j = left jl := by simp [g, jl, hj]
        rw [hgi, hgj]
        have hs := hright_left_support ir jl
        have hR : R i j ↔ ir.val = 0 ∧ jl.val = 2 := by
          dsimp [R]
          change ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
            (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1) ∨
            (2 ≤ i.val ∧ i.val + 1 = j.val ∧ j.val ≤ m + 2) ∨
            (2 ≤ j.val ∧ j.val + 1 = i.val ∧ i.val ≤ m + 2) ∨
            (i.val = m + 2 ∧ j.val = m + 3) ∨
            (i.val = m + 3 ∧ j.val = m + 2)) ↔
            (i.val - 3 = 0) ∧ j.val = 2
          have hi_ge : 3 ≤ i.val := by omega
          omega
        rw [hR]
        exact hs
      · let jr : Fin (m + 1) := ⟨j.val - 3, by omega⟩
        have hgi : g i = right ir := by simp [g, ir, hi]
        have hgj : g j = right jr := by simp [g, jr, hj]
        rw [hgi, hgj]
        have hs := hright_support ir jr
        have hR : R i j ↔ ir.val + 1 = jr.val ∨ jr.val + 1 = ir.val := by
          simp [R, ir, jr]
          omega
        rw [hR]
        exact hs
  refine ⟨e, he0, he1, he2, hearm, ?_⟩
  intro i j
  have hsupport := hsupport_g (hcast i) (hcast j)
  simpa [e, R, hcast] using hsupport

open scoped SimpleGraph

/-- In a tree, every vertex away from `c` lies in the component of exactly one
neighbor of `c` after `c` is deleted.  This is the graph-theoretic partition
principle used to construct the three arms at a unique branch vertex. -/
public lemma simpleGraph_tree_existsUnique_neighbor_reachable_without_center
    {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (hG : G.IsTree) (c v : V) (hvc : v ≠ c) :
    ∃ a, ∃ ha : G.Adj c a,
      (G.induce {c}ᶜ).Reachable
          ⟨a, by simpa using ha.ne.symm⟩ ⟨v, by simpa using hvc⟩ ∧
        ∀ b (hb : G.Adj c b),
          (G.induce {c}ᶜ).Reachable
            ⟨b, by simpa using hb.ne.symm⟩ ⟨v, by simpa using hvc⟩ →
          b = a := by
  obtain ⟨p, hp, hpuniq⟩ := hG.existsUnique_path c v
  have hpNil : ¬p.Nil := by
    intro hnil
    exact hvc (hp.nil_iff_eq.mp hnil).symm
  let a := p.snd
  have ha : G.Adj c a := by
    simpa [a] using p.adj_snd hpNil
  have htail : ∀ x ∈ p.tail.support, x ∈ ({c}ᶜ : Set V) := by
    intro x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro hxc
    subst x
    have hn : (c :: p.tail.support).Nodup := by
      rw [p.cons_support_tail hpNil]
      exact hp.support_nodup
    exact (List.nodup_cons.mp hn).1 hx
  let q := p.tail.induce ({c}ᶜ : Set V) htail
  have hreach : (G.induce {c}ᶜ).Reachable
      ⟨a, by simpa using ha.ne.symm⟩ ⟨v, by simpa using hvc⟩ := by
    refine ⟨q.copy ?_ ?_⟩
    · apply SetCoe.ext
      rfl
    · apply SetCoe.ext
      rfl
  refine ⟨a, ha, hreach, ?_⟩
  intro b hb hbReach
  obtain ⟨qb, hqb⟩ := hbReach.exists_isPath
  let f : G.induce ({c}ᶜ : Set V) ↪g G :=
    SimpleGraph.Embedding.induce ({c}ᶜ : Set V)
  let qbG := qb.map f.toHom
  have hqbG : qbG.IsPath := by
    exact hqb.map f.injective
  have hcnot : c ∉ qbG.support := by
    intro hc
    rw [SimpleGraph.Walk.support_map] at hc
    obtain ⟨z, hz, hzc⟩ := List.mem_map.mp hc
    have hznot : (z : V) ≠ c := by
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using z.property
    exact hznot hzc
  let r : G.Walk c v := qbG.cons hb
  have hr : r.IsPath := by
    apply (SimpleGraph.Walk.cons_isPath_iff hb qbG).2
    exact ⟨hqbG, hcnot⟩
  have hrp : r = p := hpuniq r hr
  have hsnd := congrArg SimpleGraph.Walk.snd hrp
  have hrsnd : r.snd = b := by
    change (SimpleGraph.Walk.cons hb qbG).snd = b
    exact (SimpleGraph.Walk.snd_cons qbG hb).trans (by rfl)
  calc
    b = r.snd := hrsnd.symm
    _ = p.snd := hsnd
    _ = a := rfl

open scoped SimpleGraph

/-- In a finite tree, a path between two distinct degree-three vertices has two
additional, distinct neighbors at each endpoint, and those neighbors are not
on the path.  The result exposes only ordinary graph witnesses; affine-D and
classification data are intentionally left to later cores. -/
public lemma simpleGraph_two_degree_three_vertices_offPath_neighbors
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : G.IsTree)
    (c₁ c₂ : V) (hneq : c₁ ≠ c₂)
    (hdeg₁ : G.degree c₁ = 3) (hdeg₂ : G.degree c₂ = 3) :
    ∃ p : G.Walk c₁ c₂, p.IsPath ∧ ∃ a₁ a₂ b₁ b₂,
      a₁ ≠ a₂ ∧ b₁ ≠ b₂ ∧
      a₁ ≠ b₁ ∧ a₁ ≠ b₂ ∧ a₂ ≠ b₁ ∧ a₂ ≠ b₂ ∧
      G.Adj c₁ a₁ ∧ G.Adj c₁ a₂ ∧ G.Adj c₂ b₁ ∧ G.Adj c₂ b₂ ∧
      a₁ ∉ p.support ∧ a₂ ∉ p.support ∧
      b₁ ∉ p.support ∧ b₂ ∉ p.support := by
  classical
  obtain ⟨p, hp, hpu⟩ := hG.existsUnique_path c₁ c₂
  have hpNil : ¬p.Nil := by
    intro h
    exact hneq (hp.nil_iff_eq.mp h)
  have hstart : G.Adj c₁ p.snd := p.adj_of_mem_edges (p.mk_start_snd_mem_edges hpNil)
  let S₁ := G.neighborFinset c₁ \ {p.snd}
  have hsub₁ : ({p.snd} : Finset V) ⊆ G.neighborFinset c₁ := by
    intro x hx
    have : x = p.snd := by simpa using hx
    rw [this]
    exact (G.mem_neighborFinset c₁ p.snd).mpr hstart
  have hcard₁ : S₁.card = 2 := by
    dsimp [S₁]
    rw [Finset.card_sdiff_of_subset hsub₁, G.card_neighborFinset_eq_degree, hdeg₁]
    simp
  obtain ⟨a₁, a₂, ha12, hS₁⟩ := Finset.card_eq_two.mp hcard₁
  have ha₁S : a₁ ∈ S₁ := by rw [hS₁]; simp
  have ha₂S : a₂ ∈ S₁ := by rw [hS₁]; simp
  have ha₁adj : G.Adj c₁ a₁ := (G.mem_neighborFinset c₁ a₁).mp (Finset.mem_sdiff.mp ha₁S).1
  have ha₂adj : G.Adj c₁ a₂ := (G.mem_neighborFinset c₁ a₂).mp (Finset.mem_sdiff.mp ha₂S).1
  have ha₁snd : a₁ ≠ p.snd := by simpa using (Finset.mem_sdiff.mp ha₁S).2
  have ha₂snd : a₂ ≠ p.snd := by simpa using (Finset.mem_sdiff.mp ha₂S).2
  have offpath {u v : V} {q : G.Walk u v} (hq : q.IsPath) (hqNil : ¬q.Nil)
      {a : V} (ha : G.Adj u a) (has : a ≠ q.snd) : a ∉ q.support := by
    intro haSupport
    let r := q.takeUntil a haSupport
    have hr : r.IsPath := hq.takeUntil haSupport
    have hnot : s(a, u) ∉ r.edges := by
      intro hedge
      have hedge' : s(u, a) ∈ r.edges := by simpa [Sym2.eq_swap] using hedge
      have hedge'' : s(u, a) ∈ q.edges := q.edges_takeUntil_subset_edges haSupport hedge'
      exact has (hq.eq_snd_of_mem_edges hedge'')
    have hcycle : (SimpleGraph.Walk.cons ha.symm r).IsCycle :=
      (SimpleGraph.Walk.cons_isCycle_iff r ha.symm).2 ⟨hr, hnot⟩
    exact hG.isAcyclic _ hcycle
  have ha₁off : a₁ ∉ p.support := offpath hp hpNil ha₁adj ha₁snd
  have ha₂off : a₂ ∉ p.support := offpath hp hpNil ha₂adj ha₂snd
  let q := p.reverse
  have hq : q.IsPath := hp.reverse
  have hqNil : ¬q.Nil := by simpa [q] using hpNil
  have hqstart : G.Adj c₂ q.snd := q.adj_of_mem_edges (q.mk_start_snd_mem_edges hqNil)
  let S₂ := G.neighborFinset c₂ \ {q.snd}
  have hsub₂ : ({q.snd} : Finset V) ⊆ G.neighborFinset c₂ := by
    intro x hx
    have : x = q.snd := by simpa using hx
    rw [this]
    exact (G.mem_neighborFinset c₂ q.snd).mpr hqstart
  have hcard₂ : S₂.card = 2 := by
    dsimp [S₂]
    rw [Finset.card_sdiff_of_subset hsub₂, G.card_neighborFinset_eq_degree, hdeg₂]
    simp
  obtain ⟨b₁, b₂, hb12, hS₂⟩ := Finset.card_eq_two.mp hcard₂
  have hb₁S : b₁ ∈ S₂ := by rw [hS₂]; simp
  have hb₂S : b₂ ∈ S₂ := by rw [hS₂]; simp
  have hb₁adj : G.Adj c₂ b₁ := (G.mem_neighborFinset c₂ b₁).mp (Finset.mem_sdiff.mp hb₁S).1
  have hb₂adj : G.Adj c₂ b₂ := (G.mem_neighborFinset c₂ b₂).mp (Finset.mem_sdiff.mp hb₂S).1
  have hb₁snd : b₁ ≠ q.snd := by simpa using (Finset.mem_sdiff.mp hb₁S).2
  have hb₂snd : b₂ ≠ q.snd := by simpa using (Finset.mem_sdiff.mp hb₂S).2
  have hb₁offq : b₁ ∉ q.support := by
    apply offpath hq hqNil hb₁adj hb₁snd
  have hb₂offq : b₂ ∉ q.support := by
    apply offpath hq hqNil hb₂adj hb₂snd
  have hb₁off : b₁ ∉ p.support := by
    intro hb
    apply hb₁offq
    rw [p.support_reverse]
    simpa using hb
  have hb₂off : b₂ ∉ p.support := by
    intro hb
    apply hb₂offq
    rw [p.support_reverse]
    simpa using hb
  have hc₂mem : c₂ ∈ p.support := by
    rw [SimpleGraph.Walk.mem_support_iff_exists_getVert]
    exact ⟨p.length, p.getVert_length, le_rfl⟩
  have cross_ne {a b : V} (ha : G.Adj c₁ a) (hb : G.Adj c₂ b)
      (hao : a ∉ p.support) (hbo : b ∉ p.support) : a ≠ b := by
    intro hab
    subst b
    have hac₁ : a ≠ c₁ := ha.ne.symm
    have hac₂ : a ≠ c₂ := by
      intro h
      apply hao
      exact h ▸ hc₂mem
    let q : G.Walk c₁ c₂ :=
      SimpleGraph.Walk.cons ha (SimpleGraph.Walk.cons hb.symm SimpleGraph.Walk.nil)
    have htail : (SimpleGraph.Walk.cons hb.symm SimpleGraph.Walk.nil).IsPath := by
      apply (SimpleGraph.Walk.cons_isPath_iff _ _).2
      exact ⟨SimpleGraph.Walk.IsPath.nil, by simp [hac₂]
        ⟩
    have hq : q.IsPath := by
      apply (SimpleGraph.Walk.cons_isPath_iff _ _).2
      refine ⟨htail, ?_⟩
      intro hmem
      simp at hmem
      rcases hmem with hmem | hmem
      · exact hac₁.symm hmem
      · exact hneq hmem
    have hpq : q = p := hpu q hq
    apply hao
    rw [← hpq]
    simp [q]
  have hab₁ : a₁ ≠ b₁ := cross_ne ha₁adj hb₁adj ha₁off hb₁off
  have hab₂ : a₁ ≠ b₂ := cross_ne ha₁adj hb₂adj ha₁off hb₂off
  have hac₁ : a₂ ≠ b₁ := cross_ne ha₂adj hb₁adj ha₂off hb₁off
  have hac₂ : a₂ ≠ b₂ := cross_ne ha₂adj hb₂adj ha₂off hb₂off
  exact ⟨p, hp, a₁, a₂, b₁, b₂, ha12, hb12, hab₁, hab₂, hac₁, hac₂,
    ha₁adj, ha₂adj, hb₁adj, hb₂adj, ha₁off, ha₂off, hb₁off, hb₂off⟩

/-- The reduced crystallographic core of Theorem 1.8.2: a finite root
system has a fundamental system. Mathlib's `RootPairing.Base` is the formal
fundamental-system object. -/
public theorem rootSystem_exists_fundamentalSystem
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] :
    Nonempty P.Base :=
  P.nonempty_base

open Function Set Submodule

/-- The Weyl-group finiteness assertion of Theorem 1.8.2: the Weyl group of
a finite root system embeds faithfully into the finite permutation group of
its roots. -/
public theorem weylGroup_finite
    {ι R M N : Type*} [Finite ι] [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] : Finite P.weylGroup := by
  apply Finite.of_injective P.weylGroupToPerm
  intro g h hgh
  apply Subtype.ext
  apply RootPairing.Equiv.weightHom_injective P
  apply LinearEquiv.ext
  have hlin :
      (RootPairing.Equiv.weightHom P (g : RootPairing.Aut P)).toLinearMap =
        (RootPairing.Equiv.weightHom P (h : RootPairing.Aut P)).toLinearMap := by
    apply LinearMap.ext_on_range (v := P.root)
      (RootPairing.IsRootSystem.span_root_eq_top (P := P))
    intro i
    have hi := congrArg (fun e : ι ≃ ι => e i) hgh
    calc
      (RootPairing.Equiv.weightHom P (g : RootPairing.Aut P)).toLinearMap
            (P.root i) = g • P.root i := rfl
      _ = P.root (P.weylGroupToPerm g i) := P.weylGroup_apply_root g i
      _ = P.root (P.weylGroupToPerm h i) := congrArg P.root hi
      _ = h • P.root i := (P.weylGroup_apply_root h i).symm
      _ = (RootPairing.Equiv.weightHom P (h : RootPairing.Aut P)).toLinearMap
            (P.root i) := rfl
  exact LinearMap.congr_fun hlin

/-- Theorem 1.8.3(a): the simple roots form a basis. -/
public lemma RootPairing.Base.simpleRoots_basis
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    (b : P.Base) :
    Nonempty (Module.Basis b.support ℝ M) :=
  ⟨b.toWeightBasis⟩

/-- Theorem 1.8.3(a): the Cartan pairing of distinct simple roots is
nonpositive. This version does not assume crystallographicity. -/
public lemma RootPairing.Base.pairing_nonpositive_of_mem_support
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    {P : RootPairing ι ℝ M N} [P.IsRootSystem]
    (b : P.Base) {i j : ι}
    (hi : i ∈ b.support) (hj : j ∈ b.support) (hij : i ≠ j) :
    P.pairing i j ≤ 0 := by
  classical
  let := Fintype.ofFinite ι
  let : Fintype b.support := Fintype.ofFinite b.support
  let k := P.reflectionPerm j i
  obtain ⟨f, -, hpos | hneg⟩ := b.exists_root_eq_sum_nat_or_neg k
  · have hrefl : P.root k = P.root i - P.pairing i j • P.root j :=
      (P.reflectionPerm_root j i).symm
    let ii : b.support := ⟨i, hi⟩
    let jj : b.support := ⟨j, hj⟩
    let g : b.support → ℝ :=
      Pi.single ii 1 + Pi.single jj (-P.pairing i j)
    let h : b.support → ℝ := fun x => f x
    have hsingle (x : b.support) (c : ℝ) :
        ∑ y, (Pi.single x c : b.support → ℝ) y • P.root y = c • P.root x := by
      rw [Fintype.sum_eq_single x] <;> simp_all
    have hleft : ∑ x, g x • P.root x = P.root i - P.pairing i j • P.root j := by
      simp [g, add_smul, Finset.sum_add_distrib, hsingle, ii, jj, sub_eq_add_neg]
    have hright : ∑ x, h x • P.root x = P.root k := by
      rw [hpos, b.support.sum_subtype (p := (· ∈ b.support)) (by simp)
        (F := inferInstance)]
      simp [h, Nat.cast_smul_eq_nsmul]
    have hli : LinearIndependent ℝ (fun x : b.support => P.root x) :=
      b.linearIndepOn_root
    have hcoeff := Fintype.linearIndependent_iffₛ.mp hli g h
      (hleft.trans (hrefl.symm.trans hright.symm)) jj
    have hfj : (f j : ℝ) = -P.pairing i j := by
      simpa [g, h, ii, jj, hij] using hcoeff.symm
    linarith [Nat.cast_nonneg (α := ℝ) (f j)]
  · have hrefl : P.root k = P.root i - P.pairing i j • P.root j :=
      (P.reflectionPerm_root j i).symm
    let ii : b.support := ⟨i, hi⟩
    let jj : b.support := ⟨j, hj⟩
    let g : b.support → ℝ :=
      Pi.single ii 1 + Pi.single jj (-P.pairing i j)
    let h : b.support → ℝ := fun x => -(f x : ℝ)
    have hsingle (x : b.support) (c : ℝ) :
        ∑ y, (Pi.single x c : b.support → ℝ) y • P.root y = c • P.root x := by
      rw [Fintype.sum_eq_single x] <;> simp_all
    have hleft : ∑ x, g x • P.root x = P.root i - P.pairing i j • P.root j := by
      simp [g, add_smul, Finset.sum_add_distrib, hsingle, ii, jj, sub_eq_add_neg]
    have hright : ∑ x, h x • P.root x = P.root k := by
      rw [hneg, b.support.sum_subtype (p := (· ∈ b.support)) (by simp)
        (F := inferInstance)]
      simp [h, Nat.cast_smul_eq_nsmul]
    have hli : LinearIndependent ℝ (fun x : b.support => P.root x) :=
      b.linearIndepOn_root
    have hcoeff := Fintype.linearIndependent_iffₛ.mp hli g h
      (hleft.trans (hrefl.symm.trans hright.symm)) ii
    have hfi : (1 : ℝ) = -(f i : ℝ) := by
      simpa [g, h, ii, jj, hij] using hcoeff
    exfalso
    linarith [Nat.cast_nonneg (α := ℝ) (f i)]

/-- The final assertion of Theorem 1.8.3(c): reflection in a base root sends
that root, and no other positive root, to a negative root. -/
public lemma simpleReflection_unique_positiveRoot
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) {j : ι} (hj : j ∈ b.support) :
    ∀ i, b.IsPos i ∧ ¬ b.IsPos (P.reflectionPerm j i) ↔ i = j := by
  let := P.indexNeg
  intro i
  constructor
  · rintro ⟨hi, hneg⟩
    by_contra hij
    exact hneg (hi.reflectionPerm hj hij)
  · rintro rfl
    refine ⟨b.isPos_of_mem_support hj, ?_⟩
    change ¬ b.IsPos (-i)
    rw [b.isPos_iff, b.height_reflectionPerm_self,
      b.height_one_of_mem_support hj]
    norm_num

/-- The extension core of Theorem 1.8.7: a bijection of fundamental systems
preserving the Cartan matrix extends to an isomorphism of root systems. -/
public theorem rootPairing_equiv_of_cartanMatrix
    {ι ι₂ R M N M₂ N₂ : Type*} [Finite ι] [Finite ι₂]
    [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup M₂] [Module R M₂] [AddCommGroup N₂] [Module R N₂]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    {P₂ : RootPairing ι₂ R M₂ N₂} [P₂.IsRootSystem]
    [P₂.IsCrystallographic] [P₂.IsReduced] (b₂ : P₂.Base)
    (e : b.support ≃ b₂.support)
    (he : ∀ i j, b₂.cartanMatrix (e i) (e j) = b.cartanMatrix i j) :
    Nonempty (P.Equiv P₂) :=
  ⟨b.equivOfCartanMatrixEq b₂ e he⟩

/-- The simple roots of a base are exactly the indecomposable roots in its
associated positive subsystem. -/
public lemma base_mem_support_iff_isIndecomposablePositive
    {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic]
    (b : P.Base) (i : ι) :
    i ∈ b.support ↔ b.toPositiveSubsystem.IsIndecomposable i := by
  rw [_root_.RootPairing.PositiveSubsystem.isIndecomposable_iff]
  simp only [_root_.RootPairing.Base.mem_toPositiveSubsystem]
  constructor
  · intro hi
    refine ⟨b.isPos_of_mem_support hi, ?_⟩
    rintro ⟨j, k, hj, hk, hsum⟩
    have hj' : 0 < b.height j := hj
    have hk' : 0 < b.height k := hk
    have hheight := b.height_add hsum
    rw [b.height_one_of_mem_support hi] at hheight
    lia
  · rintro ⟨hi, hindecomp⟩
    have hconstruct :
        b.IsPos i ∧
          (i ∈ b.support ∨
            ∃ j k, b.IsPos j ∧ b.IsPos k ∧ P.root i = P.root j + P.root k) := by
      apply hi.induction_on_add
      · intro j hj
        exact ⟨b.isPos_of_mem_support hj, Or.inl hj⟩
      · intro j k l hsum hj hk
        refine ⟨hj.1.add (b.isPos_of_mem_support hk) hsum, Or.inr ?_⟩
        exact ⟨j, k, hj.1, b.isPos_of_mem_support hk, hsum⟩
    rcases hconstruct.2 with hi | hi
    · exact hi
    · exact (hindecomp hi).elim

open Set

/-- Distinct indecomposable roots of a positive subsystem have nonpositive
Cartan pairing. -/
public lemma _root_.RootPairing.PositiveSubsystem.pairingIn_le_zero_of_isIndecomposable
    {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic]
    (S : P.PositiveSubsystem) {i j : ι}
    (hi : S.IsIndecomposable i) (hj : S.IsIndecomposable j) (hij : i ≠ j) :
    P.pairingIn ℤ i j ≤ 0 := by
  let := P.indexNeg
  have hsubset :
      {k | S.IsIndecomposable k} ⊆
        {k | IsAddIndecomposable P.root (S : Set ι) k} := by
    intro k hk
    change S.IsIndecomposable k at hk
    change IsAddIndecomposable P.root (S : Set ι) k
    rw [_root_.RootPairing.PositiveSubsystem.isIndecomposable_iff] at hk
    refine ⟨hk.1, ?_⟩
    intro a ha b hb hab
    exact (hk.2 ⟨a, b, ha, hb, hab⟩).elim
  have hpair := IsAddIndecomposable.pairwise_sub_notMem_range
    P.root (fun k => P.ne_zero k) (by simp)
    {k | S.IsIndecomposable k} (S : Set ι) hsubset (fun k => S.mem_or_neg k)
  have hnot : P.root i - P.root j ∉ range P.root := hpair hi hj hij
  by_contra h
  exact hnot (P.root_sub_root_mem_of_pairingIn_pos (by omega) hij)

open Set

/-- A nonempty finite sum of roots in a positive subsystem is nonzero. -/
public lemma _root_.RootPairing.PositiveSubsystem.sum_roots_ne_zero
    {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic]
    (S : P.PositiveSubsystem) (l : List ι)
    (hl : ∀ i ∈ l, i ∈ S) (hne : l ≠ []) :
    (l.map P.root).sum ≠ 0 := by
  let := P.indexNeg
  classical
  induction hlen : l.length using Nat.strong_induction_on generalizing l with
  | h n ih =>
      intro hzero
      cases l with
      | nil => exact hne rfl
      | cons i tail =>
          have hiS : i ∈ S := hl i (by simp)
          have htailS : ∀ j ∈ tail, j ∈ S := by
            intro j hj
            exact hl j (by simp [hj])
          have hpairsum : (tail.map fun j => P.pairingIn ℤ j i).sum = -2 := by
            have hp := congrArg (P.coroot' i) hzero
            simp only [List.map_cons, List.sum_cons, map_add, map_zero] at hp
            rw [map_list_sum, List.map_map] at hp
            have hmap : List.map ((P.coroot' i) ∘ P.root) tail =
                List.map (fun j => algebraMap ℤ R (P.pairingIn ℤ j i)) tail := by
              apply List.map_congr_left
              intro j hj
              simp [← P.algebraMap_pairingIn ℤ]
            rw [hmap, show (P.coroot' i) (P.root i) = 2 by simp] at hp
            have hcastsum :
                (tail.map fun j => algebraMap ℤ R (P.pairingIn ℤ j i)).sum = -2 :=
              eq_neg_of_add_eq_zero_right hp
            apply FaithfulSMul.algebraMap_injective ℤ R
            calc
              algebraMap ℤ R (tail.map fun j => P.pairingIn ℤ j i).sum =
                  (tail.map fun j => algebraMap ℤ R (P.pairingIn ℤ j i)).sum := by
                simp [List.map_map, Function.comp_def, map_list_sum]
              _ = -2 := hcastsum
              _ = algebraMap ℤ R (-2) := by norm_num
          obtain ⟨j, hjtail, hjneg⟩ :
              ∃ j ∈ tail, P.pairingIn ℤ j i < 0 := by
            by_contra! hnonneg
            have hsum_nonneg : 0 ≤ (tail.map fun j => P.pairingIn ℤ j i).sum :=
              List.sum_nonneg (by simpa using hnonneg)
            omega
          have hjS : j ∈ S := htailS j hjtail
          have hnotneg : P.root j ≠ -P.root i := by
            intro hroot
            have hji : j = -i := P.root.injective (by simpa using hroot)
            rw [hji] at hjS
            exact (S.neg_mem_iff_not_mem i).mp hjS hiS
          obtain ⟨k, hkroot⟩ := P.root_add_root_mem_of_pairingIn_neg hjneg hnotneg
          let l' := k :: tail.erase j
          have hl' : ∀ a ∈ l', a ∈ S := by
            intro a ha
            rcases List.mem_cons.mp ha with rfl | ha
            · exact S.add_mem hjS hiS hkroot
            · exact htailS a (List.mem_of_mem_erase ha)
          have htailne : tail ≠ [] := List.ne_nil_of_mem hjtail
          have htailpos : 0 < tail.length := Nat.pos_of_ne_zero fun hz =>
            htailne (List.length_eq_zero_iff.mp hz)
          have hlen' : l'.length < (i :: tail).length := by
            simp [l', List.length_erase_of_mem hjtail, htailpos]
          have hsum' : (l'.map P.root).sum = 0 := by
            have hperm := List.perm_cons_erase hjtail
            have htailSum : (tail.map P.root).sum =
                P.root j + ((tail.erase j).map P.root).sum :=
              (hperm.map P.root).sum_eq
            simp only [l', List.map_cons, List.sum_cons]
            rw [hkroot]
            calc
              P.root j + P.root i + ((tail.erase j).map P.root).sum =
                  P.root i + (P.root j + ((tail.erase j).map P.root).sum) := by abel
              _ = P.root i + (tail.map P.root).sum := by rw [htailSum]
              _ = 0 := by simpa [List.map_cons, List.sum_cons] using hzero
          exact ih l'.length (by omega) l' hl' (by simp [l']) rfl hsum'

open Set IsAddIndecomposable

/-- The final assertion of GLS3 Theorem 1.8.2 does not require reducedness or
crystallographicity: a generic linear functional chooses a positive subsystem
containing any prescribed linearly independent pair of roots. -/
public lemma positiveSubsystem_contains_linearIndependent_pair
    {ι M N : Type*} [Finite ι]
    [AddCommGroup M] [Module ℝ M] [AddCommGroup N] [Module ℝ N]
    (P : RootPairing ι ℝ M N) [P.IsRootSystem]
    {i j : ι} (hli : LinearIndependent ℝ ![P.root i, P.root j]) :
    ∃ S : P.PositiveSubsystem, i ∈ S ∧ j ∈ S := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  have hij : i ≠ j := by
    intro hij
    subst j
    have hp := (LinearIndependent.pair_iff' (P.ne_zero i)).mp hli
    exact (hp 1) (by simp)
  have hliSet : LinearIndepOn ℝ P.root {i, j} := by
    rw [linearIndepOn_pair_iff P.root hij (P.ne_zero i)]
    exact (LinearIndependent.pair_iff' (P.ne_zero i)).mp hli
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ ℝ)
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one (hliSet.restrict_scalars' ℚ)
  obtain ⟨h, hh⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ) P.root (fun k => P.ne_zero k)
  let q (k : ι) : ℚ := if f (P.root k) = 0 then 0 else |h (P.root k) / f (P.root k)|
  let B : ℚ := ∑ k, q k + |h (P.root i)| + |h (P.root j)| + 1
  obtain ⟨n, hn⟩ := exists_nat_gt B
  let F : Module.Dual ℚ M := (n : ℚ) • f + h
  have hq_nonneg (k : ι) : 0 ≤ q k := by
    by_cases hfk : f (P.root k) = 0 <;> simp [q, hfk]
  have hsum_nonneg : 0 ≤ ∑ k, q k := Finset.sum_nonneg fun k _ => hq_nonneg k
  have hnq (k : ι) : q k < (n : ℚ) := by
    have hk : q k ≤ ∑ l, q l :=
      Finset.single_le_sum (fun l _ => hq_nonneg l) (Finset.mem_univ k)
    have hiabs : 0 ≤ |h (P.root i)| := abs_nonneg _
    have hjabs : 0 ≤ |h (P.root j)| := abs_nonneg _
    dsimp [B] at hn
    linarith
  have hnh_i : |h (P.root i)| < (n : ℚ) := by
    have hiabs : 0 ≤ |h (P.root i)| := abs_nonneg _
    have hjabs : 0 ≤ |h (P.root j)| := abs_nonneg _
    dsimp [B] at hn
    linarith
  have hnh_j : |h (P.root j)| < (n : ℚ) := by
    have hiabs : 0 ≤ |h (P.root i)| := abs_nonneg _
    have hjabs : 0 ≤ |h (P.root j)| := abs_nonneg _
    dsimp [B] at hn
    linarith
  have hF (k : ι) : F (P.root k) ≠ 0 := by
    by_cases hfk : f (P.root k) = 0
    · simp [F, hfk, hh k]
    · intro hzero
      have heq : (n : ℚ) = -h (P.root k) / f (P.root k) := by
        dsimp [F] at hzero
        field_simp
        linarith
      have habs : |h (P.root k) / f (P.root k)| = (n : ℚ) := by
        have hdiv : h (P.root k) / f (P.root k) = -(n : ℚ) := by
          calc
            h (P.root k) / f (P.root k) = -(-h (P.root k) / f (P.root k)) := by ring
            _ = -(n : ℚ) := by rw [← heq]
        rw [hdiv]
        simp
      have := hnq k
      simp [q, hfk, habs] at this
  have hFi : 0 < F (P.root i) := by
    have hfi : f (P.root i) = 1 := hf i (by simp)
    have := (abs_lt.mp hnh_i).1
    dsimp [F]
    simp [hfi]
    linarith
  have hFj : 0 < F (P.root j) := by
    have hfj : f (P.root j) = 1 := hf j (by simp)
    have := (abs_lt.mp hnh_j).1
    dsimp [F]
    simp [hfj]
    linarith
  let := P.indexNeg
  let S : P.PositiveSubsystem :=
    { carrier := {k | 0 < F (P.root k)}
      add_mem := by
        intro a b k ha hb hk
        change 0 < F (P.root a) at ha
        change 0 < F (P.root b) at hb
        change 0 < F (P.root k)
        rw [hk]
        rw [map_add]
        linarith
      mem_xor_neg := by
        intro k
        have hneg : F (P.root (P.reflectionPerm k k)) = -F (P.root k) := by
          simp
        by_cases hk : 0 < F (P.root k)
        · apply Or.inl
          constructor
          · exact hk
          · change ¬ 0 < F (P.root (P.reflectionPerm k k))
            rw [hneg]
            linarith
        · have hkneg : F (P.root k) < 0 := lt_of_le_of_ne (le_of_not_gt hk) (hF k)
          apply Or.inr
          constructor
          · change 0 < F (P.root (P.reflectionPerm k k))
            rw [hneg]
            linarith
          · exact hk }
  exact ⟨S, hFi, hFj⟩

open Set

/-- Two bases with the same support are equal. -/
@[ext]
public lemma _root_.RootPairing.Base.ext_support
    {ι R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} {b c : P.Base} (h : b.support = c.support) : b = c := by
  cases b
  cases c
  simp_all

/-- Transport a base by an automorphism of the root pairing. -/
public noncomputable def _root_.RootPairing.Base.mapAut
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (g : RootPairing.Aut P) (b : P.Base) : P.Base :=
  RootPairing.Base.mk' P (g.indexEquiv '' (b.support : Set ι)) (by
    have hmap : LinearIndepOn R (g.weightMap ∘ P.root) (b.support : Set ι) :=
      b.linearIndepOn_root.map_injOn g.weightMap g.bijective_weightMap.injective.injOn
    have hcomp : LinearIndepOn R (P.root ∘ g.indexEquiv) (b.support : Set ι) :=
      hmap.congr (fun i _ => by
        simpa [Function.comp_apply] using
          RootPairing.Hom.root_weightMap_apply P P i g.toHom)
    exact LinearIndepOn.image_of_comp g.indexEquiv P.root hcomp) (by
      intro i
      let k := g.indexEquiv.symm i
      have hk := b.root_mem_or_neg_mem k
      have hmap (x : M) (hx : x ∈ AddSubmonoid.closure (P.root '' (b.support : Set ι))) :
          g.weightMap x ∈ AddSubmonoid.closure
            (P.root '' (g.indexEquiv '' (b.support : Set ι))) := by
        induction hx using AddSubmonoid.closure_induction with
        | mem x hx =>
            rcases hx with ⟨j, hj, rfl⟩
            exact AddSubmonoid.subset_closure ⟨g.indexEquiv j, ⟨j, hj, rfl⟩,
              (RootPairing.Hom.root_weightMap_apply P P j g.toHom).symm⟩
        | zero => simp
        | add x y hx hy hx' hy' => simpa using AddSubmonoid.add_mem _ hx' hy'
      have hroot : g.weightMap (P.root k) = P.root i := by
        simpa [k] using RootPairing.Hom.root_weightMap_apply P P k g.toHom
      rcases hk with hk | hk
      · left
        rw [← hroot]
        exact hmap _ hk
      · right
        rw [← hroot, ← map_neg]
        exact hmap _ hk)

@[simp]
public lemma _root_.RootPairing.Base.mem_mapAut_support
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (g : RootPairing.Aut P) (b : P.Base) (i : ι) :
    i ∈ (RootPairing.Base.mapAut g b).support ↔ g.indexEquiv.symm i ∈ b.support := by
  change i ∈ (Set.toFinite (g.indexEquiv '' (b.support : Set ι))).toFinset ↔ _
  simp

public noncomputable instance _root_.RootPairing.Base.baseSMul
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] :
    SMul (RootPairing.Aut P) P.Base := ⟨RootPairing.Base.mapAut⟩

public noncomputable instance _root_.RootPairing.Base.baseMulAction
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced] :
    MulAction (RootPairing.Aut P) P.Base where
  one_smul b := by
    change RootPairing.Base.mapAut 1 b = b
    apply RootPairing.Base.ext_support
    ext i
    rw [RootPairing.Base.mem_mapAut_support]
    simp
  mul_smul g h b := by
    change RootPairing.Base.mapAut (g * h) b =
      RootPairing.Base.mapAut g (RootPairing.Base.mapAut h b)
    apply RootPairing.Base.ext_support
    ext i
    rw [RootPairing.Base.mem_mapAut_support, RootPairing.Base.mem_mapAut_support,
      RootPairing.Base.mem_mapAut_support]
    simp

public lemma _root_.RootPairing.Base.isPos_mapAut_of
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (g : RootPairing.Aut P) (b : P.Base) {i : ι} (hi : b.IsPos i) :
    (RootPairing.Base.mapAut g b).IsPos (g.indexEquiv i) := by
  rw [_root_.RootPairing.Base.isPos_iff_root_mem_closure] at hi ⊢
  have hmap (x : M) (hx : x ∈ AddSubmonoid.closure (P.root '' (b.support : Set ι))) :
      g.weightMap x ∈ AddSubmonoid.closure
        (P.root '' ((RootPairing.Base.mapAut g b).support : Set ι)) := by
    induction hx using AddSubmonoid.closure_induction with
    | mem x hx =>
        rcases hx with ⟨j, hj, rfl⟩
        exact AddSubmonoid.subset_closure
          ⟨g.indexEquiv j, by
              change g.indexEquiv j ∈ (RootPairing.Base.mapAut g b).support
              rw [RootPairing.Base.mem_mapAut_support]
              simpa using hj,
            (RootPairing.Hom.root_weightMap_apply P P j g.toHom).symm⟩
    | zero => simp
    | add x y hx hy hx' hy' => simpa using AddSubmonoid.add_mem _ hx' hy'
  convert hmap _ hi using 1
  exact (RootPairing.Hom.root_weightMap_apply P P i g.toHom).symm

@[simp]
public lemma _root_.RootPairing.Base.isPos_mapAut_iff
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (g : RootPairing.Aut P) (b : P.Base) (i : ι) :
    (RootPairing.Base.mapAut g b).IsPos i ↔ b.IsPos (g.indexEquiv.symm i) := by
  constructor
  · intro hi
    have h := RootPairing.Base.isPos_mapAut_of g⁻¹ (RootPairing.Base.mapAut g b) hi
    have hb : RootPairing.Base.mapAut g⁻¹ (RootPairing.Base.mapAut g b) = b := by
      change g⁻¹ • (g • b) = b
      simp
    rw [hb] at h
    simpa using h
  · intro hi
    have h := RootPairing.Base.isPos_mapAut_of g b hi
    simpa using h

public lemma _root_.RootPairing.Base.isPos_mapReflection_iff
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) {j : ι} (hj : j ∈ b.support) (i : ι) :
    (RootPairing.Base.mapAut (RootPairing.Equiv.reflection P j) b).IsPos i ↔
      (b.IsPos i ∧ i ≠ j) ∨ i = P.reflectionPerm j j := by
  let := P.indexNeg
  rw [RootPairing.Base.isPos_mapAut_iff]
  simp only [RootPairing.Equiv.reflection_indexEquiv, P.reflectionPerm_symm]
  constructor
  · intro hi
    by_cases hipos : b.IsPos i
    · left
      refine ⟨hipos, ?_⟩
      intro hij
      subst i
      have hneg : b.IsPos (-j) := by simpa using hi
      exact (RootPairing.Base.IsPos.neg_iff_not b j).mp hneg (b.isPos_of_mem_support hj)
    · right
      have huniq : P.reflectionPerm j i = j := by
        by_contra hne
        exact hipos (by simpa using hi.reflectionPerm hj hne)
      have := congrArg (P.reflectionPerm j) huniq
      simpa using this
  · rintro (⟨hi, hij⟩ | rfl)
    · exact hi.reflectionPerm hj hij
    · simpa using b.isPos_of_mem_support hj

open Set IsAddIndecomposable

/-- A reduced crystallographic root system admits a positive subsystem
containing any linearly independent root pair.

This is GLS3, Theorem 1.8.2. -/
public theorem positiveSubsystem_contains_linearIndependent_pair_of_reducedCrystallographic
    {ι R M N : Type*} [Finite ι] [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (P : RootPairing ι R M N) [P.IsRootSystem] [P.IsCrystallographic] [P.IsReduced]
    {i j : ι} (hli : LinearIndependent R ![P.root i, P.root j]) :
    ∃ S : P.PositiveSubsystem, i ∈ S ∧ j ∈ S := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let _i : Module ℚ M := Module.compHom M (algebraMap ℚ R)
  let _i : Module ℚ N := Module.compHom N (algebraMap ℚ R)
  have hij : i ≠ j := by
    intro hij
    subst j
    have hp := (LinearIndependent.pair_iff' (P.ne_zero i)).mp hli
    exact (hp 1) (by simp)
  have hliSet : LinearIndepOn R P.root {i, j} := by
    rw [linearIndepOn_pair_iff P.root hij (P.ne_zero i)]
    exact (LinearIndependent.pair_iff' (P.ne_zero i)).mp hli
  obtain ⟨f, hf⟩ := Module.exists_dual_forall_apply_eq_one (hliSet.restrict_scalars' ℚ)
  obtain ⟨h, hh⟩ := Module.exists_dual_forall_apply_ne_zero (K := ℚ) P.root (fun k => by
    let := P.indexNeg
    exact P.ne_zero k)
  let q (k : ι) : ℚ := if f (P.root k) = 0 then 0 else |h (P.root k) / f (P.root k)|
  let B : ℚ := ∑ k, q k + |h (P.root i)| + |h (P.root j)| + 1
  obtain ⟨n, hn⟩ := exists_nat_gt B
  let F : Module.Dual ℚ M := (n : ℚ) • f + h
  have hq_nonneg (k : ι) : 0 ≤ q k := by
    by_cases hfk : f (P.root k) = 0 <;> simp [q, hfk]
  have hsum_nonneg : 0 ≤ ∑ k, q k := Finset.sum_nonneg fun k _ => hq_nonneg k
  have hnq (k : ι) : q k < (n : ℚ) := by
    have hk : q k ≤ ∑ l, q l :=
      Finset.single_le_sum (fun l _ => hq_nonneg l) (Finset.mem_univ k)
    have hiabs : 0 ≤ |h (P.root i)| := abs_nonneg _
    have hjabs : 0 ≤ |h (P.root j)| := abs_nonneg _
    dsimp [B] at hn
    linarith
  have hnh_i : |h (P.root i)| < (n : ℚ) := by
    have hiabs : 0 ≤ |h (P.root i)| := abs_nonneg _
    have hjabs : 0 ≤ |h (P.root j)| := abs_nonneg _
    dsimp [B] at hn
    linarith
  have hnh_j : |h (P.root j)| < (n : ℚ) := by
    have hiabs : 0 ≤ |h (P.root i)| := abs_nonneg _
    have hjabs : 0 ≤ |h (P.root j)| := abs_nonneg _
    dsimp [B] at hn
    linarith
  have hF (k : ι) : F (P.root k) ≠ 0 := by
    by_cases hfk : f (P.root k) = 0
    · simp [F, hfk, hh k]
    · intro hzero
      have heq : (n : ℚ) = -h (P.root k) / f (P.root k) := by
        dsimp [F] at hzero
        field_simp
        linarith
      have habs : |h (P.root k) / f (P.root k)| = (n : ℚ) := by
        have hdiv : h (P.root k) / f (P.root k) = -(n : ℚ) := by
          calc
            h (P.root k) / f (P.root k) = -(-h (P.root k) / f (P.root k)) := by ring
            _ = -(n : ℚ) := by rw [← heq]
        rw [hdiv]
        simp
      have := hnq k
      simp [q, hfk, habs] at this
  have hFi : 0 < F (P.root i) := by
    have hfi : f (P.root i) = 1 := hf i (by simp)
    have := (abs_lt.mp hnh_i).1
    dsimp [F]
    simp [hfi]
    linarith
  have hFj : 0 < F (P.root j) := by
    have hfj : f (P.root j) = 1 := hf j (by simp)
    have := (abs_lt.mp hnh_j).1
    dsimp [F]
    simp [hfj]
    linarith
  let := P.indexNeg
  let Fa : M →+ ℚ := F
  have hFa (k : ι) : Fa (P.root k) ≠ 0 := by simpa [Fa] using hF k
  let b : P.Base := RootPairing.Base.mk' P (baseOf P.root Fa)
    (P.linearIndepOn_root_baseOf Fa hFa)
    (fun k => mem_or_neg_mem_closure_baseOf P.root Fa k (hFa k) (by simp))
  have hb_support : (b.support : Set ι) = baseOf P.root Fa := by
    change ((Set.toFinite (baseOf P.root Fa)).toFinset : Set ι) = baseOf P.root Fa
    simp
  refine ⟨b.toPositiveSubsystem, ?_, ?_⟩
  · rw [_root_.RootPairing.Base.mem_toPositiveSubsystem,
      _root_.RootPairing.Base.isPos_iff_root_mem_closure]
    rw [hb_support, AddSubmonoid.closure_image_isAddIndecomposable_baseOf]
    exact AddSubmonoid.subset_closure ⟨i, hFi, rfl⟩
  · rw [_root_.RootPairing.Base.mem_toPositiveSubsystem,
      _root_.RootPairing.Base.isPos_iff_root_mem_closure]
    rw [hb_support, AddSubmonoid.closure_image_isAddIndecomposable_baseOf]
    exact AddSubmonoid.subset_closure ⟨j, hFj, rfl⟩

open scoped BigOperators

/-- A finite nonempty matrix with diagonal entries `2` and nonpositive column
sums cannot have a positive-definite diagonal symmetrization. -/
public lemma not_diagonal_mul_posDef_of_columnSums_nonpos
    {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (hcol : ∀ i, ∑ j, A j i ≤ 0) : False := by
  have hdpos (i : κ) : 0 < d i := by
    have hi := hpos.diag_pos (i := i)
    simp [Matrix.diagonal_mul, hdiag] at hi
    omega
  let L : ℤ := ∏ i, d i
  let x : κ → ℤ := fun i => ∏ j ∈ Finset.univ.erase i, d j
  have hdx (i : κ) : d i * x i = L := by
    simpa [L, x] using Finset.mul_prod_erase Finset.univ d (Finset.mem_univ i)
  have hxpos (i : κ) : 0 < x i := by
    simp only [x]
    exact Finset.prod_pos fun j _ => hdpos j
  have hx : x ≠ 0 := by
    intro h
    have hi := congrFun h (Classical.choice inferInstance)
    have := hxpos (Classical.choice inferInstance)
    simp [hi] at this
  have hsymm := cartanSymmetrizer_entry_eq_of_diagonal_mul_posDef A d hpos
  have hmul (i : κ) :
      ((Matrix.diagonal d * A).mulVec x) i = (∑ j, A j i) * L := by
    simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_mul]
    calc
      (∑ j, d i * A i j * x j) = ∑ j, d j * A j i * x j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hsymm i j]
      _ = ∑ j, A j i * L := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← hdx j]
        ring
      _ = (∑ j, A j i) * L := by rw [Finset.sum_mul]
  have hLpos : 0 < L := by
    simp only [L]
    exact Finset.prod_pos fun i _ => hdpos i
  have hmul_nonpos (i : κ) : ((Matrix.diagonal d * A).mulVec x) i ≤ 0 := by
    rw [hmul i]
    exact mul_nonpos_of_nonpos_of_nonneg (hcol i) hLpos.le
  have hquad := hpos.dotProduct_mulVec_pos hx
  have hquad_nonpos : star x ⬝ᵥ ((Matrix.diagonal d * A).mulVec x) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    have hxi : 0 ≤ star (x i) := by simpa using (hxpos i).le
    exact mul_nonpos_of_nonneg_of_nonpos hxi (hmul_nonpos i)
  exact (not_lt_of_ge hquad_nonpos) hquad

open SimpleGraph

/-- Exact matrix entries on a path with one designated directed double bond
and simple bonds everywhere else.  All hypotheses are local matrix facts and
no classification conclusion is stored in data. -/
public lemma cartan_pathGraph_entries_of_unique_doubleBond
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    {n r : ℕ} (e : Fin n ≃ κ)
    (hpath : ∀ i j,
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj (e i) (e j) ↔
        (pathGraph n).Adj i j)
    (hr : r + 1 < n) (u v : ℤ)
    (hforward : A (e ⟨r, by omega⟩) (e ⟨r + 1, by omega⟩) = u)
    (hreverse : A (e ⟨r + 1, by omega⟩) (e ⟨r, by omega⟩) = v)
    (hsimple : ∀ {i j : Fin n}, (pathGraph n).Adj i j →
      ¬(i.val = r ∧ j.val = r + 1) →
      ¬(j.val = r ∧ i.val = r + 1) →
      A (e i) (e j) = -1 ∧ A (e j) (e i) = -1) :
    ∀ i j : Fin n, A (e i) (e j) =
      if i = j then 2 else if i.val + 1 = j.val then
        if i.val = r then u else -1
      else if j.val + 1 = i.val then
        if j.val = r then v else -1
      else 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    simp [hdiag]
  by_cases hf : i.val + 1 = j.val
  · rw [if_neg hij, if_pos hf]
    have hadj : (pathGraph n).Adj i j := by
      rw [pathGraph_adj]
      exact Or.inl hf
    by_cases hir : i.val = r
    · rw [if_pos hir]
      have hr0 : r < n := by omega
      have hjval : j.val = r + 1 := by omega
      have hi : i = ⟨r, hr0⟩ := Fin.ext hir
      have hj : j = ⟨r + 1, hr⟩ := Fin.ext hjval
      simpa [hi, hj] using hforward
    · rw [if_neg hir]
      exact (hsimple hadj (by omega) (by omega)).1
  by_cases hr' : j.val + 1 = i.val
  · rw [if_neg hij, if_neg hf, if_pos hr']
    have hadj : (pathGraph n).Adj i j := by
      rw [pathGraph_adj]
      exact Or.inr hr'
    by_cases hjr : j.val = r
    · rw [if_pos hjr]
      have hr0 : r < n := by omega
      have hival : i.val = r + 1 := by omega
      have hi : i = ⟨r + 1, hr⟩ := Fin.ext hival
      have hj : j = ⟨r, hr0⟩ := Fin.ext hjr
      simpa [hi, hj] using hreverse
    · rw [if_neg hjr]
      exact (hsimple hadj (by omega) (by omega)).1
  rw [if_neg hij, if_neg hf, if_neg hr']
  exact (cartan_pathGraph_nonadjacent_entries_eq_zero
    A hrank e hpath hij (by simp [pathGraph_adj, hf, hr'])).1

/-- Preconnectedness of the undirected support graph recovers the Cartan
closure-induction principle when rank-two nonzero entries occur in both
orientations. -/
public lemma cartanClosureInduction_of_support_preconnected
    {κ : Type*} (A : Matrix κ κ ℤ)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpre : (SimpleGraph.fromRel fun i j => A i j ≠ 0).Preconnected) :
    ∀ (p : κ → Prop) {i j : κ}, p i →
      (∀ i j, p i → A j i ≠ 0 → p j) → p j := by
  intro p i j hpi hclosed
  have hreach := hpre i j
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
  induction hreach with
  | refl => exact hpi
  | @tail b c hreach hbc ih =>
      change (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj b c at hbc
      rw [SimpleGraph.fromRel_adj] at hbc
      apply hclosed b c ih
      rcases hbc.2 with hforward | hreverse
      · have hb := cartan_rankTwo_nonzero_bounds A hrank hbc.1 hforward
        omega
      · exact hreverse

/-- A degree-one Cartan support vertex has a unique neighbor, and their two
directed entries form one of the five nonzero rank-two Cartan bonds. -/
public lemma cartanSupport_leaf_existsUnique_rankTwoNeighbor
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ)
    [DecidableRel (fun i j : κ => A i j ≠ 0)]
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (v : κ)
    (hdeg : (SimpleGraph.fromRel fun i j => A i j ≠ 0).degree v = 1) :
    ∃! u,
      (A v u = -1 ∧ A u v = -1) ∨
      (A v u = -1 ∧ A u v = -2) ∨
      (A v u = -2 ∧ A u v = -1) ∨
      (A v u = -1 ∧ A u v = -3) ∨
      (A v u = -3 ∧ A u v = -1) := by
  classical
  let G : SimpleGraph κ := SimpleGraph.fromRel fun i j => A i j ≠ 0
  have hdegG : G.degree v = 1 := hdeg
  obtain ⟨u, hadj, huniq⟩ := SimpleGraph.degree_eq_one_iff_existsUnique_adj.mp hdegG
  have hne : v ≠ u := hadj.ne
  have hadj' : (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj v u := hadj
  rw [SimpleGraph.fromRel_adj] at hadj'
  have hnonzero : A v u ≠ 0 := by
    rcases hadj'.2 with hforward | hreverse
    · exact hforward
    · have hb := cartan_rankTwo_nonzero_bounds A hrank hne.symm hreverse
      omega
  have hbond :
      (A v u = -1 ∧ A u v = -1) ∨
      (A v u = -1 ∧ A u v = -2) ∨
      (A v u = -2 ∧ A u v = -1) ∨
      (A v u = -1 ∧ A u v = -3) ∨
      (A v u = -3 ∧ A u v = -1) := by
    rcases hrank v u hne with h0 | h11 | h12 | h21 | h13 | h31
    · exact (hnonzero h0.1).elim
    · exact Or.inl h11
    · exact Or.inr (Or.inl h12)
    · exact Or.inr (Or.inr (Or.inl h21))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h13)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h31)))
  refine ⟨u, hbond, ?_⟩
  intro w hw
  apply huniq w
  rw [SimpleGraph.fromRel_adj]
  have hvw : v ≠ w := by
    intro hvw
    subst w
    rcases hw with hw | hw | hw | hw | hw
    all_goals have := hdiag v; omega
  have hnz : A v w ≠ 0 := by
    rcases hw with hw | hw | hw | hw | hw
    all_goals omega
  exact ⟨hvw, Or.inl hnz⟩

open SimpleGraph

/-- Under an exact path-graph numbering of Cartan support, adjacent path
positions carry one of the five nonzero ordered rank-two Cartan bonds. -/
public lemma cartan_pathGraph_adjacent_rankTwoBond
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    {n : ℕ} (e : Fin n ≃ κ)
    (hpath : ∀ i j,
      (SimpleGraph.fromRel fun i j => A i j ≠ 0).Adj (e i) (e j) ↔
        (pathGraph n).Adj i j)
    {i j : Fin n} (hadj : (pathGraph n).Adj i j) :
    (A (e i) (e j) = -1 ∧ A (e j) (e i) = -1) ∨
    (A (e i) (e j) = -1 ∧ A (e j) (e i) = -2) ∨
    (A (e i) (e j) = -2 ∧ A (e j) (e i) = -1) ∨
    (A (e i) (e j) = -1 ∧ A (e j) (e i) = -3) ∨
    (A (e i) (e j) = -3 ∧ A (e j) (e i) = -1) := by
  have hsupp := (hpath i j).mpr hadj
  have hij : e i ≠ e j := e.injective.ne hadj.ne
  have hforward : A (e i) (e j) ≠ 0 := by
    rw [SimpleGraph.fromRel_adj] at hsupp
    rcases hsupp.2 with hforward | hreverse
    · exact hforward
    · have hb := cartan_rankTwo_nonzero_bounds A hrank hij.symm hreverse
      omega
  rcases hrank (e i) (e j) hij with h0 | h11 | h12 | h21 | h13 | h31
  · exact (hforward h0.1).elim
  · exact Or.inl h11
  · exact Or.inr (Or.inl h12)
  · exact Or.inr (Or.inr (Or.inl h21))
  · exact Or.inr (Or.inr (Or.inr (Or.inl h13)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr h31)))

/-- If a numbered Cartan path contains a heavy edge, it has a first heavy
edge, and every earlier edge has both directed entries equal to `-1`. -/
public lemma cartan_path_exists_first_heavy_edge
    {κ : Type*} [DecidableEq κ]
    (A : Matrix κ κ ℤ)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    {n : ℕ} (f : Fin (n + 1) ↪ κ)
    (hedge : ∀ r : Fin n, A (f r.castSucc) (f r.succ) ≠ 0)
    (q : ℕ) (hqpos : 0 < q) (hqle : q ≤ n)
    (hqheavy : 2 ≤
      A (f ⟨q - 1, by omega⟩) (f ⟨q, by omega⟩) *
      A (f ⟨q, by omega⟩) (f ⟨q - 1, by omega⟩)) :
    ∃ m : Fin (n + 1), 0 < m.val ∧ m.val ≤ q ∧
      (∀ r : Fin (n + 1), 0 < r.val → r.val < m.val →
        A (f ⟨r.val - 1, by omega⟩) (f r) = -1 ∧
        A (f r) (f ⟨r.val - 1, by omega⟩) = -1) ∧
      2 ≤ A (f ⟨m.val - 1, by omega⟩) (f m) *
        A (f m) (f ⟨m.val - 1, by omega⟩) := by
  let P : ℕ → Prop := fun m =>
    ∃ hm : m < n + 1, 0 < m ∧
      2 ≤ A (f ⟨m - 1, by omega⟩) (f ⟨m, hm⟩) *
        A (f ⟨m, hm⟩) (f ⟨m - 1, by omega⟩)
  have hqP : P q := by
    refine ⟨by omega, hqpos, ?_⟩
    simpa using hqheavy
  have hex : ∃ m, P m := ⟨q, hqP⟩
  let k := Nat.find hex
  obtain ⟨hklt, hkpos, hkheavy⟩ := Nat.find_spec hex
  let m : Fin (n + 1) := ⟨k, hklt⟩
  have hkleq : k ≤ q := by
    exact Nat.find_min' hex hqP
  refine ⟨m, hkpos, hkleq, ?_, ?_⟩
  · intro r hrpos hrk
    let s : Fin n := ⟨r.val - 1, by omega⟩
    have hne : f ⟨r.val - 1, by omega⟩ ≠ f r := by
      apply f.injective.ne
      intro h
      have hv : r.val - 1 = r.val := congrArg Fin.val h
      omega
    have hnz : A (f ⟨r.val - 1, by omega⟩) (f r) ≠ 0 := by
      have hs0 : s.castSucc = (⟨r.val - 1, by omega⟩ : Fin (n + 1)) := by
        apply Fin.ext
        rfl
      have hs1 : s.succ = r := by
        apply Fin.ext
        simp [s]
        omega
      rw [← hs0, ← hs1]
      exact hedge s
    rcases hrank (f ⟨r.val - 1, by omega⟩) (f r) hne with
      h0 | h11 | h12 | h21 | h13 | h31
    · exact (hnz h0.1).elim
    · exact h11
    all_goals
      exfalso
      apply Nat.find_min hex hrk
      refine ⟨r.isLt, hrpos, ?_⟩
      simp_all [P]
  · simpa [m] using hkheavy

/-- Every two-vertex subdiagram of a base of a finite reduced crystallographic root system is one
of the standard rank-two diagrams, with the two orientations listed separately.

This is GLS3, Theorem 1.8.7. -/
public theorem base_rankTwo_cartanClassification
    {ι R M N : Type*} [Finite ι]
    [Field R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsRootSystem]
    [P.IsCrystallographic] [P.IsReduced] (b : P.Base)
    (i j : b.support) (hij : i ≠ j) :
    (b.cartanMatrix i j = 0 ∧ b.cartanMatrix j i = 0) ∨
    (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -1) ∨
    (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -2) ∨
    (b.cartanMatrix i j = -2 ∧ b.cartanMatrix j i = -1) ∨
    (b.cartanMatrix i j = -1 ∧ b.cartanMatrix j i = -3) ∨
    (b.cartanMatrix i j = -3 ∧ b.cartanMatrix j i = -1) := by
  have hi := b.cartanMatrix_mem_of_ne hij
  have hj := b.cartanMatrix_mem_of_ne hij.symm
  have hp := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i j
  change (b.cartanMatrix i j, b.cartanMatrix j i) ∈
    ({(0, 0), (1, 1), (-1, -1), (1, 2), (2, 1), (-1, -2), (-2, -1), (1, 3),
      (3, 1), (-1, -3), (-3, -1), (2, 2), (-2, -2)} : Set (ℤ × ℤ)) at hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hi hj hp
  have hneg : P.root i ≠ -P.root j :=
    b.root_ne_neg_of_ne i.property j.property (by simpa using hij)
  have hn22 : ¬ (b.cartanMatrix i j = -2 ∧ b.cartanMatrix j i = -2) := by
    intro h
    exact hneg ((P.pairingIn_neg_two_neg_two_iff ℤ i j).mp h)
  aesop

open Set

/-- The reduced crystallographic case of Theorem 1.8.3(b): the reflections
in the roots of a fundamental system generate the Weyl group. -/
public theorem weylGroup_generated_by_simpleReflections
    {ι R M N : Type*} [Finite ι] [CommRing R] [IsDomain R] [CharZero R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced]
    (b : P.Base) :
    P.weylGroup = Subgroup.closure
      (Set.range fun j : b.support => RootPairing.Equiv.reflection P j) := by
  apply le_antisymm
  · rw [RootPairing.weylGroup, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    let S : Subgroup (RootPairing.Aut P) := Subgroup.closure
      (Set.range fun j : b.support => RootPairing.Equiv.reflection P j)
    change RootPairing.Equiv.reflection P i ∈ S
    apply b.induction_reflect i
    · intro i hi
      rw [_root_.RootPairing.Equiv.reflection_reflectionPerm]
      exact S.mul_mem (S.mul_mem hi hi) hi
    · intro i hi
      exact Subgroup.subset_closure ⟨⟨i, hi⟩, rfl⟩
    · intro i j hi hj
      have hjS : RootPairing.Equiv.reflection P j ∈ S :=
        Subgroup.subset_closure ⟨⟨j, hj⟩, rfl⟩
      rw [_root_.RootPairing.Equiv.reflection_reflectionPerm]
      exact S.mul_mem (S.mul_mem hjS hi) hjS
  · rw [Subgroup.closure_le]
    rintro _ ⟨j, rfl⟩
    exact P.reflection_mem_weylGroup j

set_option maxHeartbeats 800000 in
/-- The standard positive null vector for an affine-`D` path with two leaves at
each endpoint.  The hypotheses list the displayed row entries and the zero
entries needed to evaluate every row of the principal submatrix. -/
public lemma affineD_mulVec_eq_zero_of_row_entries
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    {m : ℕ} (hm : 0 < m) (A : Matrix κ κ ℤ) (e : Fin (m + 5) ↪ κ)
    (hdiag : ∀ i, A (e i) (e i) = 2)
    (hleft₁ : A (e 0) (e 1) = -1)
    (hright₁ : A (e ⟨m, by omega⟩) (e ⟨m - 1, by omega⟩) = -1)
    (ha₁ : A (e 0) (e ⟨m + 1, by omega⟩) = -1)
    (ha₂ : A (e 0) (e ⟨m + 2, by omega⟩) = -1)
    (hā₁ : A (e ⟨m + 1, by omega⟩) (e 0) = -1)
    (hā₂ : A (e ⟨m + 2, by omega⟩) (e 0) = -1)
    (hb₁ : A (e ⟨m, by omega⟩) (e ⟨m + 3, by omega⟩) = -1)
    (hb₂ : A (e ⟨m, by omega⟩) (e ⟨m + 4, by omega⟩) = -1)
    (hback₁ : A (e ⟨m + 3, by omega⟩) (e ⟨m, by omega⟩) = -1)
    (hback₂ : A (e ⟨m + 4, by omega⟩) (e ⟨m, by omega⟩) = -1)
    (hpath₁ : ∀ (i : Fin (m + 5)) (hi : i.val < m),
      A (e i) (e ⟨i.val + 1, by omega⟩) = -1)
    (hpath₂ : ∀ (i : Fin (m + 5)) (hi : i.val < m),
      A (e ⟨i.val + 1, by omega⟩) (e i) = -1)
    (hzero₀ : ∀ j, j ≠ 0 → j ≠ 1 → j ≠ ⟨m + 1, by omega⟩ →
      j ≠ ⟨m + 2, by omega⟩ → A (e 0) (e j) = 0)
    (hzeroₘ : ∀ j, j ≠ ⟨m, by omega⟩ → j ≠ ⟨m - 1, by omega⟩ →
      j ≠ ⟨m + 3, by omega⟩ → j ≠ ⟨m + 4, by omega⟩ →
      A (e ⟨m, by omega⟩) (e j) = 0)
    (hzeroPath : ∀ i j, 0 < i.val → i.val < m → i ≠ j →
      j.val + 1 ≠ i.val → i.val + 1 ≠ j.val → A (e i) (e j) = 0)
    (hzeroA₁ : ∀ j, j ≠ ⟨m + 1, by omega⟩ → j ≠ 0 →
      A (e ⟨m + 1, by omega⟩) (e j) = 0)
    (hzeroA₂ : ∀ j, j ≠ ⟨m + 2, by omega⟩ → j ≠ 0 →
      A (e ⟨m + 2, by omega⟩) (e j) = 0)
    (hzeroB₁ : ∀ j, j ≠ ⟨m + 3, by omega⟩ → j ≠ ⟨m, by omega⟩ →
      A (e ⟨m + 3, by omega⟩) (e j) = 0)
    (hzeroB₂ : ∀ j, j ≠ ⟨m + 4, by omega⟩ → j ≠ ⟨m, by omega⟩ →
      A (e ⟨m + 4, by omega⟩) (e j) = 0) :
    ∃ x : Fin (m + 5) → ℤ, x ≠ 0 ∧ (A.submatrix e e).mulVec x = 0 := by
  let x : Fin (m + 5) → ℤ := fun i => if i.val ≤ m then 2 else 1
  have hx : x ≠ 0 := by
    intro h
    have h0 := congrFun h (0 : Fin (m + 5))
    simp [x] at h0
  have hker : (A.submatrix e e).mulVec x = 0 := by
    funext i
    change (∑ j : Fin (m + 5), A (e i) (e j) * x j) = 0
    by_cases hi0 : i.val = 0
    · let i0 : Fin (m + 5) := ⟨0, by omega⟩
      let i1 : Fin (m + 5) := ⟨1, by omega⟩
      let il1 : Fin (m + 5) := ⟨m + 1, by omega⟩
      let il2 : Fin (m + 5) := ⟨m + 2, by omega⟩
      have hi : i = i0 := by apply Fin.ext; simp [i0, hi0]
      rw [hi]
      rw [fin_sum_support_four (fun j => A (e i0) (e j) * x j)
        i0 i1 il1 il2
        (by intro h; have := congrArg Fin.val h; simp only [i0, i1] at this; omega)
        (by intro h; have := congrArg Fin.val h; simp only [i0, il1] at this; omega)
        (by intro h; have := congrArg Fin.val h; simp only [i0, il2] at this; omega)
        (by intro h; have := congrArg Fin.val h; simp only [i1, il1] at this; omega)
        (by intro h; have := congrArg Fin.val h; simp only [i1, il2] at this; omega)
        (by intro h; have := congrArg Fin.val h; simp only [il1, il2] at this; omega)
        (by
          intro j hji0 hji1 hjil1 hjil2
          have hz := hzero₀ j (by simpa [i0] using hji0)
            (by simpa [i1] using hji1) (by simpa [il1] using hjil1)
            (by simpa [il2] using hjil2)
          rw [show A (e i0) (e j) = 0 by simpa [i0] using hz]
          · simp [x]
        )]
      have hdiag0 : A (e i0) (e i0) = 2 := by simpa [i0] using hdiag 0
      have hleft : A (e i0) (e i1) = -1 := by simpa [i0, i1] using hleft₁
      have ha1 : A (e i0) (e il1) = -1 := by simpa [i0, il1] using ha₁
      have ha2 : A (e i0) (e il2) = -1 := by simpa [i0, il2] using ha₂
      rw [hdiag0, hleft, ha1, ha2]
      have hm1 : 1 ≤ m := by omega
      simp [x, i0, i1, il1, il2, hm1]
    · by_cases him : i.val = m
      · let im : Fin (m + 5) := ⟨m, by omega⟩
        let im1 : Fin (m + 5) := ⟨m - 1, by omega⟩
        let il3 : Fin (m + 5) := ⟨m + 3, by omega⟩
        let il4 : Fin (m + 5) := ⟨m + 4, by omega⟩
        have hi : i = im := by apply Fin.ext; simp [im, him]
        rw [hi]
        rw [fin_sum_support_four (fun j => A (e im) (e j) * x j)
          im im1 il3 il4
          (by intro h; have := congrArg Fin.val h; simp only [im, im1] at this; omega)
          (by intro h; have := congrArg Fin.val h; simp only [im, il3] at this; omega)
          (by intro h; have := congrArg Fin.val h; simp only [im, il4] at this; omega)
          (by intro h; have := congrArg Fin.val h; simp only [im1, il3] at this; omega)
          (by intro h; have := congrArg Fin.val h; simp only [im1, il4] at this; omega)
          (by intro h; have := congrArg Fin.val h; simp only [il3, il4] at this; omega)
          (by
            intro j hjim hjim1 hjil3 hjil4
            have hz := hzeroₘ j (by simpa [im] using hjim)
              (by simpa [im1] using hjim1) (by simpa [il3] using hjil3)
              (by simpa [il4] using hjil4)
            rw [show A (e im) (e j) = 0 by simpa [im] using hz]
            · simp [x]
          )]
        have hdiagm : A (e im) (e im) = 2 := by simpa [im] using hdiag ⟨m, by omega⟩
        have hright : A (e im) (e im1) = -1 := by simpa [im, im1] using hright₁
        have hb1 : A (e im) (e il3) = -1 := by simpa [im, il3] using hb₁
        have hb2 : A (e im) (e il4) = -1 := by simpa [im, il4] using hb₂
        rw [hdiagm, hright, hb1, hb2]
        simp [x, im, im1, il3, il4]
      · by_cases hle : i.val ≤ m
        · have hpos : 0 < i.val := by omega
          have hlt : i.val < m := by omega
          let im1 : Fin (m + 5) := ⟨i.val - 1, by omega⟩
          let ip1 : Fin (m + 5) := ⟨i.val + 1, by omega⟩
          have hieq : i ≠ im1 := by intro h; have := congrArg Fin.val h; simp only [im1] at this; omega
          have hieq' : i ≠ ip1 := by intro h; have := congrArg Fin.val h; simp only [ip1] at this; omega
          have hpm : im1 ≠ ip1 := by intro h; have := congrArg Fin.val h; simp only [im1, ip1] at this; omega
          have hpath₂' : A (e i) (e im1) = -1 := by
            have him1lt : im1.val < m := by simp [im1]; omega
            have hh := hpath₂ im1 him1lt
            have hi_sub : i.val - 1 + 1 = i.val := by omega
            simpa [im1, hi_sub] using hh
          have hpath₁' : A (e i) (e ip1) = -1 := by simpa [ip1] using hpath₁ i hlt
          rw [fin_sum_support_three (fun j => A (e i) (e j) * x j) i im1 ip1 hieq hieq' hpm]
          · rw [hdiag i, hpath₂', hpath₁']
            have him1_le : im1.val ≤ m := by simp [im1]; omega
            have hip1_le : ip1.val ≤ m := by simp [ip1]; omega
            simp [x, hle, him1_le, hip1_le, im1, ip1]
          · intro j hji hjm1 hjp1
            have hjm1' : j.val + 1 ≠ i.val := by
              intro h
              apply hjm1
              apply Fin.ext
              simp [im1]
              omega
            have hjp1' : i.val + 1 ≠ j.val := by
              intro h
              apply hjp1
              apply Fin.ext
              simp [ip1]
              omega
            rw [hzeroPath i j hpos hlt (Ne.symm hji) hjm1' hjp1']
            · simp
        · have hcases : i.val = m + 1 ∨ i.val = m + 2 ∨ i.val = m + 3 ∨ i.val = m + 4 := by omega
          rcases hcases with h1 | h2 | h3 | h4
          · let il : Fin (m + 5) := ⟨m + 1, by omega⟩
            have hi : i = il := by apply Fin.ext; simp [il, h1]
            rw [hi]
            rw [fin_sum_support_two (fun j => A (e il) (e j) * x j) il 0
              (by intro h; have := congrArg Fin.val h; simp [il] at this)]
            · have ha : A (e il) (e 0) = -1 := by simpa [il] using hā₁
              rw [hdiag il, ha]
              simp [x, il]
            · intro j hjil hj0
              have hz := hzeroA₁ j (by simpa [il] using hjil) (by simpa using hj0)
              rw [show A (e il) (e j) = 0 by simpa [il] using hz]
              simp [x]
          · let il : Fin (m + 5) := ⟨m + 2, by omega⟩
            have hi : i = il := by apply Fin.ext; simp [il, h2]
            rw [hi]
            rw [fin_sum_support_two (fun j => A (e il) (e j) * x j) il 0
              (by intro h; have := congrArg Fin.val h; simp [il] at this)]
            · have ha : A (e il) (e 0) = -1 := by simpa [il] using hā₂
              rw [hdiag il, ha]
              simp [x, il]
            · intro j hjil hj0
              have hz := hzeroA₂ j (by simpa [il] using hjil) (by simpa using hj0)
              rw [show A (e il) (e j) = 0 by simpa [il] using hz]
              simp [x]
          · let il : Fin (m + 5) := ⟨m + 3, by omega⟩
            let im : Fin (m + 5) := ⟨m, by omega⟩
            have hi : i = il := by apply Fin.ext; simp [il, h3]
            rw [hi]
            rw [fin_sum_support_two (fun j => A (e il) (e j) * x j) il im
              (by intro h; have := congrArg Fin.val h; simp [il, im] at this)]
            · have hb : A (e il) (e im) = -1 := by simpa [il, im] using hback₁
              rw [hdiag il, hb]
              simp [x, il, im]
            · intro j hjil hjim
              have hz := hzeroB₁ j (by simpa [il] using hjil) (by simpa [im] using hjim)
              rw [show A (e il) (e j) = 0 by simpa [il] using hz]
              simp [x]
          · let il : Fin (m + 5) := ⟨m + 4, by omega⟩
            let im : Fin (m + 5) := ⟨m, by omega⟩
            have hi : i = il := by apply Fin.ext; simp [il, h4]
            rw [hi]
            rw [fin_sum_support_two (fun j => A (e il) (e j) * x j) il im
              (by intro h; have := congrArg Fin.val h; simp [il, im] at this)]
            · have hb : A (e il) (e im) = -1 := by simpa [il, im] using hback₂
              rw [hdiag il, hb]
              simp [x, il, im]
            · intro j hjil hjim
              have hz := hzeroB₂ j (by simpa [il] using hjil) (by simpa [im] using hjim)
              rw [show A (e il) (e j) = 0 by simpa [il] using hz]
              simp [x]
  exact ⟨x, hx, hker⟩

open scoped BigOperators

set_option maxHeartbeats 800000 in
/-- A degree-three Cartan branch whose first non-simple bond has product at least two cannot be positive definite. -/
public lemma not_cartan_branch_single_heavy_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {m : ℕ} (hm : 0 < m) (e : Fin (m + 4) ↪ κ) (u v : ℤ)
    (hA : ∀ i j : Fin (m + 4), A (e i) (e j) =
      if i = j then 2 else if
        ((i.val = 0 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 0) ∨
         (i.val = 1 ∧ j.val = 2) ∨ (i.val = 2 ∧ j.val = 1)) then -1 else if
        (2 ≤ i.val ∧ i.val + 1 = j.val ∧ j.val ≤ m + 2) then -1 else if
        (2 ≤ j.val ∧ j.val + 1 = i.val ∧ i.val ≤ m + 2) then -1 else if
        (i.val = m + 2 ∧ j.val = m + 3) then u else if
        (i.val = m + 3 ∧ j.val = m + 2) then v else 0)
    (hheavy : 2 ≤ u * v) : False := by
  let ic : Fin (m + 4) := ⟨2, by omega⟩
  let ih : Fin (m + 4) := ⟨m + 2, by omega⟩
  let ie : Fin (m + 4) := ⟨m + 3, by omega⟩
  let il0 : Fin (m + 4) := ⟨0, by omega⟩
  let il1 : Fin (m + 4) := ⟨1, by omega⟩
  let x : Fin (m + 4) → ℤ := fun i => if i = il0 ∨ i = il1 then 1 else if i = ie then -v else 2
  have hm0 : m ≠ 0 := by omega
  have h0c : il0 ≠ ic := by intro h; have hv := congrArg Fin.val h; simp [il0, ic] at hv
  have h0h : il0 ≠ ih := by intro h; have hv := congrArg Fin.val h; simp [il0, ih] at hv
  have h0e : il0 ≠ ie := by intro h; have hv := congrArg Fin.val h; simp [il0, ie] at hv
  have h1c : il1 ≠ ic := by intro h; have hv := congrArg Fin.val h; simp [il1, ic] at hv
  have h1h : il1 ≠ ih := by intro h; have hv := congrArg Fin.val h; simp [il1, ih] at hv
  have h1e : il1 ≠ ie := by intro h; have hv := congrArg Fin.val h; simp [il1, ie] at hv
  have hce : ic ≠ ie := by intro h; have hv := congrArg Fin.val h; simp [ic, ie] at hv
  have hci : ic ≠ ih := by intro h; have hv := congrArg Fin.val h; simp [ic, ih] at hv; omega
  have hhe : ih ≠ ie := by intro h; have hv := congrArg Fin.val h; simp [ih, ie] at hv
  have h01 : il0 ≠ il1 := by intro h; have hv := congrArg Fin.val h; simp [il0, il1] at hv
  have hxe : x ie = -v := by simp [x, ie, il0, il1]
  have hxc : x ic = 2 := by
    simp [x, ic, il0, il1, ie]
  have hxi : x ih = 2 := by
    simp [x, ih, il0, il1, ie]
  have hx : x ≠ 0 := by
    intro h
    have hh := congrFun h ic
    rw [hxc] at hh
    norm_num at hh
  have hsub := hpos.submatrix e.injective
  have hrow_leaf0 : (A.submatrix e e).mulVec x il0 = 0 := by
    change (∑ j : Fin (m + 4), A (e il0) (e j) * x j) = 0
    rw [fin_sum_support_three (fun j => A (e il0) (e j) * x j)
      il0 ic ih h0c h0h hci]
    · have hdiag : A (e il0) (e il0) = 2 := by rw [hA]; simp
      have hlink : A (e il0) (e ic) = -1 := by
        rw [hA]
        simp [il0, ic]
      have hzero : A (e il0) (e ih) = 0 := by
        rw [hA]
        simp [il0, ih, hm0]
      rw [hdiag, hlink, hzero]
      simp [x, il0, il1, ic, ih, ie, hce, hhe]
    · intro j hja hjc hjh
      rw [hA]
      have hj0 : j.val ≠ 0 := by
        intro hj; apply hja; apply Fin.ext; simpa [il0] using hj
      have hj2 : j.val ≠ 2 := by
        intro hj; apply hjc; apply Fin.ext; simpa [ic] using hj
      have hjm : j.val ≠ m + 2 := by
        intro hj; apply hjh; apply Fin.ext; simpa [ih] using hj
      by_cases hj1 : j = il1
      · subst j
        simp [x, il0, il1, ie, hm0]
      · have hj1v : j.val ≠ 1 := by
          intro hj; apply hj1; apply Fin.ext; simpa [il1] using hj
        have hj0' : il0 ≠ j := hja.symm
        have hj1' : il1 ≠ j := by intro h; exact hj1 h.symm
        have hil0Path : ¬(2 ≤ il0.val ∧ il0.val + 1 = j.val ∧ j.val ≤ m + 2) := by simp [il0]
        simp [x, hj0, hj1v, hj2, hjm, hj0', hil0Path]
  have hrow_leaf1 : (A.submatrix e e).mulVec x il1 = 0 := by
    change (∑ j : Fin (m + 4), A (e il1) (e j) * x j) = 0
    rw [fin_sum_support_three (fun j => A (e il1) (e j) * x j)
      il1 ic ih h1c h1h hci]
    · have hdiag : A (e il1) (e il1) = 2 := by rw [hA]; simp
      have hlink : A (e il1) (e ic) = -1 := by
        rw [hA]
        simp [il1, ic]
      have hzero : A (e il1) (e ih) = 0 := by
        rw [hA]
        simp [il1, ih, hm0]
      rw [hdiag, hlink, hzero]
      simp [x, il0, il1, ic, ih, ie, hce, hhe]
    · intro j hja hjc hjh
      rw [hA]
      have hj1 : j.val ≠ 1 := by
        intro hj; apply hja; apply Fin.ext; simpa [il1] using hj
      have hj2 : j.val ≠ 2 := by
        intro hj; apply hjc; apply Fin.ext; simpa [ic] using hj
      have hjm : j.val ≠ m + 2 := by
        intro hj; apply hjh; apply Fin.ext; simpa [ih] using hj
      by_cases hj0 : j = il0
      · subst j
        simp [x, il0, il1, ie, hm0]
      · have hj0v : j.val ≠ 0 := by
          intro hj; apply hj0; apply Fin.ext; simpa [il0] using hj
        have hj0' : il0 ≠ j := by intro h; exact hj0 h.symm
        have hj1' : il1 ≠ j := hja.symm
        have hil1Path : ¬(2 ≤ il1.val ∧ il1.val + 1 = j.val ∧ j.val ≤ m + 2) := by simp [il1]
        have hil1Back : ¬(2 ≤ j.val ∧ j.val + 1 = il1.val ∧ il1.val ≤ m + 2) := by
          intro h
          simp [il1] at h
          apply hj0
          apply Fin.ext
          simpa [il0] using h.2
        have hil1Heavy : il1.val ≠ m + 2 := by simp [il1]
        have hj0eq : j.val = 0 → j = il0 := by intro h; apply Fin.ext; simpa [il0] using h
        have hj0neq : 2 ≤ j.val → j.val ≠ 0 := by
          intro h2 h0
          omega
        simp [x, hj0v, hj1, hj2, hjm, hj1', hil1Path, hil1Back, hil1Heavy, hj0]
  have hrow_end : (A.submatrix e e).mulVec x ie = 0 := by
    change (∑ j : Fin (m + 4), A (e ie) (e j) * x j) = 0
    rw [fin_sum_support_two (fun j => A (e ie) (e j) * x j) ie ih
      hhe.symm (by
        intro j hji hjh
        rw [hA]
        have hjm : j.val ≠ m + 2 := by
          intro hj; apply hjh; apply Fin.ext; simpa [ih] using hj
        have hje : j.val ≠ m + 3 := by
          intro hj; apply hji; apply Fin.ext; simpa [ie] using hj
        have hie0 : ie.val ≠ 0 := by simp [ie]
        have hie1 : ie.val ≠ 1 := by simp [ie]
        have hie2 : ie.val ≠ 2 := by simp [ie]
        have hie' : ie ≠ j := hji.symm
        have hih' : ih ≠ j := hjh.symm
        have hieUpper : ¬ie.val ≤ m + 2 := by simp [ie]
        have hiePath : ¬(2 ≤ ie.val ∧ ie.val + 1 = j.val ∧ j.val ≤ m + 2) := by
          intro h
          simp [ie] at h
          omega
        have hieBack : ¬(2 ≤ j.val ∧ j.val + 1 = ie.val ∧ ie.val ≤ m + 2) := by
          intro h
          simp [ie] at h
        have hiePlus : ¬(ie.val + 1 = j.val ∧ j.val ≤ m + 2) := by omega
        have hieForward : ie.val + 1 = j.val → m + 2 < j.val := by omega
        simp [x, hjm, hje, hie0, hie1, hie2, hie', hieUpper, hiePlus])]
    · have hdiag : A (e ie) (e ie) = 2 := by rw [hA]; simp
      have hlink : A (e ie) (e ih) = v := by rw [hA]; simp [ie, ih]
      rw [hdiag, hlink]
      simp [x, il0, il1, ie, ih, hhe]
      ring
  have hrow_heavy : (A.submatrix e e).mulVec x ih = 2 - u * v := by
    let ip : Fin (m + 4) := ⟨m + 1, by omega⟩
    change (∑ j : Fin (m + 4), A (e ih) (e j) * x j) = _
    rw [fin_sum_support_three (fun j => A (e ih) (e j) * x j) ih ip ie
      (by simp [ih, ip])
      hhe
      (by simp [ip, ie])]
    · have hdiag : A (e ih) (e ih) = 2 := by rw [hA]; simp
      have hp : A (e ih) (e ip) = -1 := by
        rw [hA]
        simp [ih, ip]
      have he : A (e ih) (e ie) = u := by rw [hA]; simp [ih, ie, hm0]
      rw [hdiag, hp, he]
      have hip0 : ip ≠ il0 := by intro h; have hv := congrArg Fin.val h; simp [ip, il0] at hv
      have hip1 : ip ≠ il1 := by
        intro h
        have hv : m = 0 := by
          have hv' := congrArg Fin.val h
          simpa [ip, il1] using hv'
        exact hm0 hv
      have hipe : ip ≠ ie := by
        intro h
        have hv := congrArg Fin.val h
        dsimp [ip, ie] at hv
        omega
      have hxp : x ip = 2 := by simp [x, ip, il0, il1, ie, hipe, hm0]
      rw [hxi, hxp, hxe]
      ring
    · intro j hji hjp hje
      rw [hA]
      have hjm : j.val ≠ m + 2 := by
        intro hj; apply hji; apply Fin.ext; simpa [ih] using hj
      have hjp' : j.val ≠ m + 1 := by
        intro hj; apply hjp; apply Fin.ext; simpa [ip] using hj
      have hje' : j.val ≠ m + 3 := by
        intro hj; apply hje; apply Fin.ext; simpa [ie] using hj
      by_cases hj0 : j = il0
      · subst j; simp [x, ih, il0, il1, ie, hm0]
      · by_cases hj1 : j = il1
        · subst j; simp [x, ih, il0, il1, ie, hm0]
        · have hj0v : j.val ≠ 0 := by
            intro hj; apply hj0; apply Fin.ext; simpa [il0] using hj
          have hj1v : j.val ≠ 1 := by
            intro hj; apply hj1; apply Fin.ext; simpa [il1] using hj
          have hih' : ih ≠ j := hji.symm
          have hip' : ip ≠ j := hjp.symm
          have hie' : ie ≠ j := hje.symm
          have hihForward : ¬(2 ≤ ih.val ∧ ih.val + 1 = j.val ∧ j.val ≤ m + 2) := by
            intro h
            simp [ih] at h
            omega
          have hihBack : ¬(2 ≤ j.val ∧ j.val + 1 = ih.val ∧ ih.val ≤ m + 2) := by
            intro h
            simp [ih] at h
            omega
          have hih0 : ih.val ≠ 0 := by simp [ih]
          have hih1 : ih.val ≠ 1 := by simp [ih]
          have hihForward' : ih.val + 1 = j.val → m + 2 < j.val := by omega
          simp [x, hjm, hje', hj0v, hj1v, hih', hihForward, hihBack, hih0, hih1]
  have hrow_center : (A.submatrix e e).mulVec x ic = 0 := by
    let ip : Fin (m + 4) := ⟨3, by omega⟩
    change (∑ j : Fin (m + 4), A (e ic) (e j) * x j) = 0
    rw [fin_sum_support_four (fun j => A (e ic) (e j) * x j) il0 il1 ic ip
      h01 h0c (by simp [il0, ip]) h1c (by simp [il1, ip])
      (by simp [ic, ip])]
    · have hdiag : A (e ic) (e ic) = 2 := by rw [hA]; simp
      have h0 : A (e ic) (e il0) = -1 := by rw [hA]; simp [ic, il0]
      have h1 : A (e ic) (e il1) = -1 := by rw [hA]; simp [ic, il1]
      have hp : A (e ic) (e ip) = -1 := by rw [hA]; simp [ic, ip]; omega
      rw [hdiag, h0, h1, hp]
      have hxp : x ip = 2 := by simp [x, ip, il0, il1, ie, hm0]
      rw [hxc, hxp]
      simp [x, il0, il1, ie]
    · intro j hja hjb hjc hjd
      rw [hA]
      have hj0 : j.val ≠ 0 := by intro h; apply hja; apply Fin.ext; simpa [il0] using h
      have hj1 : j.val ≠ 1 := by intro h; apply hjb; apply Fin.ext; simpa [il1] using h
      have hj2 : j.val ≠ 2 := by intro h; apply hjc; apply Fin.ext; simpa [ic] using h
      have hj3 : j.val ≠ 3 := by intro h; apply hjd; apply Fin.ext; simpa [ip] using h
      have hjic : ic ≠ j := hjc.symm
      have hj3' : (3 : ℕ) ≠ j.val := hj3.symm
      have hjic' : (⟨2, by omega⟩ : Fin (m + 4)) ≠ j := hjic
      simp [ic, hj0, hj1, hj2, hj3', hjic, hm0]
  have hrow_path : ∀ i : Fin (m + 4), 3 ≤ i.val → i.val ≤ m + 1 →
      (A.submatrix e e).mulVec x i = 0 := by
    intro i hi3 him1
    let im1 : Fin (m + 4) := ⟨i.val - 1, by omega⟩
    let ip1 : Fin (m + 4) := ⟨i.val + 1, by omega⟩
    have him1i : im1 ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [im1] at hv
      omega
    have iip1 : i ≠ ip1 := by
      intro h
      have hv := congrArg Fin.val h
      simp [ip1] at hv
    have him1ip1 : im1 ≠ ip1 := by
      intro h
      have hv := congrArg Fin.val h
      simp [im1, ip1] at hv
    change (∑ j : Fin (m + 4), A (e i) (e j) * x j) = 0
    rw [fin_sum_support_three (fun j => A (e i) (e j) * x j) i im1 ip1
      (Ne.symm him1i) iip1 him1ip1]
    · have hdiag : A (e i) (e i) = 2 := by rw [hA]; simp
      have hleft : A (e i) (e im1) = -1 := by
        rw [hA]
        simp [im1]
        omega
      have hright : A (e i) (e ip1) = -1 := by
        rw [hA]
        simp [ip1]
        omega
      rw [hdiag, hleft, hright]
      have hi0 : i.val ≠ 0 := by omega
      have hi1 : i.val ≠ 1 := by omega
      have hie : i.val ≠ m + 3 := by omega
      have hih : i.val ≠ m + 2 := by omega
      have him10 : i.val - 1 ≠ 0 := by omega
      have him1ie : i.val - 1 ≠ m + 4 := by omega
      have hip10 : i.val + 1 ≠ 0 := by omega
      have hi2 : i.val ≠ 2 := by omega
      have hi0Fin : i ≠ il0 := by intro h; apply hi0; simpa [il0] using congrArg Fin.val h
      have hi1Fin : i ≠ il1 := by intro h; apply hi1; simpa [il1] using congrArg Fin.val h
      have hieFin : i ≠ ie := by intro h; apply hie; simpa [ie] using congrArg Fin.val h
      have hihFin : i ≠ ih := by intro h; apply hih; simpa [ih] using congrArg Fin.val h
      have hiZero : i ≠ (0 : Fin (m + 4)) := by simpa [il0] using hi0Fin
      have hiOne : i ≠ (1 : Fin (m + 4)) := by simpa [il1] using hi1Fin
      have him4 : i.val ≠ m + 4 := by omega
      have hxim1 : x im1 = 2 := by
        simp [x, im1, il0, il1, ie, him10, hi2, him4]
      have hxip1 : x ip1 = 2 := by
        simp [x, ip1, il0, il1, ie, hiZero, hih]
      have hxi : x i = 2 := by simp [x, hi0Fin, hi1Fin, hieFin]
      rw [hxim1, hxip1, hxi]
      ring
    · intro j hji hjm1 hjp1
      rw [hA]
      have hji' : i ≠ j := hji.symm
      have hfor : i.val + 1 ≠ j.val := by
        intro h
        apply hjp1
        apply Fin.ext
        exact h.symm
      have hback : j.val + 1 ≠ i.val := by
        intro h
        apply hjm1
        apply Fin.ext
        simp [im1]
        omega
      have hi2 : i.val ≠ 2 := by omega
      have hiHeavy : i.val ≠ m + 2 := by omega
      have hiHeavy3 : i.val ≠ m + 3 := by omega
      have hi0 : i.val ≠ 0 := by omega
      have hi1 : i.val ≠ 1 := by omega
      simp [hji', hfor, hback, hi0, hi1, hi2, hiHeavy, hiHeavy3]
  let B : Matrix (Fin (m + 4)) (Fin (m + 4)) ℤ :=
    Matrix.diagonal (d ∘ e) * A.submatrix e e
  have hBpos : B.PosDef := by
    exact diagonal_mul_submatrix_posDef A d e hpos
  have hBmul_zero (i : Fin (m + 4)) (hi : i ≠ ih) : B.mulVec x i = 0 := by
    rw [show B = Matrix.diagonal (d ∘ e) * A.submatrix e e by rfl]
    rw [← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_diagonal]
    have hrow : (A.submatrix e e).mulVec x i = 0 := by
      by_cases hi0 : i = il0
      · simpa [hi0] using hrow_leaf0
      · by_cases hi1 : i = il1
        · simpa [hi1] using hrow_leaf1
        · by_cases hie : i = ie
          · simpa [hie] using hrow_end
          · by_cases hic : i = ic
            · simpa [hic] using hrow_center
            · by_cases hih : i = ih
              · exact False.elim (hi hih)
              · have hi3 : 3 ≤ i.val := by
                  have hi0v : i.val ≠ 0 := by
                    intro h
                    apply hi0
                    apply Fin.ext
                    simpa [il0] using h
                  have hi1v : i.val ≠ 1 := by
                    intro h
                    apply hi1
                    apply Fin.ext
                    simpa [il1] using h
                  have hi2 : i.val ≠ 2 := by
                    intro h
                    apply hic
                    apply Fin.ext
                    simpa [ic] using h
                  omega
                have him1 : i.val ≤ m + 1 := by
                  have hie' : i.val ≠ m + 3 := by
                    intro h
                    apply hie
                    apply Fin.ext
                    simpa [ie] using h
                  have hih' : i.val ≠ m + 2 := by
                    intro h
                    apply hi
                    apply Fin.ext
                    simpa [ih] using h
                  omega
                exact hrow_path i hi3 him1
    rw [hrow]
    simp
  have hBmul_heavy : B.mulVec x ih = d (e ih) * (2 - u * v) := by
    rw [show B = Matrix.diagonal (d ∘ e) * A.submatrix e e by rfl]
    rw [← Matrix.mulVec_mulVec]
    rw [Matrix.mulVec_diagonal]
    rw [hrow_heavy]
    rfl
  have hquad := hBpos.dotProduct_mulVec_pos hx
  have hquad_eq : star x ⬝ᵥ B.mulVec x = star (x ih) * (B.mulVec x ih) := by
    change (∑ i, star (x i) * B.mulVec x i) = _
    rw [Fintype.sum_eq_single ih (by
      intro i hne
      rw [hBmul_zero i hne]
      simp)]
  have hdih : 0 < d (e ih) := by
    have h := hpos.diag_pos (i := e ih)
    have hdiag : A (e ih) (e ih) = 2 := by rw [hA]; simp
    simp [Matrix.diagonal_mul, hdiag] at h
    omega
  rw [hquad_eq, hBmul_heavy, hxi] at hquad
  change 0 < 2 * (d (e ih) * (2 - u * v)) at hquad
  have hfactor : 2 - u * v ≤ 0 := by omega
  have hprod : d (e ih) * (2 - u * v) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hdih) hfactor
  have hnonpos : 2 * (d (e ih) * (2 - u * v)) ≤ 0 := by
    exact mul_nonpos_of_nonneg_of_nonpos (by norm_num) hprod
  exact (not_lt_of_ge hnonpos) hquad

public lemma not_cartan_path_two_heavy_edges_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hpos : (Matrix.diagonal d * A).PosDef)
    {n p q : ℕ} (e : Fin n ↪ κ) (u v s t : ℤ)
    (hp : p + 1 < n) (hq : q + 1 < n) (hpq : p + 1 < q)
    (hA : ∀ i j : Fin n, A (e i) (e j) =
      if i = j then 2 else if i.val + 1 = j.val then
        if i.val = p then u else if i.val = q then s else -1
      else if j.val + 1 = i.val then
        if j.val = p then v else if j.val = q then t else -1
      else 0)
    (huv : 2 ≤ u * v) (hst : 2 ≤ s * t) : False := by
  let ep : Fin n := ⟨p, by omega⟩
  let ep1 : Fin n := ⟨p + 1, hp⟩
  let eq : Fin n := ⟨q, by omega⟩
  let eq1 : Fin n := ⟨q + 1, hq⟩
  let x : Fin n → ℤ := fun i =>
    if i = ep then s else if i = eq1 then v else
      if p < i.val ∧ i.val ≤ q then -v * s else 0
  have hepeq : ep ≠ eq1 := by
    intro h
    have := congrArg Fin.val h
    simp [ep, eq1] at this
    omega
  have hx : x ≠ 0 := by
    intro h
    have h0 := congrFun h ep
    have hs0 : s ≠ 0 := by
      intro hs0
      subst s
      omega
    simp [x, ep, eq1, hs0] at h0
  have hsub := hpos.submatrix e.injective
  have hquad := hsub.dotProduct_mulVec_pos hx
  have hrow_ep : (A.submatrix e e).mulVec x ep = 2 * s + u * (-v * s) := by
    change (∑ j : Fin n, A (e ep) (e j) * x j) = _
    rw [fin_sum_support_two (fun j => A (e ep) (e j) * x j) ep ep1 (by
        intro h
        have hv := congrArg Fin.val h
        simp [ep, ep1] at hv
        ) (by
      intro j hja hjb
      have hja' : ep ≠ j := by exact fun h => hja h.symm
      have hjb' : ep1 ≠ j := by exact fun h => hjb h.symm
      by_cases hsegj : p < j.val ∧ j.val ≤ q
      · have hfor : p + 1 ≠ j.val := by
          intro hv
          apply hjb
          apply Fin.ext
          simp [ep1]
          exact hv.symm
        have hback : ¬j.val + 1 = p := by omega
        rw [hA]
        simp [ep, hja', hfor, hback]
      · by_cases hjeq1 : j = eq1
        · have hz : A (e ep) (e eq1) = 0 := by
            rw [hA]
            simp [ep, eq1]
            omega
          simp [hjeq1, hz]
        · simp [x, hsegj, hja, hjeq1])]
    have hdiag : A (e ep) (e ep) = 2 := by
      rw [hA]
      simp [ep]
    have hforward : A (e ep) (e ep1) = u := by
      rw [hA]
      simp [ep, ep1]
    have hseg : p < p + 1 ∧ p + 1 ≤ q := by omega
    have hpq' : p < q := by omega
    have hpqne : p ≠ q := by omega
    simp [hdiag, hforward, x, ep, ep1, eq1, hseg, hpqne]

  have hrow_mid : ∀ i : Fin n, p < i.val → i.val ≤ q →
      (A.submatrix e e).mulVec x i = 0 := by
    intro i hi hiq
    have hie : i ≠ ep := by
      intro h
      have hv := congrArg Fin.val h
      simp [ep] at hv
      omega
    have hieq1 : i ≠ eq1 := by
      intro h
      have hv := congrArg Fin.val h
      simp [eq1] at hv
      omega
    let im1 : Fin n := ⟨i.val - 1, by omega⟩
    let ip1 : Fin n := ⟨i.val + 1, by omega⟩
    have him1 : im1 ≠ i := by
      intro h
      have hv := congrArg Fin.val h
      simp [im1] at hv
      omega
    have hiip1 : i ≠ ip1 := by
      intro h
      have hv := congrArg Fin.val h
      simp [ip1] at hv
    have him1ip1 : im1 ≠ ip1 := by
      intro h
      have hv := congrArg Fin.val h
      simp [im1, ip1] at hv
    change (∑ j : Fin n, A (e i) (e j) * x j) = 0
    rw [fin_sum_support_three (fun j => A (e i) (e j) * x j) i im1 ip1
      (Ne.symm him1) (by
        intro h
        have hv := congrArg Fin.val h
        simp [ip1] at hv
        ) him1ip1 (by
      intro j hji hjm1 hjp1
      have hji' : i ≠ j := by exact fun h => hji h.symm
      by_cases hsegj : p < j.val ∧ j.val ≤ q
      · have hfor : i.val + 1 ≠ j.val := by
          intro hv
          apply hjp1
          apply Fin.ext
          exact hv.symm
        have hback : j.val + 1 ≠ i.val := by
          intro hv
          apply hjm1
          apply Fin.ext
          simp [im1]
          omega
        rw [hA]
        simp [hji', hfor, hback]
      · by_cases hjp : j = ep
        · rw [hA]
          have hfor : ¬(i.val + 1 = p) := by omega
          have hback : p + 1 ≠ i.val := by
            intro hv
            apply hjm1
            apply Fin.ext
            have hjval := congrArg Fin.val hjp
            simp [im1, ep] at hjval ⊢
            omega
          have hie : i ≠ ep := by
            intro h
            have hv := congrArg Fin.val h
            simp [ep] at hv
            omega
          simp [ep, hjp, hie, hfor, hback]
        · by_cases hjq : j = eq1
          · rw [hA]
            by_cases hiq' : i.val = q
            · exfalso
              apply hjp1
              apply Fin.ext
              subst j
              simp [ip1, eq1, hiq']
            · have hfor : i.val + 1 ≠ q + 1 := by
                intro h
                apply hiq'
                omega
              have hjval := congrArg Fin.val hjq
              have hback : q + 1 + 1 ≠ i.val := by omega
              simp [eq1, hjq, hieq1, hback, hiq']
          · simp [x, hsegj, hjp, hjq])]
    by_cases hip1 : i.val = p + 1
    · have hiqne : i.val ≠ q := by omega
      have him1eq : im1 = ep := by
        apply Fin.ext
        simp [im1, ep, hip1]
      have hxi : x i = -v * s := by
        simp [x, ep, eq1, hi, hiq, hie, hieq1]
      have hxim1 : x im1 = s := by simp [x, him1eq, ep]
      have hxip1 : x ip1 = -v * s := by
        have hip1seg : p < ip1.val ∧ ip1.val ≤ q := by
          simp [ip1, hip1]
          omega
        have hip1nep : ip1 ≠ ep := by
          intro h
          have hv := congrArg Fin.val h
          simp [ip1, ep, hip1] at hv
          omega
        have hip1neq1 : ip1 ≠ eq1 := by
          intro h
          have hv := congrArg Fin.val h
          simp [ip1, eq1, hip1] at hv
          omega
        simp [x, ep, eq1, hip1seg, hip1nep, hip1neq1]
      have haii : A (e i) (e i) = 2 := by rw [hA]; simp
      have hp1qne : p + 1 ≠ q := by omega
      have haim1 : A (e i) (e im1) = v := by
        rw [hA]
        have hne : i ≠ im1 := Ne.symm him1
        have hfor : i.val + 1 ≠ im1.val := by simp [im1]; omega
        have hback : im1.val + 1 = i.val := by simp [im1]; omega
        have him1p : im1.val = p := by simp [im1, hip1]
        rw [if_neg hne, if_neg hfor, if_pos hback, if_pos him1p]
      have haip1 : A (e i) (e ip1) = -1 := by
        rw [hA]
        have hfor : i.val + 1 = ip1.val := by simp [ip1]
        have hip : i.val ≠ p := by omega
        rw [if_neg hiip1, if_pos hfor, if_neg hip, if_neg hiqne]
      rw [haii, haim1, haip1, hxi, hxim1, hxip1]
      ring
    · by_cases hiq' : i.val = q
      · have him1seg : p < im1.val ∧ im1.val ≤ q := by
          simp [im1]
          omega
        have him1nep : im1 ≠ ep := by
          intro h
          have hv := congrArg Fin.val h
          simp [im1, ep] at hv
          omega
        have him1eq1 : im1 ≠ eq1 := by
          intro h
          have hv := congrArg Fin.val h
          simp [im1, eq1] at hv
          omega
        have hxi : x i = -v * s := by simp [x, ep, eq1, hi, hiq, hie, hieq1]
        have hxim1 : x im1 = -v * s := by simp [x, ep, eq1, him1seg, him1nep, him1eq1]
        have hxip1 : x ip1 = v := by
          have hipeq : ip1 = eq1 := by
            apply Fin.ext
            simp [ip1, eq1, hiq']
          have hq1p : q + 1 ≠ p := by omega
          simp [x, hipeq, eq1, ep, hq1p]
        have haii : A (e i) (e i) = 2 := by rw [hA]; simp
        have haim1 : A (e i) (e im1) = -1 := by
          rw [hA]
          have hqm1p : q - 1 ≠ p := by omega
          have hqm1q : q - 1 ≠ q := by omega
          have hne : i ≠ im1 := Ne.symm him1
          have hfor : i.val + 1 ≠ im1.val := by simp [im1]; omega
          have hback : im1.val + 1 = i.val := by simp [im1]; omega
          have him1p : im1.val ≠ p := by simp [im1]; omega
          have him1q : im1.val ≠ q := by simp [im1]; omega
          rw [if_neg hne, if_neg hfor, if_pos hback,
            if_neg him1p, if_neg him1q]
        have haip1 : A (e i) (e ip1) = s := by
          rw [hA]
          have hfor : i.val + 1 = ip1.val := by simp [ip1]
          have hqnp : q ≠ p := by omega
          have hip : i.val ≠ p := by omega
          rw [if_neg hiip1, if_pos hfor, if_neg hip, if_pos hiq']
        rw [haii, haim1, haip1, hxi, hxim1, hxip1]
        ring
      · have him1seg : p < im1.val ∧ im1.val ≤ q := by
          simp [im1]
          omega
        have him1nep : im1 ≠ ep := by
          intro h
          have hv := congrArg Fin.val h
          simp [im1, ep] at hv
          omega
        have him1eq1 : im1 ≠ eq1 := by
          intro h
          have hv := congrArg Fin.val h
          simp [im1, eq1] at hv
          omega
        have hiseg : p < i.val ∧ i.val ≤ q := ⟨hi, hiq⟩
        have hxi : x i = -v * s := by simp [x, ep, eq1, hiseg, hie, hieq1]
        have hxim1 : x im1 = -v * s := by simp [x, ep, eq1, him1seg, him1nep, him1eq1]
        have hip1seg : p < ip1.val ∧ ip1.val ≤ q := by
          simp [ip1]
          omega
        have hip1nep : ip1 ≠ ep := by
          intro h
          have hv := congrArg Fin.val h
          simp [ip1, ep] at hv
          omega
        have hip1eq1 : ip1 ≠ eq1 := by
          intro h
          have hv := congrArg Fin.val h
          simp [ip1, eq1] at hv
          omega
        have hxip1 : x ip1 = -v * s := by simp [x, ep, eq1, hip1seg, hip1nep, hip1eq1]
        have haii : A (e i) (e i) = 2 := by rw [hA]; simp
        have haim1 : A (e i) (e im1) = -1 := by
          rw [hA]
          simp [im1]
          omega
        have haip1 : A (e i) (e ip1) = -1 := by
          rw [hA]
          simp [ip1]
          omega
        rw [haii, haim1, haip1, hxi, hxim1, hxip1]
        ring
  have hrow_eq1 : (A.submatrix e e).mulVec x eq1 = 2 * v + t * (-v * s) := by
    change (∑ j : Fin n, A (e eq1) (e j) * x j) = _
    rw [fin_sum_support_two (fun j => A (e eq1) (e j) * x j) eq1 eq (by
        intro h
        have hv := congrArg Fin.val h
        simp [eq1, eq] at hv) (by
      intro j hja hjb
      have hja' : eq1 ≠ j := by exact fun h => hja h.symm
      have hjb' : eq ≠ j := by exact fun h => hjb h.symm
      by_cases hsegj : p < j.val ∧ j.val ≤ q
      · have hfor : q + 1 ≠ j.val := by
          intro hv
          apply hja
          apply Fin.ext
          simp [eq1]
          exact hv.symm
        have hforward : eq1.val + 1 ≠ j.val := by simp [eq1]; omega
        have hback : j.val + 1 ≠ eq1.val := by
          intro hv
          apply hjb
          apply Fin.ext
          have hv' : j.val + 1 = q + 1 := by simpa [eq1] using hv
          simpa [eq] using Nat.add_right_cancel hv'
        rw [hA]
        simp [hja', hforward, hback]
      · by_cases hjeq : j = eq
        · exact (hjb hjeq).elim
        · by_cases hjep : j = ep
          · subst j
            have hz : A (e eq1) (e ep) = 0 := by
              rw [hA]
              simp [eq1, ep]
              omega
            simp [hz]
          · simp [x, hsegj, hja, hjep])]
    have hdiag : A (e eq1) (e eq1) = 2 := by
      rw [hA]
      simp [eq1]
    have hreverse : A (e eq1) (e eq) = t := by
      rw [hA]
      have hqp : q ≠ p := by omega
      have hne : eq1 ≠ eq := by
        intro h
        have hv := congrArg Fin.val h
        simp [eq1, eq] at hv
      have hfor : eq1.val + 1 ≠ eq.val := by simp [eq1, eq]; omega
      have hback : eq.val + 1 = eq1.val := by simp [eq1, eq]
      rw [if_neg hne, if_neg hfor, if_pos hback, if_neg hqp, if_pos rfl]
    have hqp : q ≠ p := by omega
    have hpq' : p < q := by omega
    have hq1p : q + 1 ≠ p := by omega
    simp [hdiag, hreverse, x, ep, eq1, eq, hqp, hpq', hq1p]

  have hrow_scaled : ∀ i : Fin n,
      ((Matrix.diagonal d * A).submatrix e e).mulVec x i =
        d (e i) * (A.submatrix e e).mulVec x i := by
    intro i
    simp [Matrix.mulVec, Matrix.submatrix, Matrix.diagonal_mul, dotProduct,
      Finset.mul_sum, mul_assoc]
  have hdot : star x ⬝ᵥ
      ((Matrix.diagonal d * A).submatrix e e).mulVec x =
        x ep * (d (e ep) * (A.submatrix e e).mulVec x ep) +
        x eq1 * (d (e eq1) * (A.submatrix e e).mulVec x eq1) := by
    change (∑ i, x i *
      ((Matrix.diagonal d * A).submatrix e e).mulVec x i) = _
    rw [fin_sum_support_two
      (fun i => x i *
        ((Matrix.diagonal d * A).submatrix e e).mulVec x i)
      ep eq1 hepeq]
    · simp [hrow_scaled]
    · intro i hie hieq
      by_cases hi : p < i.val ∧ i.val ≤ q
      · rw [hrow_scaled, hrow_mid i hi.1 hi.2]
        simp
      · simp [x, hie, hieq, hi]
  rw [hdot, hrow_ep, hrow_eq1] at hquad
  have hxep : x ep = s := by simp [x]
  have hxeq1 : x eq1 = v := by simp [x, Ne.symm hepeq]
  rw [hxep, hxeq1] at hquad
  have hdep : 0 < d (e ep) := by
    have h := hpos.diag_pos (i := e ep)
    have hdiag : A (e ep) (e ep) = 2 := by simpa using hA ep ep
    simp [Matrix.diagonal_mul, hdiag] at h
    omega
  have hdeq1 : 0 < d (e eq1) := by
    have h := hpos.diag_pos (i := e eq1)
    have hdiag : A (e eq1) (e eq1) = 2 := by simpa using hA eq1 eq1
    simp [Matrix.diagonal_mul, hdiag] at h
    omega
  have hs2 : 0 ≤ s ^ 2 := sq_nonneg s
  have hv2 : 0 ≤ v ^ 2 := sq_nonneg v
  have hq1 : 2 - u * v ≤ 0 := by omega
  have hq2 : 2 - s * t ≤ 0 := by omega
  have ht1 : d (e ep) * s ^ 2 * (2 - u * v) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (le_of_lt hdep) hs2) hq1
  have ht2 : d (e eq1) * v ^ 2 * (2 - s * t) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (le_of_lt hdeq1) hv2) hq2
  nlinarith

/-- Symmetric affine-fork exclusions classify an arbitrary positive triple of
arm lengths, without first choosing a sorting permutation. -/
public lemma nat_three_arm_lengths_permutation_of_affine_forbidden
    (a b c : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hE6 : ¬ (2 ≤ a ∧ 2 ≤ b ∧ 2 ≤ c))
    (hE7 : ¬ ((3 ≤ a ∧ 3 ≤ b) ∨ (3 ≤ a ∧ 3 ≤ c) ∨
      (3 ≤ b ∧ 3 ≤ c)))
    (hE8 : ¬ ((5 ≤ a ∧ 2 ≤ b) ∨ (5 ≤ a ∧ 2 ≤ c) ∨
      (5 ≤ b ∧ 2 ≤ a) ∨ (5 ≤ b ∧ 2 ≤ c) ∨
      (5 ≤ c ∧ 2 ≤ a) ∨ (5 ≤ c ∧ 2 ≤ b))) :
    2 ≤ (a ::ₘ b ::ₘ c ::ₘ 0).count 1 ∨
    (a ::ₘ b ::ₘ c ::ₘ 0) = (1 ::ₘ 2 ::ₘ 2 ::ₘ 0) ∨
    (a ::ₘ b ::ₘ c ::ₘ 0) = (1 ::ₘ 2 ::ₘ 3 ::ₘ 0) ∨
    (a ::ₘ b ::ₘ c ::ₘ 0) = (1 ::ₘ 2 ::ₘ 4 ::ₘ 0) := by
  have finish : ∀ x y z : ℕ,
      (a ::ₘ b ::ₘ c ::ₘ 0) = (x ::ₘ y ::ₘ z ::ₘ 0) →
      ((x = 1 ∧ y = 1) ∨
        (x = 1 ∧ y = 2 ∧ z = 2) ∨
        (x = 1 ∧ y = 2 ∧ z = 3) ∨
        (x = 1 ∧ y = 2 ∧ z = 4)) →
      2 ≤ (a ::ₘ b ::ₘ c ::ₘ 0).count 1 ∨
      (a ::ₘ b ::ₘ c ::ₘ 0) = (1 ::ₘ 2 ::ₘ 2 ::ₘ 0) ∨
      (a ::ₘ b ::ₘ c ::ₘ 0) = (1 ::ₘ 2 ::ₘ 3 ::ₘ 0) ∨
      (a ::ₘ b ::ₘ c ::ₘ 0) = (1 ::ₘ 2 ::ₘ 4 ::ₘ 0) := by
    intro x y z hperm hs
    rcases hs with hD | hE6' | hE7' | hE8'
    · left
      rw [hperm]
      rcases hD with ⟨rfl, rfl⟩
      simp
    · right; left
      rw [hperm]
      rcases hE6' with ⟨rfl, rfl, rfl⟩
      rfl
    · right; right; left
      rw [hperm]
      rcases hE7' with ⟨rfl, rfl, rfl⟩
      rfl
    · right; right; right
      rw [hperm]
      rcases hE8' with ⟨rfl, rfl, rfl⟩
      rfl
  rcases le_total a b with hab | hba
  · rcases le_total b c with hbc | hcb
    · exact finish a b c rfl (nat_three_arm_lengths_of_affine_forbidden
        a b c ha hab hbc (by omega) (by omega) (by omega))
    · rcases le_total a c with hac | hca
      · apply finish a c b
        · ext n
          simp only [Multiset.count_cons, Multiset.count_zero]
          omega
        · exact nat_three_arm_lengths_of_affine_forbidden
            a c b ha hac hcb (by omega) (by omega) (by omega)
      · apply finish c a b
        · ext n
          simp only [Multiset.count_cons, Multiset.count_zero]
          omega
        · exact nat_three_arm_lengths_of_affine_forbidden
            c a b hc hca hab (by omega) (by omega) (by omega)
  · rcases le_total a c with hac | hca
    · apply finish b a c
      · ext n
        simp only [Multiset.count_cons, Multiset.count_zero]
        omega
      · exact nat_three_arm_lengths_of_affine_forbidden
          b a c hb hba hac (by omega) (by omega) (by omega)
    · rcases le_total b c with hbc | hcb
      · apply finish b c a
        · ext n
          simp only [Multiset.count_cons, Multiset.count_zero]
          omega
        · exact nat_three_arm_lengths_of_affine_forbidden
            b c a hb hbc hca (by omega) (by omega) (by omega)
      · apply finish c b a
        · ext n
          simp only [Multiset.count_cons, Multiset.count_zero]
          omega
        · exact nat_three_arm_lengths_of_affine_forbidden
            c b a hc hcb hba (by omega) (by omega) (by omega)

/-- Exact affine-`E₆` Cartan support with simple directed bond entries
contradicts positive definiteness.  The support and entries are explicit
ordinary hypotheses. -/
public lemma not_cartan_affineE6_of_support_numbering
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (e : Fin 7 ↪ κ)
    (hsupport : ∀ i j : Fin 7,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (e i) (e j) ↔
        ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
         (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
         (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
         (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
         (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
         (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5)))
    (hbond : ∀ i j : Fin 7,
      ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
       (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
       (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
       (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
       (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
       (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5)) →
      A (e i) (e j) = -1) : False := by
  have hA : ∀ i j, A (e i) (e j) =
      if i = j then 2 else if
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
        (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
        (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
        (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
        (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5)
      then -1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact hdiag _
    by_cases hedge :
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
        (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
        (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
        (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
        (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5)
    · rw [if_neg hij, if_pos hedge]
      exact hbond i j hedge
    · have hzero : A (e i) (e j) = 0 := by
        by_contra hne
        have hadj : (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
            (e i) (e j) := by
          rw [SimpleGraph.fromRel_adj]
          exact ⟨e.injective.ne hij, Or.inl hne⟩
        exact hedge ((hsupport i j).mp hadj)
      rw [if_neg hij, if_neg hedge]
      exact hzero
  exact not_cartan_affineE6_of_diagonal_mul_posDef A d hpos e hA

/-- Exact affine-`E₇` Cartan support with simple directed bond entries
contradicts positive definiteness. -/
public lemma not_cartan_affineE7_of_support_numbering
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (e : Fin 8 ↪ κ)
    (hsupport : ∀ i j : Fin 8,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (e i) (e j) ↔
        ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
         (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
         (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
         (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
         (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
         (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
         (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6)))
    (hbond : ∀ i j : Fin 8,
      ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
       (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
       (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
       (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
       (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
       (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
       (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6)) →
      A (e i) (e j) = -1) : False := by
  have hA : ∀ i j, A (e i) (e j) =
      if i = j then 2 else if
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
        (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
        (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
        (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
        (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
        (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6)
      then -1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact hdiag _
    by_cases hedge :
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
        (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
        (i = 3 ∧ j = 4) ∨ (i = 4 ∧ j = 3) ∨
        (i = 0 ∧ j = 5) ∨ (i = 5 ∧ j = 0) ∨
        (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
        (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6)
    · rw [if_neg hij, if_pos hedge]
      exact hbond i j hedge
    · have hzero : A (e i) (e j) = 0 := by
        by_contra hne
        have hadj : (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
            (e i) (e j) := by
          rw [SimpleGraph.fromRel_adj]
          exact ⟨e.injective.ne hij, Or.inl hne⟩
        exact hedge ((hsupport i j).mp hadj)
      rw [if_neg hij, if_neg hedge]
      exact hzero
  exact not_cartan_affineE7_of_diagonal_mul_posDef A d hpos e hA

/-- Exact affine-`E₈` Cartan support with simple directed bond entries
contradicts positive definiteness. -/
public lemma not_cartan_affineE8_of_support_numbering
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hpos : (Matrix.diagonal d * A).PosDef)
    (e : Fin 9 ↪ κ)
    (hsupport : ∀ i j : Fin 9,
      (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj (e i) (e j) ↔
        ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
         (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
         (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
         (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
         (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨
         (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
         (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6) ∨
         (i = 7 ∧ j = 8) ∨ (i = 8 ∧ j = 7)))
    (hbond : ∀ i j : Fin 9,
      ((i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
       (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
       (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
       (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
       (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨
       (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
       (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6) ∨
       (i = 7 ∧ j = 8) ∨ (i = 8 ∧ j = 7)) →
      A (e i) (e j) = -1) : False := by
  have hA : ∀ i j, A (e i) (e j) =
      if i = j then 2 else if
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
        (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
        (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
        (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨
        (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
        (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6) ∨
        (i = 7 ∧ j = 8) ∨ (i = 8 ∧ j = 7)
      then -1 else 0 := by
    intro i j
    by_cases hij : i = j
    · subst j
      rw [if_pos rfl]
      exact hdiag _
    by_cases hedge :
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
        (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨
        (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) ∨
        (i = 0 ∧ j = 4) ∨ (i = 4 ∧ j = 0) ∨
        (i = 4 ∧ j = 5) ∨ (i = 5 ∧ j = 4) ∨
        (i = 5 ∧ j = 6) ∨ (i = 6 ∧ j = 5) ∨
        (i = 6 ∧ j = 7) ∨ (i = 7 ∧ j = 6) ∨
        (i = 7 ∧ j = 8) ∨ (i = 8 ∧ j = 7)
    · rw [if_neg hij, if_pos hedge]
      exact hbond i j hedge
    · have hzero : A (e i) (e j) = 0 := by
        by_contra hne
        have hadj : (SimpleGraph.fromRel fun x y => A x y ≠ 0).Adj
            (e i) (e j) := by
          rw [SimpleGraph.fromRel_adj]
          exact ⟨e.injective.ne hij, Or.inl hne⟩
        exact hedge ((hsupport i j).mp hadj)
      rw [if_neg hij, if_neg hedge]
      exact hzero
  exact not_cartan_affineE8_of_diagonal_mul_posDef A d hpos e hA

/-- At a Cartan support vertex with two distinct neighbors, the sum of the two
opposite-entry bond products is at most three. -/
public lemma cartan_twoNeighbor_edgeProducts_sum_le_three
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c a b : κ) (hca : c ≠ a) (hcb : c ≠ b) (hab : a ≠ b)
    (hnea : A c a ≠ 0) (hneb : A c b ≠ 0) :
    A c a * A a c + A c b * A b c ≤ 3 := by
  classical
  have hcaBounds := cartan_rankTwo_nonzero_bounds A hrank hca hnea
  have hcbBounds := cartan_rankTwo_nonzero_bounds A hrank hcb hneb
  by_cases hnab : A a b = 0
  · have hz : A a b = 0 ∧ A b a = 0 := by
      rcases hrank a b hab with h0 | h11 | h12 | h21 | h13 | h31
      · exact h0
      all_goals omega
    by_contra hsum
    have hfour : 4 ≤ A c a * A a c + A c b * A b c := by omega
    apply not_cartan_twoStar_of_diagonal_mul_posDef A d hdiag hpos c a b
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · exact hz.1
    · exact hz.2
    · exact hfour
  · have habBounds := cartan_rankTwo_nonzero_bounds A hrank hab hnab
    let e : Fin 3 → κ := ![c, a, b]
    have he : Function.Injective e := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [e]
    exfalso
    apply not_cartan_weightedTriangle_of_diagonal_mul_posDef A d hpos ⟨e, he⟩
    · intro i
      exact hdiag _
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [e]

/-- Under the six finite rank-two Cartan patterns, positive diagonal
symmetrizability prevents a vertex from having four distinct nonzero
neighbors. -/
public lemma not_cartan_fourNeighbors_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c : κ) (l : Fin 4 ↪ κ) (hc : ∀ a, c ≠ l a)
    (hne : ∀ a, A c (l a) ≠ 0) : False := by
  classical
  have hlc : ∀ a, l a ≠ c := fun a => (hc a).symm
  by_cases hleaf : ∀ ⦃a b : Fin 4⦄, a ≠ b → A (l a) (l b) = 0
  · apply not_cartan_fourStar_of_diagonal_mul_posDef A d hdiag hpos c l
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    · exact hleaf
    · intro a
      exact (cartan_rankTwo_nonzero_bounds A hrank (hc a) (hne a)).2.2
  · push Not at hleaf
    obtain ⟨a, b, hab, habne⟩ := hleaf
    have hlab : l a ≠ l b := fun h => hab (l.injective h)
    have hca := cartan_rankTwo_nonzero_bounds A hrank (hc a) (hne a)
    have hcb := cartan_rankTwo_nonzero_bounds A hrank (hc b) (hne b)
    have hlabBounds := cartan_rankTwo_nonzero_bounds A hrank hlab habne
    let e : Fin 3 → κ := ![c, l a, l b]
    have he : Function.Injective e := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (hc a (by simpa [e] using hij))
      · exact False.elim (hc b (by simpa [e] using hij))
      · exact False.elim (hc a |>.symm (by simpa [e] using hij))
      · rfl
      · exact False.elim (hab (l.injective (by simpa [e] using hij)))
      · exact False.elim (hc b |>.symm (by simpa [e] using hij))
      · exact False.elim (hab.symm (l.injective (by simpa [e] using hij)))
      · rfl
    apply not_cartan_weightedTriangle_of_diagonal_mul_posDef A d hpos ⟨e, he⟩
    · intro i
      exact hdiag _
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [e]

/-- Two heavy bonds cannot meet at one vertex in a finite positive-definite
Cartan matrix.  If the other endpoints are joined, the weighted triangle
obstruction applies; otherwise the two-star determinant obstruction applies. -/
public lemma not_cartan_two_heavy_edges_of_diagonal_mul_posDef
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix κ κ ℤ) (d : κ → ℤ)
    (hdiag : ∀ i, A i i = 2)
    (hrank : ∀ i j, i ≠ j →
      (A i j = 0 ∧ A j i = 0) ∨
      (A i j = -1 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -2) ∨
      (A i j = -2 ∧ A j i = -1) ∨
      (A i j = -1 ∧ A j i = -3) ∨
      (A i j = -3 ∧ A j i = -1))
    (hpos : (Matrix.diagonal d * A).PosDef)
    (c a b : κ) (he : Function.Injective ![c, a, b])
    (hca : A c a ≠ 0) (hcb : A c b ≠ 0)
    (hpa : 2 ≤ A c a * A a c) (hpb : 2 ≤ A c b * A b c) : False := by
  have hca_ne : c ≠ a := by
    intro h
    have hv := he (show (![c, a, b] (0 : Fin 3)) = (![c, a, b] (1 : Fin 3)) by
      simp [h])
    have hne : (0 : Fin 3) ≠ 1 := by decide
    exact hne hv
  have hcb_ne : c ≠ b := by
    intro h
    have hv := he (show (![c, a, b] (0 : Fin 3)) = (![c, a, b] (2 : Fin 3)) by
      simp [h])
    have hne : (0 : Fin 3) ≠ 2 := by decide
    exact hne hv
  have hab_ne : a ≠ b := by
    intro h
    have hv := he (show (![c, a, b] (1 : Fin 3)) = (![c, a, b] (2 : Fin 3)) by
      simp [h])
    have hne : (1 : Fin 3) ≠ 2 := by decide
    exact hne hv
  have hba_from_zero : A a b = 0 → A b a = 0 := by
    intro hab
    by_contra hba
    have hb := cartan_rankTwo_nonzero_bounds A hrank hab_ne.symm hba
    omega
  by_cases hab : A a b = 0
  · have hba : A b a = 0 := hba_from_zero hab
    exact not_cartan_twoStar_of_diagonal_mul_posDef A d hdiag hpos c a b he
      hab hba (by omega)
  · have hb := cartan_rankTwo_nonzero_bounds A hrank hab_ne hab
    have hca' := cartan_rankTwo_nonzero_bounds A hrank hca_ne hca
    have hcb' := cartan_rankTwo_nonzero_bounds A hrank hcb_ne hcb
    let e : Fin 3 ↪ κ := ⟨![c, a, b], he⟩
    apply not_cartan_weightedTriangle_of_diagonal_mul_posDef A d hpos e
    · intro i
      fin_cases i <;> simp [hdiag]
    · intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [e]

end Theory.AlgebraicGroup
