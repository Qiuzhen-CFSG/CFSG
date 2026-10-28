module

public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon

/-!
# Girth forced by rooted nonbacktracking path transitivity

In a thick graph, changing the last vertex of a closed nonbacktracking walk
produces an open walk of the same length. Rooted path transitivity cannot map
one to the other. Thus N-path transitivity excludes cycles of length at mostN.
Comparing two short paths then makes every nonbacktracking walk of length at
mostN/2 geodesic.

This applies to faithful binary Ree completions before any smallness or global
recognition theorem. It supplies the four-step metric fact in Aschbacher–Smith
F.4.6 and J.4.7, without circularly assuming the later octagon conclusion.
-/

public section
namespace SimpleGraph.BasedWalk
variable {V : Type*} {G : SimpleGraph V}

theorem nonbacktracking_ofWalk_of_isCycle {u : V} (p : G.Walk u u) (hp : p.IsCycle) :
    (ofWalk p).Nonbacktracking := by
  cases p with
  | nil => simp at hp
  | @cons u v u h p =>
    have ht := (Walk.cons_isCycle_iff p h).mp hp
    cases p with
    | nil => exact (h.ne rfl).elim
    | @cons v w u h' p =>
      have hn := nonbacktracking_ofWalk_of_isPath _ ht.1
      refine ⟨?_,hn⟩
      intro he
      change w=u at he
      subst w
      exact ht.2 (by simp)

theorem endpoint_take_penultimate {n : ℕ} {x : V} (p : BasedWalk G (n+1) x) :
    (p.take n (Nat.le_succ n)).endpoint=p.penultimate := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => exact ih p.2

end SimpleGraph.BasedWalk

namespace SimpleGraph.PathTransitivePolygon
variable {V A : Type*} {G : SimpleGraph V} [Group A] [MulAction A V]

theorem cycle_bound_of_root_transitivity (hact : GraphAction G A)
    (hthick : ∀ v a b : V,∃z,G.Adj v z ∧ z≠a ∧ z≠b)
    {N : ℕ} (ht : ∀u,RootPathTransitive G A u N)
    (u : V) (c : G.Walk u u) (hc : c.IsCycle) : N<c.length := by
  by_contra hnot
  have hle : c.length≤N := by omega
  have hdeg : BasedWalk.HasTwoNeighbors G := by
    intro v a
    obtain ⟨z,hz,hza,_⟩ := hthick v a a
    exact ⟨z,hz,hza⟩
  have hthree := hc.three_le_length
  obtain ⟨j,hj⟩ : ∃j,c.length=j+1+1 := ⟨c.length-2,by omega⟩
  let p : BasedWalk G (j+1+1) u := hj ▸ BasedWalk.ofWalk c
  have hp : p.Nonbacktracking := by simpa [p] using BasedWalk.nonbacktracking_ofWalk_of_isCycle c hc
  have hend : p.endpoint=u := by simp [p,BasedWalk.endpoint_ofWalk]
  let q := p.take (j+1) (Nat.le_succ (j+1))
  have hq : q.Nonbacktracking := BasedWalk.nonbacktracking_take _ p hp
  obtain ⟨z,hz,hzu,hzprev'⟩ := hthick q.endpoint u q.penultimate
  let q' := q.snoc hz
  have hq' : q'.Nonbacktracking := (BasedWalk.nonbacktracking_snoc_iff q hz).mpr ⟨hq,hzprev'⟩
  have hshort : RootPathTransitive G A u (j+1+1) := (ht u).mono hdeg (by omega)
  obtain ⟨a,hau,ha⟩ := hshort p q' hp hq'
  have he := endpoint_smul_of_vertices hact a p q' ha
  rw [hend,hau,BasedWalk.endpoint_snoc] at he
  exact hzu he.symm

end SimpleGraph.PathTransitivePolygon

namespace SimpleGraph.PathTransitivePolygon
variable {V : Type*} {G : SimpleGraph V}

theorem isPath_of_nonbacktracking_of_cycle_bound {N n : ℕ}
    (hg : ∀ v(c:G.Walk v v),c.IsCycle → N<c.length)
    {x : V} (p : BasedWalk G n x) (hp : p.Nonbacktracking) (hn : n≤N) :
    p.toWalk.IsPath := by
  classical
  induction n generalizing x with
  | zero => exact Walk.IsPath.nil
  | succ n ih =>
    have ht : p.2.Nonbacktracking := by
      cases n with
      | zero => trivial
      | succ n => exact hp.2
    have htpath := ih p.2 ht (by omega)
    apply (Walk.cons_isPath_iff p.1.property p.2.toWalk).mpr
    refine ⟨htpath, ?_⟩
    intro hx
    cases n with
    | zero =>
      have he : x = (p.1 : V) := by
        rw [BasedWalk.support_toWalk] at hx
        exact List.mem_singleton.mp hx
      exact p.1.property.ne he
    | succ n =>
      let r := p.2.toWalk.takeUntil x hx
      have hr : r.IsPath := htpath.takeUntil hx
      have he : s(x, (p.1 : V)) ∉ r.edges := by
        intro he
        have hl : r.length = 1 := hr.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using he)
        have hs : r.snd = x := by
          change r.getVert 1 = x
          simpa only [hl] using r.getVert_length
        have hs' : r.snd = (p.2.1 : V) := by
          have hbase : p.2.toWalk.snd = (p.2.1 : V) :=
            (Walk.getVert_cons_succ (n := 0) p.2.2.toWalk p.2.1.property).trans
              (Walk.getVert_zero _)
          exact (Walk.snd_takeUntil p.1.property.ne p.2.toWalk hx).trans hbase
        exact hp.1 (hs'.symm.trans hs)
      have hc : (Walk.cons p.1.property r).IsCycle := (Walk.cons_isCycle_iff r _).mpr ⟨hr, he⟩
      have hbound := hg x _ hc
      have hlen := p.2.toWalk.length_takeUntil_le_length hx
      rw [BasedWalk.length_toWalk] at hlen
      change N<r.length + 1 at hbound
      change r.length ≤ n + 1 at hlen
      omega

theorem geodesic_of_nonbacktracking_of_cycle_bound (conn : G.Connected) {N n : ℕ}
    (hg : ∀ v(c:G.Walk v v),c.IsCycle →N<c.length)
    {x : V} (p : BasedWalk G n x) (hp : p.Nonbacktracking) (hn : 2*n≤N) :
    G.dist x p.endpoint=n := by
  have hpath := isPath_of_nonbacktracking_of_cycle_bound hg p hp (by omega)
  obtain ⟨q,hq⟩ := conn.exists_walk_length_eq_dist x p.endpoint
  have hqpath := q.isPath_of_length_eq_dist hq
  have hd := G.dist_le p.toWalk
  rw [BasedWalk.length_toWalk] at hd
  have he : p.toWalk=q := by
    by_contra hne
    obtain ⟨v,_,_,c,hc,hlen⟩ := hpath.exists_isCycle_length_le_add_of_ne hqpath hne
    have hb := hg v c hc
    rw [BasedWalk.length_toWalk,hq] at hlen
    omega
  rw [←hq,←he,BasedWalk.length_toWalk]

end SimpleGraph.PathTransitivePolygon
