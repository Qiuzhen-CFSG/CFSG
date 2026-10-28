module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortFix
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.QuadrangleRecognition

/-!
# Girth eight from five-path transitivity

Five-path transitivity in a thick graph excludes cycles through length five.
A six-cycle would have a four-edge prefix whose fixer fixes the unique
complementary two-path. Transitivity on its fifth step contradicts this.
Bipartiteness then gives girth at least eight and makes every four-path
geodesic, without a cardinality or recognition assumption.

Source: Aschbacher–Smith F.3.5(1–2), F.4.6(6,8), printed pp.271,276–277
of `refs/quasithin.pdf`. The long-prefix argument is the same as that in
`PathTransitivePolygon.SevenGirth`, specialized to the quadrangle length.
-/

public section
open SimpleGraph SimpleGraph.BasedWalk
namespace SimpleGraph.PathTransitivePolygon
variable {V A : Type*} [Group A] [MulAction A V] {G : SimpleGraph V}
private def actionIso (ha : GraphAction G A) (a : A) : G ≃g G where
  toEquiv := MulAction.toPerm a
  map_rel_iff' := ha.adj_iff a

private theorem no_cycle_of_transitive_long_prefix
    (ha : GraphAction G A)
    (hthick : ∀ v a b : V,∃z,G.Adj v z ∧ z≠a ∧ z≠b)
    {k : ℕ} (hk : 3 ≤ k)
    (ht : ∀v,RootPathTransitive G A v (k+2))
    (hg : ∀v(c:G.Walk v v),c.IsCycle → 2*k-2<c.length)
    {u : V} (c : G.Walk u u) (hc : c.IsCycle) (hl : c.length=2*k) : False := by
  have hlen : (c.take (k+1)).length=k+1 := by rw [Walk.take_length,hl,Nat.min_eq_left (by omega)]
  let p : BasedWalk G (k+1) u := hlen ▸ BasedWalk.ofWalk (c.take (k+1))
  have hp : p.Nonbacktracking := (BasedWalk.nonbacktracking_cast hlen _).mpr
    (BasedWalk.nonbacktracking_ofWalk_of_isPath _ (hc.isPath_take (by omega)))
  have hpend : p.endpoint=c.getVert (k+1) := by
    simp only [p,BasedWalk.endpoint_cast,BasedWalk.endpoint_ofWalk]
  have hprev : p.penultimate=c.getVert k := by
    have hget (n : ℕ) {x : V} (w : BasedWalk G (n+1) x) :
        w.penultimate=w.toWalk.getVert n := by
      induction n generalizing x with
      | zero => rfl
      | succ n ih => exact ih w.2
    rw [hget]
    have he : p.toWalk = (c.take (k+1)).copy rfl hpend.symm := by
      apply Walk.support_injective
      simp only [Walk.support_copy,BasedWalk.support_toWalk,p,BasedWalk.vertices_cast,
        BasedWalk.vertices_ofWalk]
    rw [he,Walk.getVert_copy,Walk.take_getVert,Nat.min_eq_right (by omega)]
  let z := c.getVert (k+2)
  have hz : G.Adj p.endpoint z := by
    rw [hpend]
    exact c.adj_getVert_succ (by omega)
  have hzprev : z ≠ p.penultimate := by
    rw [hprev]
    intro he
    have hi := hc.getVert_injOn' (by dsimp; omega) (by dsimp; omega) he
    omega
  obtain ⟨w,hw,hwz,hwprev⟩ := hthick p.endpoint z p.penultimate
  obtain ⟨a,hau,he⟩ := ht u (p.snoc hz) (p.snoc hw)
    ((nonbacktracking_snoc_iff p hz).mpr ⟨hp,hzprev⟩)
    ((nonbacktracking_snoc_iff p hw).mpr ⟨hp,hwprev⟩)
  have haend : a • z=w := by
    have hh := endpoint_smul_of_vertices ha a (p.snoc hz) (p.snoc hw) he
    simpa only [endpoint_snoc] using hh
  have heprefix : p.vertices.map (a • ·)=p.vertices := by
    have hh := congrArg (List.take (k+2)) he
    have htake (z : V) (hz : G.Adj p.endpoint z) :
        (p.snoc hz).vertices.take (k+2) = p.vertices := by
      rw [vertices_snoc,←length_vertices p,List.take_left]
    rw [←List.map_take,htake z hz,htake w hw] at hh
    exact hh
  have hafix : a • p.endpoint=p.endpoint := endpoint_smul_of_vertices ha a p p heprefix
  let q := BasedWalk.ofWalk (c.drop (k+1))
  have hq : q.Nonbacktracking := nonbacktracking_ofWalk_of_isPath _ (hc.isPath_drop (by omega))
  have hfix := BasedWalk.fixes_short_walk hg q hq (by
    simp only [Walk.drop_length,hl]
    omega) (actionIso ha a) (by
      change a • c.getVert (k+1)=c.getVert (k+1)
      simpa only [hpend] using hafix)
    (by
      change a • q.endpoint=q.endpoint
      simpa only [q,BasedWalk.endpoint_ofWalk] using hau)
  have hzmem : z ∈ q.vertices := by
    change z ∈ (BasedWalk.ofWalk (c.drop (k+1))).vertices
    rw [BasedWalk.vertices_ofWalk]
    have hh := (c.drop (k+1)).getVert_mem_support 1
    simpa only [Walk.drop_getVert,Nat.add_assoc] using hh
  exact hwz (haend.symm.trans (hfix z hzmem))

/-- Five-path transitivity in a thick bipartite graph excludes cycles below eight. -/
theorem cycle_bound_of_five_transitive
    (ha : GraphAction G A)
    (hthick : ∀ v a b : V, ∃ z, G.Adj v z ∧ z ≠ a ∧ z ≠ b)
    (ht : ∀ v, RootPathTransitive G A v 5)
    (color : V → Bool) (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (v : V) (c : G.Walk v v) (hc : c.IsCycle) : 8 ≤ c.length := by
  have hg := cycle_bound_of_root_transitivity ha hthick ht
  have hb := hg v c hc
  obtain ⟨k,hk⟩ := (QuadrangleRecognition.even_length_iff color hcolor c).mpr rfl
  by_contra h
  have hl : c.length = 6 := by omega
  exact no_cycle_of_transitive_long_prefix ha hthick (by decide : 3 ≤ 3) ht
    (fun x w hw => by have := hg x w hw; omega) c hc hl

/-- At half the girth, a nonbacktracking walk is geodesic; equality of
lengths is allowed, although uniqueness need not hold at that length. -/
theorem geodesic_of_nonbacktracking_of_double_le_girth
    (hconn : G.Connected) {n : ℕ}
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 2*n ≤ c.length)
    {x : V} (p : BasedWalk G n x) (hp : p.Nonbacktracking) :
    G.dist x p.endpoint = n := by
  by_cases hn : n = 0
  · subst n
    simp only [BasedWalk.endpoint, dist_self]
  have hpath := isPath_of_nonbacktracking_of_cycle_bound
    (N := 2*n-1) (fun v c hc => by have := hg v c hc; omega) p hp (by omega)
  have hd := G.dist_le p.toWalk
  rw [BasedWalk.length_toWalk] at hd
  apply le_antisymm hd
  by_contra h
  obtain ⟨q,hq⟩ := hconn.exists_walk_length_eq_dist x p.endpoint
  have hne : p.toWalk ≠ q := by
    intro he
    have hh := congrArg Walk.length he
    rw [BasedWalk.length_toWalk,hq] at hh
    omega
  obtain ⟨v,_,_,c,hc,hlen⟩ := hpath.exists_isCycle_length_le_add_of_ne
    (q.isPath_of_length_eq_dist hq) hne
  have hb := hg v c hc
  rw [BasedWalk.length_toWalk,hq] at hlen
  omega
end SimpleGraph.PathTransitivePolygon
