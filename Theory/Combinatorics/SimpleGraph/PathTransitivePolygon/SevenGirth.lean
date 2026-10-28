module

public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortFix
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.QuadrangleRecognition

/-!
# Girth twelve from seven-path transitivity

Seven-path transitivity first excludes cycles through length seven. On an
eight-cycle, a five-edge prefix has a unique three-edge complement. Its
pointwise fixer must fix that complement, contrary to transitivity on the
forward extensions. The same argument then excludes ten-cycles using a
six-edge prefix and its unique four-edge complement. Bipartiteness excludes
odd cycles. Neither finiteness nor a distance-six witness is assumed.

This supplies the short-geodesic input to Aschbacher–Smith F.3.6 and F.4.26,
printed pp.272 and 288.
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

/-- Seven-path transitivity in a thick bipartite graph excludes all cycles below twelve. -/
theorem cycle_bound_of_seven_transitive
    (ha : GraphAction G A)
    (hthick : ∀v a b : V,∃z,G.Adj v z ∧ z≠a ∧ z≠b)
    (ht : ∀v,RootPathTransitive G A v 7)
    (color : V → Bool) (hcolor : ∀{u v},G.Adj u v → color u≠color v)
    (v : V) (c : G.Walk v v) (hc : c.IsCycle) : 12≤c.length := by
  have hdeg : HasTwoNeighbors G := by
    intro x y
    obtain ⟨z,hz,hy,_⟩ := hthick x y y
    exact ⟨z,hz,hy⟩
  have hg7 := cycle_bound_of_root_transitivity ha hthick ht
  have heven (x : V) (w : G.Walk x x) : Even w.length :=
    (QuadrangleRecognition.even_length_iff color hcolor w).mpr rfl
  have hg9 : ∀x(w:G.Walk x x),w.IsCycle → 9<w.length := by
    intro x w hw
    have h7 := hg7 x w hw
    obtain ⟨k,hk⟩ := heven x w
    by_contra h
    have hh : w.length=8 := by omega
    exact no_cycle_of_transitive_long_prefix ha hthick (by decide : 3≤4)
      (fun x => (ht x).mono hdeg (by decide))
      (fun x w hw => by have := hg7 x w hw; omega) w hw hh
  have h9 := hg9 v c hc
  obtain ⟨k,hk⟩ := heven v c
  by_contra h
  have hh : c.length=10 := by omega
  exact no_cycle_of_transitive_long_prefix ha hthick (by decide : 3≤5) ht
    (fun x w hw => by have := hg9 x w hw; omega) c hc hh
end SimpleGraph.PathTransitivePolygon
