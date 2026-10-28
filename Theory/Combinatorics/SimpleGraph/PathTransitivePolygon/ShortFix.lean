module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.ShortGirth
/-!
# Automorphisms fixing the ends of a short nonbacktracking walk

Below half the cycle bound, a nonbacktracking walk is the unique path between
its endpoints. A graph automorphism fixing those endpoints therefore fixes
its ordered vertex list pointwise. This supplies short-path stabilizer
transport through coset coverings, before any global recognition theorem.
-/

public section
namespace SimpleGraph.BasedWalk
open Walk
variable {V : Type*} {G : SimpleGraph V}
theorem fixes_short_walk {N n : ℕ}
    (hg : ∀ v(c:G.Walk v v),c.IsCycle → N<c.length)
    {x : V} (p : BasedWalk G n x) (hp : p.Nonbacktracking) (hn : 2*n≤N)
    (f : G ≃g G) (hx : f x=x) (hy : f p.endpoint=p.endpoint) :
    ∀w∈p.vertices,f w=w := by
  have hpath := PathTransitivePolygon.isPath_of_nonbacktracking_of_cycle_bound hg p hp (by omega)
  let q : G.Walk x p.endpoint := (p.toWalk.map f.toHom).copy hx hy
  have hq : q.IsPath := by
    rw [Walk.isPath_copy]
    exact hpath.map f.injective
  have he : q=p.toWalk := by
    by_contra hne
    obtain ⟨v,_,_,c,hc,hcL⟩ := hq.exists_isCycle_length_le_add_of_ne hpath hne
    have hb := hg v c hc
    have hlen : q.length=n := by simp only [q,Walk.length_copy,Walk.length_map,length_toWalk]
    rw [hlen,length_toWalk] at hcL
    omega
  have hs := congrArg Walk.support he
  simp only [q,Walk.support_copy,Walk.support_map,support_toWalk] at hs
  simpa only [List.map_id,id_eq] using
    (List.map_inj_left (l:=p.vertices) (f:=f) (g:=id)).mp
      (hs.trans (List.map_id _).symm)
end SimpleGraph.BasedWalk
