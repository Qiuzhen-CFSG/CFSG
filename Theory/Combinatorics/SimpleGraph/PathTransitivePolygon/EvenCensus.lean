module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.FourGeodesic

/-!
# Odd-distance census in an even polygon

In a bipartite graph with diameter at most 2d and girth at least 4d,
each vertex of the opposite type is the endpoint of exactly one odd
nonbacktracking path of length below 2d. Thus the sum of those path counts
is the full opposite-type cardinality, with no regularity or action premise.

Source: the sphere count in Aschbacher–Smith F.4.13(2), printed p.280.
-/

public noncomputable section
namespace SimpleGraph.PathTransitivePolygon
variable {V : Type*} {G : SimpleGraph V}

/-- In a bipartite polygon of diameter at most 2d and girth at least 4d,
short odd paths count the opposite vertex type exactly. -/
theorem card_opposite_of_even_polygon [Finite V] {d : ℕ} (hd : 0 < d)
    (conn : G.Connected)
    (color : V → Bool) (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 4*d ≤ c.length)
    (hdiam : ∀ v w, G.dist v w ≤ 2*d) (x : V) :
    Nat.card {y : V // color y ≠ color x} =
      ∑ k : Fin d, Nat.card {p : BasedWalk G (2*k.val+1) x // p.Nonbacktracking} := by
  classical
  let P := Σ k : Fin d, {p : BasedWalk G (2*k.val+1) x // p.Nonbacktracking}
  have hp (k : Fin d) (p : BasedWalk G (2*k.val+1) x) (hn : p.Nonbacktracking) :
      p.toWalk.IsPath :=
    isPath_of_nonbacktracking_of_cycle_bound
      (N := 4*d-1) (fun v c hc => by have := hg v c hc; omega) p hn (by omega)
  let f : P → {y : V // color y ≠ color x} := fun ⟨k,p⟩ => ⟨p.val.endpoint, by
    intro he
    have hh := (QuadrangleRecognition.even_length_iff color hcolor p.val.toWalk).mpr he.symm
    rw [BasedWalk.length_toWalk] at hh
    obtain ⟨a,ha⟩ := hh
    omega⟩
  have hi : Function.Injective f := by
    rintro ⟨i,p,hnp⟩ ⟨j,q,hnq⟩ he
    have hend : p.endpoint = q.endpoint := congrArg Subtype.val he
    have hw : p.toWalk = q.toWalk.copy rfl hend.symm := by
      by_contra hne
      obtain ⟨v,_,_,w,hw,hl⟩ := (hp i p hnp).exists_isCycle_length_le_add_of_ne
        ((Walk.isPath_copy _ _ _).mpr (hp j q hnq)) hne
      have hb := hg v w hw
      simp only [Walk.length_copy,BasedWalk.length_toWalk] at hl
      omega
    have hij : i = j := by
      apply Fin.ext
      have hl := congrArg Walk.length hw
      simp only [Walk.length_copy,BasedWalk.length_toWalk] at hl
      omega
    subst j
    apply congrArg (Sigma.mk i)
    apply Subtype.ext
    apply BasedWalk.vertices_injective
    have hs := congrArg Walk.support hw
    simpa only [Walk.support_copy,BasedWalk.support_toWalk] using hs
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨p,hp,hlen⟩ := conn.exists_path_of_dist x y.val
    have hne : ¬ Even p.length := by
      intro h
      exact y.property ((QuadrangleRecognition.even_length_iff color hcolor p).mp h).symm
    have hdia := hdiam x y.val
    have hmod : p.length % 2 ≠ 0 := by simpa only [Nat.even_iff] using hne
    let k : Fin d := ⟨p.length/2, by omega⟩
    have hl : p.length = 2*k.val+1 := by dsimp [k]; omega
    let q : BasedWalk G (2*k.val+1) x := hl ▸ BasedWalk.ofWalk p
    have hq : q.Nonbacktracking := (BasedWalk.nonbacktracking_cast hl _).mpr
      (BasedWalk.nonbacktracking_ofWalk_of_isPath p hp)
    refine ⟨⟨k,q,hq⟩,Subtype.ext ?_⟩
    change q.endpoint = y.val
    simp only [q,BasedWalk.endpoint_cast,BasedWalk.endpoint_ofWalk]
  let : Finite P := Finite.of_injective f hi
  have (k : Fin d) : Finite {p : BasedWalk G (2*k.val+1) x // p.Nonbacktracking} :=
    Finite.of_injective (fun p => (⟨k,p⟩ : P)) (fun p q he => by
      simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using he)
  rw [←Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩),Nat.card_sigma]

end SimpleGraph.PathTransitivePolygon
