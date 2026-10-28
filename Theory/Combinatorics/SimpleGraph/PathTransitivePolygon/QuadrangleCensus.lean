module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.FourGeodesic

/-!
# The two odd-distance shells of a quadrangle

Girth at least eight makes paths of length one or three unique between
their endpoints. Bipartiteness and diameter at most four exhaust the
opposite vertex type by those two path sets. Their disjoint sum therefore
counts that type, retaining unequal valencies in later applications.

Source: Aschbacher–Smith F.4.13(2), printed p.280 of `refs/quasithin.pdf`.
-/

public noncomputable section
namespace SimpleGraph.PathTransitivePolygon.QuadrangleRecognition
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

private theorem short_walk_unique
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 8 ≤ c.length)
    {x : V} {n : ℕ} (hn : n ≤ 3)
    (p q : BasedWalk G n x) (hp : p.Nonbacktracking) (hq : q.Nonbacktracking)
    (he : p.endpoint = q.endpoint) : p = q := by
  have hg' : ∀ v (c : G.Walk v v), c.IsCycle → 7 < c.length := by
    intro v c hc
    have := hg v c hc
    omega
  have hpp := isPath_of_nonbacktracking_of_cycle_bound hg' p hp (by omega)
  have hqp := isPath_of_nonbacktracking_of_cycle_bound hg' q hq (by omega)
  have hw : p.toWalk = q.toWalk.copy rfl he.symm := by
    by_contra hne
    obtain ⟨v,_,_,c,hc,hlen⟩ := hpp.exists_isCycle_length_le_add_of_ne
      (by simpa only [Walk.isPath_copy] using hqp) hne
    have hb := hg v c hc
    simp only [BasedWalk.length_toWalk, Walk.length_copy] at hlen
    omega
  apply BasedWalk.vertices_injective n x
  have hs := congrArg Walk.support hw
  simpa only [Walk.support_copy,BasedWalk.support_toWalk] using hs

/-- In a bipartite quadrangle, vertices of the opposite type are counted
by the unique paths of length one or three from a fixed vertex. -/
theorem card_opposite_of_quadrangle [Finite V]
    (conn : G.Connected)
    (color : V → Bool) (hcolor : ∀ {u v}, G.Adj u v → color u ≠ color v)
    (hg : ∀ v (c : G.Walk v v), c.IsCycle → 8 ≤ c.length)
    (hdiam : ∀ v w, G.dist v w ≤ 4) (x : V) :
    Nat.card {y : V // color y ≠ color x} =
      Nat.card {p : BasedWalk G 1 x // p.Nonbacktracking} +
      Nat.card {p : BasedWalk G 3 x // p.Nonbacktracking} := by
  classical
  let P (n : ℕ) := {p : BasedWalk G n x // p.Nonbacktracking}
  have hodd {n : ℕ} (hn : n = 1 ∨ n = 3) (p : P n) : color p.val.endpoint ≠ color x := by
    intro he
    have hh := (even_length_iff color hcolor p.val.toWalk).mpr he.symm
    rw [BasedWalk.length_toWalk] at hh
    obtain ⟨k,hk⟩ := hh
    omega
  let f : P 1 ⊕ P 3 → {y : V // color y ≠ color x} :=
    Sum.elim (fun p => ⟨p.val.endpoint,hodd (Or.inl rfl) p⟩)
      (fun p => ⟨p.val.endpoint,hodd (Or.inr rfl) p⟩)
  have hgeo {n : ℕ} (hn : n ≤ 3) (p : P n) : G.dist x p.val.endpoint = n :=
    geodesic_of_nonbacktracking_of_cycle_bound conn
      (N := 7) (fun v c hc => by have := hg v c hc; omega) p.val p.property (by omega)
  have hneq (p : P 1) (q : P 3) : p.val.endpoint ≠ q.val.endpoint := by
    intro he
    have hp := hgeo (by decide) p
    have hq := hgeo (by decide) q
    rw [he,hq] at hp
    contradiction
  have hi : Function.Injective f := by
    intro p q he
    have hv := congrArg Subtype.val he
    cases p with
    | inl p =>
      cases q with
      | inl q => exact congrArg Sum.inl (Subtype.ext
          (short_walk_unique hg (by decide) p.val q.val p.property q.property hv))
      | inr q => exact (hneq p q hv).elim
    | inr p =>
      cases q with
      | inl q => exact (hneq q p hv.symm).elim
      | inr q => exact congrArg Sum.inr (Subtype.ext
          (short_walk_unique hg (by decide) p.val q.val p.property q.property hv))
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨p,hp,hlen⟩ := conn.exists_path_of_dist x y.val
    have hne : ¬ Even p.length := by
      intro h
      exact y.property ((even_length_iff color hcolor p).mp h).symm
    have hd := hdiam x y.val
    have hl : p.length = 1 ∨ p.length = 3 := by
      have hm : p.length % 2 ≠ 0 := by simpa only [Nat.even_iff] using hne
      omega
    rcases hl with hl | hl
    · let q : BasedWalk G 1 x := hl ▸ BasedWalk.ofWalk p
      have hq : q.Nonbacktracking := (BasedWalk.nonbacktracking_cast hl _).mpr
        (BasedWalk.nonbacktracking_ofWalk_of_isPath p hp)
      refine ⟨Sum.inl ⟨q,hq⟩,Subtype.ext ?_⟩
      change q.endpoint = y.val
      simp only [q,BasedWalk.endpoint_cast,BasedWalk.endpoint_ofWalk]
    · let q : BasedWalk G 3 x := hl ▸ BasedWalk.ofWalk p
      have hq : q.Nonbacktracking := (BasedWalk.nonbacktracking_cast hl _).mpr
        (BasedWalk.nonbacktracking_ofWalk_of_isPath p hp)
      refine ⟨Sum.inr ⟨q,hq⟩,Subtype.ext ?_⟩
      change q.endpoint = y.val
      simp only [q,BasedWalk.endpoint_cast,BasedWalk.endpoint_ofWalk]
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩),Nat.card_sum]
end SimpleGraph.PathTransitivePolygon.QuadrangleRecognition
