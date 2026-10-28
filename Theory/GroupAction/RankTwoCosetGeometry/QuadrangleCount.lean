module
public import Theory.Combinatorics.SimpleGraph.PathTransitivePolygon.FiveGirth
public import Theory.Combinatorics.SimpleGraph.NonbacktrackingCount
public import Theory.GroupAction.RankTwoCosetGeometry.ProjectivePlane

/-!
# Counting the two vertex types of a regular generalized quadrangle

Girth eight gives uniqueness of one- and three-paths to their endpoints.
Diameter four and parity put every vertex of the opposite type at distance
one or three. Their disjoint path counts therefore give (q+1)(q²+1)
vertices of either type. This is the order calculation in
Aschbacher–Smith F.4.13(2), printed p.280 of `refs/quasithin.pdf`.
-/

public noncomputable section
open SimpleGraph SimpleGraph.PathTransitivePolygon
namespace Subgroup.CosetGeometry.RankTwo
variable {G : Type*} [Group G] (F : Bool → Subgroup G)
variable (hgen : F false ⊔ F true = ⊤)
variable (hgirth : ∀ v (p : (graph F).Walk v v), p.IsCycle → 8 ≤ p.length)

include hgirth in
private theorem short_endpoint_injective {n : ℕ} (hn : n ≤ 3) {v : Vertex F} :
    Function.Injective (fun p : {p : BasedWalk (graph F) n v // p.Nonbacktracking} =>
      p.val.endpoint) := by
  intro p q he
  have hg : ∀ x (w : (graph F).Walk x x), w.IsCycle → 7 < w.length := by
    intro x w hw
    have := hgirth x w hw
    omega
  have hp := isPath_of_nonbacktracking_of_cycle_bound hg p.val p.property (by omega)
  have hq := isPath_of_nonbacktracking_of_cycle_bound hg q.val q.property (by omega)
  have hh : p.val.toWalk = q.val.toWalk.copy rfl he.symm := by
    by_contra hne
    obtain ⟨x,_,_,w,hw,hlen⟩ := hp.exists_isCycle_length_le_add_of_ne
      (by simpa only [Walk.isPath_copy] using hq) hne
    have hb := hg x w hw
    rw [Walk.length_copy,BasedWalk.length_toWalk,BasedWalk.length_toWalk] at hlen
    omega
  apply Subtype.ext
  apply BasedWalk.vertices_injective n v
  have hs := congrArg Walk.support hh
  simpa only [Walk.support_copy,BasedWalk.support_toWalk] using hs

private theorem odd_endpoint_type {n : ℕ} (hn : Odd n) {v : Vertex F}
    (p : BasedWalk (graph F) n v) : p.endpoint.type = !v.type := by
  have hne : v.type ≠ p.endpoint.type := by
    intro he
    have hh := (even_walk_iff F p.toWalk).mpr he
    rw [BasedWalk.length_toWalk] at hh
    exact (Nat.not_even_iff_odd.mpr hn) hh
  cases hv : v.type <;> cases hw : p.endpoint.type <;> simp_all

include hgen hgirth in
/-- The opposite type is precisely the disjoint set of endpoints of
nonbacktracking one- and three-paths from any fixed root. -/
theorem card_opposite_fiber_of_quadrangle [Finite G]
    (hdiam : ∀ v w, (graph F).dist v w ≤ 4) (v : Vertex F) :
    Nat.card (Fiber F (!v.type)) =
      Nat.card {p : BasedWalk (graph F) 1 v // p.Nonbacktracking} +
      Nat.card {p : BasedWalk (graph F) 3 v // p.Nonbacktracking} := by
  let P (n : ℕ) := {p : BasedWalk (graph F) n v // p.Nonbacktracking}
  let f : P 1 ⊕ P 3 → Fiber F (!v.type) := fun p => match p with
    | .inl p => ⟨p.val.endpoint,odd_endpoint_type F (by decide) p.val⟩
    | .inr p => ⟨p.val.endpoint,odd_endpoint_type F (by decide) p.val⟩
  have hdist (n : ℕ) (hn : n ≤ 3) (p : P n) : (graph F).dist v p.val.endpoint = n :=
    geodesic_of_nonbacktracking_of_cycle_bound (connected F hgen)
      (N := 7) (fun x w hw => by have := hgirth x w hw; omega)
      p.val p.property (by omega)
  have hi : Function.Injective f := by
    intro p q he
    have hh := congrArg Subtype.val he
    cases p with
    | inl p => cases q with
      | inl q => exact congrArg Sum.inl (short_endpoint_injective F hgirth (by decide) hh)
      | inr q => have h1 := hdist 1 (by decide) p
                 have h3 := hdist 3 (by decide) q
                 change p.val.endpoint = q.val.endpoint at hh
                 rw [hh] at h1
                 omega
    | inr p => cases q with
      | inl q => have h3 := hdist 3 (by decide) p
                 have h1 := hdist 1 (by decide) q
                 change p.val.endpoint = q.val.endpoint at hh
                 rw [hh] at h3
                 omega
      | inr q => exact congrArg Sum.inr (short_endpoint_injective F hgirth (by decide) hh)
  have hs : Function.Surjective f := by
    intro w
    have ho : Odd ((graph F).dist v w.val) := (odd_dist_iff F hgen v w.val).mpr (by
      rw [w.property]
      cases v.type <;> decide)
    have hd := hdiam v w.val
    obtain ⟨k,hk⟩ := ho
    have hc : (graph F).dist v w.val = 1 ∨ (graph F).dist v w.val = 3 := by omega
    obtain ⟨p,hp,he⟩ := BasedWalk.exists_geodesic ((connected F hgen) v w.val)
    rcases hc with hc | hc
    · let q : BasedWalk (graph F) 1 v := hc ▸ p
      refine ⟨.inl ⟨q,(BasedWalk.nonbacktracking_cast hc p).mpr hp⟩,Subtype.ext ?_⟩
      simpa only [f,q,BasedWalk.endpoint_cast] using he
    · let q : BasedWalk (graph F) 3 v := hc ▸ p
      refine ⟨.inr ⟨q,(BasedWalk.nonbacktracking_cast hc p).mpr hp⟩,Subtype.ext ?_⟩
      simpa only [f,q,BasedWalk.endpoint_cast] using he
  exact (Nat.card_congr (Equiv.ofBijective f ⟨hi,hs⟩)).symm.trans Nat.card_sum

/-- Constant valence gives the rooted path census independently of girth. -/
theorem card_paths_of_constant_valence (q : ℕ)
    (hv : ∀ v, Nat.card ((graph F).neighborSet v) = q + 1)
    (k : ℕ) (v : Vertex F) :
    Nat.card {p : BasedWalk (graph F) (k+1) v // p.Nonbacktracking} = (q+1)*q^k := by
  have hf {v w : Vertex F} (h : (graph F).Adj v w) : w.type = !v.type := by
    have hne := h.1
    cases hv : v.type <;> cases hw : w.type <;> simp_all
  have : ∀ v : Vertex F, Finite ((graph F).neighborSet v) :=
    fun v => Nat.finite_of_card_ne_zero (by rw [hv]; omega)
  rw [BasedWalk.card_nonbacktracking_succ (graph F) (fun v => v.type)
    (fun _ => q+1) hf hv]
  congr 1
  generalize (!v.type) = b
  induction k generalizing b with
  | zero => rfl
  | succ k ih => simp [BasedWalk.forwardCount,ih,pow_succ,mul_comm]

include hgen hgirth in
/-- The coset index in either type of a regular quadrangle. -/
theorem index_of_quadrangle_geometry [Finite G]
    (hdiam : ∀ v w, (graph F).dist v w ≤ 4) (q : ℕ)
    (hv : ∀ v, Nat.card ((graph F).neighborSet v) = q+1) (i : Bool) :
    (F i).index = (q+1)*(q^2+1) := by
  have hc := card_opposite_fiber_of_quadrangle F hgen hgirth hdiam (base F (!i))
  have ht : (!(base F (!i)).type) = i := Bool.not_not i
  rw [ht, Nat.card_congr (fiberEquivQuotient F i), ←Subgroup.index_eq_card,
    card_paths_of_constant_valence F q hv 0,card_paths_of_constant_valence F q hv 2] at hc
  rw [hc]
  ring
end Subgroup.CosetGeometry.RankTwo
