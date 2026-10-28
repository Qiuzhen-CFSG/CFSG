module
public import Theory.GroupAction.CubicTree.ArcRegularity

/-!
# Extending transitive paths from a fixed root

First align the prefixes, then use their pointwise fixer to align the last
vertex. Iterating this step keeps the root fixed. In particular, different
vertex orbits may have different maximal transitivity lengths.
No finiteness, valence, connectivity or tree assumption is required.

Source: the path convention in Aschbacher--Smith F.3.2--4, p.270, and the
prefix induction of Goldschmidt (1980), Lemma (2.12), p.383.
-/

public section
namespace SimpleGraph.PathTransitivePolygon
open SimpleGraph.BasedWalk Theory.GroupAction.CubicTree
variable {V A : Type*} [Group A] [MulAction A V] {Γ : SimpleGraph V}

/-- Transitivity on prefixes and on their forward extensions gives the next length. -/
theorem RootPathTransitive.succ_of_rightRegular
    (h : GraphAction Γ A) {x : V} {n : ℕ}
    (ht : RootPathTransitive Γ A x n)
    (hstep : ∀ p : BasedWalk Γ n x, p.Nonbacktracking → RightRegular (A := A) p) :
    RootPathTransitive Γ A x (n + 1) := by
  intro p q hp hq
  let p₀ := p.take n (Nat.le_succ n)
  let q₀ := q.take n (Nat.le_succ n)
  have hp₀ : p₀.Nonbacktracking := nonbacktracking_take (Nat.le_succ n) p hp
  have hq₀ : q₀.Nonbacktracking := nonbacktracking_take (Nat.le_succ n) q hq
  obtain ⟨g, hg, hprefix⟩ := ht p₀ q₀ hp₀ hq₀
  let r : BasedWalk Γ n x := hg ▸ p₀.map (h.hom g)
  have hrq : r = q₀ := by
    apply BasedWalk.vertices_injective n x
    calc
      r.vertices = (p₀.map (h.hom g)).vertices := vertices_cast_base hg _
      _ = p₀.vertices.map (g • ·) := BasedWalk.vertices_map _ _
      _ = q₀.vertices := hprefix
  have hpforward : Forward p₀ p.endpoint := by
    have hadj : Γ.Adj p₀.endpoint p.endpoint := by
      simpa only [p₀, endpoint_take_penultimate] using p.adj_penultimate_endpoint
    apply (forward_iff_snoc_nonbacktracking p₀ hp₀ hadj).2
    simpa only [p₀, snoc_take] using hp
  have hqforward : Forward q₀ q.endpoint := by
    have hadj : Γ.Adj q₀.endpoint q.endpoint := by
      simpa only [q₀, endpoint_take_penultimate] using q.adj_penultimate_endpoint
    apply (forward_iff_snoc_nonbacktracking q₀ hq₀ hadj).2
    simpa only [q₀, snoc_take] using hq
  have hgforward : Forward q₀ (g • p.endpoint) := by
    rw [← hrq]
    exact (forward_cast_base hg (p₀.map (h.hom g))).2
      ((forward_map_iff h g p₀).2 hpforward)
  obtain ⟨a, hafix, haend⟩ :=
    (hstep q₀ hq₀) (g • p.endpoint) q.endpoint
      hgforward hqforward
  have hxmem : x ∈ q₀.vertices := by
    have hmem := q₀.toWalk.start_mem_support
    simpa only [BasedWalk.support_toWalk] using hmem
  refine ⟨a * g, by rw [mul_smul, hg]; exact hafix x hxmem, ?_⟩
  have hfixed : q₀.vertices.map (a • ·) = q₀.vertices := by
    simpa only [List.map_id] using
      (List.map_congr_left (f := fun y => a • y) (g := id) hafix)
  calc
    p.vertices.map ((a * g) • ·) =
        (p₀.vertices ++ [p.endpoint]).map ((a * g) • ·) := by
          rw [BasedWalk.vertices_eq_prefix_append_endpoint]
    _ = (p₀.vertices.map (g • ·)).map (a • ·) ++ [a • (g • p.endpoint)] := by
      simp only [List.map_append, List.map_singleton, List.map_map, mul_smul,
        Function.comp_def]
    _ = q₀.vertices ++ [q.endpoint] := by rw [hprefix, hfixed, haend]
    _ = q.vertices := (BasedWalk.vertices_eq_prefix_append_endpoint q).symm

/-- Induction at one fixed root; no transitivity at the other vertex type is required. -/
theorem RootPathTransitive.extend_of_rightRegular
    (h : GraphAction Γ A) {x : V} {m N : ℕ}
    (ht : RootPathTransitive Γ A x m)
    (hsteps : ∀ n, m ≤ n → n < N → RootPathTransitive Γ A x n →
      ∀ p : BasedWalk Γ n x, p.Nonbacktracking → RightRegular (A := A) p)
    (hmN : m ≤ N) : RootPathTransitive Γ A x N := by
  have hh : ∀ n, m ≤ n → n ≤ N → RootPathTransitive Γ A x n := by
    intro n
    induction n with
    | zero =>
      intro hm hn
      have he : m = 0 := by omega
      subst m
      exact ht
    | succ n ih =>
      intro hm hn
      by_cases he : m = n + 1
      · exact he ▸ ht
      · have hmn : m ≤ n := by omega
        have ht' := ih hmn (by omega)
        exact ht'.succ_of_rightRegular h (hsteps n hmn (by omega) ht')
  exact hh N hmN le_rfl
end SimpleGraph.PathTransitivePolygon
