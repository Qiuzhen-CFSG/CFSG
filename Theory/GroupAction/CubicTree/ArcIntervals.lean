module

public import Theory.GroupAction.CubicTree.ArcRegularity
public import Mathlib.Combinatorics.SimpleGraph.Paths

/-!
# Literal subarcs between two positions

Subarcs use Mathlib's walk truncations and the existing `BasedWalk` conversion.
Their vertex sets are exactly the inclusive index intervals. This identifies
the actual pointwise arc fixers with the interval intersections used in
Goldschmidt's overlapping-stabilizer argument (2.13), printed p.384.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
open SimpleGraph SimpleGraph.BasedWalk
universe u
variable {V : Type u} {Γ : SimpleGraph V}

/-- The subarc from position `j` through position `i`, inclusive. -/
def segment {x y : V} (p : Γ.Walk x y) (j i : ℕ) (hji : j ≤ i) (hi : i ≤ p.length) :
    BasedWalk Γ (i - j) (p.getVert j) :=
  (by simp only [Walk.take_length, Walk.drop_length]; omega :
    ((p.drop j).take (i - j)).length = i - j) ▸
      BasedWalk.ofWalk ((p.drop j).take (i - j))

theorem segment_nonbacktracking {x y : V} (p : Γ.Walk x y) (hp : p.IsPath)
    (j i : ℕ) (hji : j ≤ i) (hi : i ≤ p.length) :
    (segment p j i hji hi).Nonbacktracking := by
  unfold segment
  apply (BasedWalk.nonbacktracking_cast _ _).2
  exact BasedWalk.nonbacktracking_ofWalk_of_isPath _ ((hp.drop j).take (i - j))

@[simp] theorem endpoint_segment {x y : V} (p : Γ.Walk x y)
    (j i : ℕ) (hji : j ≤ i) (hi : i ≤ p.length) :
    (segment p j i hji hi).endpoint = p.getVert i := by
  simp only [segment, BasedWalk.endpoint_cast, BasedWalk.endpoint_ofWalk, Walk.drop_getVert]
  congr 1
  omega

theorem mem_vertices_segment {x y z : V} (p : Γ.Walk x y)
    (j i : ℕ) (hji : j ≤ i) (hi : i ≤ p.length) :
    z ∈ (segment p j i hji hi).vertices ↔
      ∃ k, j ≤ k ∧ k ≤ i ∧ p.getVert k = z := by
  simp only [segment, BasedWalk.vertices_cast, BasedWalk.vertices_ofWalk,
    Walk.mem_support_iff_exists_getVert, Walk.take_length, Walk.drop_length,
    Walk.take_getVert, Walk.drop_getVert]
  constructor
  · rintro ⟨k, hk, hki⟩
    have hki' : k ≤ i - j := by omega
    refine ⟨j + k, by omega, by omega, ?_⟩
    simpa only [Nat.min_eq_right hki'] using hk
  · rintro ⟨k, hjk, hki, hk⟩
    refine ⟨k - j, ?_, by omega⟩
    have hle : k - j ≤ i - j := by omega
    simpa only [Nat.min_eq_right hle, Nat.add_sub_of_le hjk] using hk

private theorem forward_of_adj_of_not_mem {n : ℕ} {x z : V} (p : BasedWalk Γ n x)
    (hadj : Γ.Adj p.endpoint z) (hm : z ∉ p.vertices) : Forward p z := by
  cases n with
  | zero => exact hadj
  | succ n =>
    refine ⟨hadj, ?_⟩
    intro he
    apply hm
    have hh := (p.take n (Nat.le_succ n)).toWalk.end_mem_support
    rw [BasedWalk.support_toWalk, BasedWalk.endpoint_take_penultimate,
      BasedWalk.vertices_take] at hh
    exact he ▸ List.mem_of_mem_take hh

theorem segment_next_forward {x y : V} (p : Γ.Walk x y) (hp : p.IsPath)
    (j i : ℕ) (hji : j ≤ i) (hi : i < p.length) :
    Forward (segment p j i hji hi.le) (p.getVert (i + 1)) := by
  have hadj : Γ.Adj (segment p j i hji hi.le).endpoint (p.getVert (i + 1)) := by
    rw [endpoint_segment]
    exact p.adj_getVert_succ hi
  apply forward_of_adj_of_not_mem _ hadj
  intro hm
  obtain ⟨k, hjk, hki, hke⟩ := (mem_vertices_segment p j i hji hi.le).1 hm
  have hk : k = i + 1 := hp.getVert_injOn
    (by change k ≤ p.length; omega) (by change i + 1 ≤ p.length; omega) hke
  omega

end Theory.GroupAction.CubicTree
