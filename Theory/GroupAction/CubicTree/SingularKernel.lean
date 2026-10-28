module

public import Theory.GroupAction.CubicTree.ArcRegularity

/-!
# Trivial stabilizers of totally singular arcs

If every arc of a fixed positive length is totally singular at both ends,
an element fixing one such arc fixes every vertex. The proof moves a fixed
arc across each adjacent edge. Moving forward drops its first vertex; moving
backward prepends a fixed extension and drops its last vertex. Connectedness
then propagates the fixed arc to every vertex.

Only minimum valence two is needed for this step of the cubic-tree argument.
Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980), remark after
(2.12), printed p.384.
-/

@[expose] public section

namespace Theory.GroupAction.CubicTree

open SimpleGraph SimpleGraph.BasedWalk

universe u v
variable {V : Type u} {A : Type v} {Γ : SimpleGraph V}
variable [Group A] [MulAction A V]

private theorem fixed_arc_adjacent_endpoint (hdeg : HasTwoNeighbors Γ)
    (n : ℕ) (a : A)
    (hsing : ∀ (x : V) (p : BasedWalk Γ (n + 1) x), p.Nonbacktracking →
      (∀ y ∈ p.vertices, a • y = y) →
      (∀ z, Forward p z → a • z = z) ∧
      (∀ z, Backward p z → a • z = z))
    {x w : V} (p : BasedWalk Γ (n + 1) x) (hp : p.Nonbacktracking)
    (hfix : ∀ y ∈ p.vertices, a • y = y) (hw : Γ.Adj p.endpoint w) :
    ∃ z, ∃ q : BasedWalk Γ (n + 1) z,
      q.Nonbacktracking ∧ q.endpoint = w ∧ ∀ y ∈ q.vertices, a • y = y := by
  classical
  obtain ⟨hright, hleft⟩ := hsing x p hp hfix
  by_cases hback : w = p.penultimate
  · obtain ⟨z, hxz, hzne⟩ := hdeg x p.1
    let q : BasedWalk Γ (n + 1) z :=
      ⟨⟨x, hxz.symm⟩, p.take n (Nat.le_succ n)⟩
    refine ⟨z, q, ?_, ?_, ?_⟩
    · cases n with
      | zero => trivial
      | succ n =>
        exact ⟨hzne.symm, nonbacktracking_take (Nat.le_succ (n + 1)) p hp⟩
    · exact (endpoint_take_penultimate p).trans hback.symm
    · intro y hy
      change y ∈ z :: (p.take n (Nat.le_succ n)).vertices at hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hleft _ ⟨hxz, hzne⟩
      · apply hfix y
        rw [vertices_take] at hy
        exact List.mem_of_mem_take hy
  · have hforward : Forward p w := ⟨hw, hback⟩
    have hsnoc : (p.snoc hw).Nonbacktracking :=
      (forward_iff_snoc_nonbacktracking p hp hw).1 hforward
    refine ⟨((p.snoc hw).1 : V), (p.snoc hw).2,
      nonbacktracking_tail _ hsnoc, endpoint_snoc p hw, ?_⟩
    intro y hy
    have hy' : y ∈ (p.snoc hw).vertices := List.mem_cons_of_mem x hy
    rw [vertices_snoc, List.mem_append, List.mem_singleton] at hy'
    rcases hy' with hy' | rfl
    · exact hfix y hy'
    · exact hright _ hforward

/-- Total singularity at one positive length forces every corresponding
pointwise arc stabilizer into the global action kernel. -/
theorem smul_eq_of_all_totallySingular (hconn : Γ.Preconnected)
    (hdeg : HasTwoNeighbors Γ) {s : ℕ} (hs : 0 < s)
    (hsing : ∀ (x : V) (p : BasedWalk Γ s x), p.Nonbacktracking →
      ∀ a : A, (∀ y ∈ p.vertices, a • y = y) →
      (∀ z, Forward p z → a • z = z) ∧
      (∀ z, Backward p z → a • z = z))
    {x : V} (p : BasedWalk Γ s x) (hp : p.Nonbacktracking)
    (a : A) (hfix : ∀ y ∈ p.vertices, a • y = y) (y : V) : a • y = y := by
  cases s with
  | zero => omega
  | succ n =>
    let P (w : V) : Prop := ∃ z, ∃ q : BasedWalk Γ (n + 1) z,
      q.Nonbacktracking ∧ q.endpoint = w ∧ ∀ v ∈ q.vertices, a • v = v
    have hstep {v w : V} (hvw : Γ.Adj v w) : P v → P w := by
      rintro ⟨z, q, hq, rfl, hqfix⟩
      exact fixed_arc_adjacent_endpoint hdeg n a
        (fun z q hq hfix => hsing z q hq a hfix) q hq hqfix hvw
    have hwalk {v w : V} (q : Γ.Walk v w) : P v → P w := by
      induction q with
      | nil => exact id
      | cons hadj q ih => exact fun hv => ih (hstep hadj hv)
    obtain ⟨q⟩ := hconn p.endpoint y
    obtain ⟨z, r, _, hr, hrfixed⟩ := hwalk q ⟨x, p, hp, rfl, hfix⟩
    rw [← hr]
    apply hrfixed
    simpa only [support_toWalk] using r.toWalk.end_mem_support

/-- In a faithful connected action the totally singular arc fixers vanish. -/
theorem eq_one_of_all_totallySingular [FaithfulSMul A V]
    (hconn : Γ.Preconnected) (hdeg : HasTwoNeighbors Γ) {s : ℕ} (hs : 0 < s)
    (hsing : ∀ (x : V) (p : BasedWalk Γ s x), p.Nonbacktracking →
      ∀ a : A, (∀ y ∈ p.vertices, a • y = y) →
      (∀ z, Forward p z → a • z = z) ∧
      (∀ z, Backward p z → a • z = z))
    {x : V} (p : BasedWalk Γ s x) (hp : p.Nonbacktracking)
    (a : A) (hfix : ∀ y ∈ p.vertices, a • y = y) : a = 1 := by
  apply eq_of_smul_eq_smul (α := V)
  intro y
  rw [one_smul]
  exact smul_eq_of_all_totallySingular hconn hdeg hs hsing p hp a hfix y

end Theory.GroupAction.CubicTree
