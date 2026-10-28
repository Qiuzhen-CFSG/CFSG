module

public import Theory.GroupAction.CubicTree.ArcReversal

/-!
# Transporting endpoint regularity

Regularity is invariant under the literal graph action and under equality of
ordered vertex lists. This connects the transitivity assertion in Goldschmidt
(2.12) to its propagation of singularity between the two vertex orbits.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
open SimpleGraph SimpleGraph.BasedWalk SimpleGraph.PathTransitivePolygon
universe u v
variable {V : Type u} {A : Type v} {Γ : SimpleGraph V}
variable [Group A] [MulAction A V]

theorem backward_map_iff (h : GraphAction Γ A) (a : A)
    {n : ℕ} {x z : V} (p : BasedWalk Γ n x) :
    Backward (p.map (h.hom a)) (a • z) ↔ Backward p z := by
  cases n with
  | zero => exact h.adj_iff a
  | succ n =>
    change (Γ.Adj (a • x) (a • z) ∧ a • z ≠ a • (p.1 : V)) ↔ _
    exact and_congr (h.adj_iff a) (not_congr (MulAction.toPerm a).injective.eq_iff)

private theorem transport_transitive (a : A) (L : List V) (D E : V → Prop)
    (hD : ∀ z, E z ↔ D (a⁻¹ • z))
    (ht : ∀ z w, D z → D w → ∃ b : A, (∀ y ∈ L, b • y = y) ∧ b • z = w) :
    ∀ z w, E z → E w →
      ∃ b : A, (∀ y ∈ L.map (a • ·), b • y = y) ∧ b • z = w := by
  intro z w hz hw
  obtain ⟨b, hb, he⟩ := ht (a⁻¹ • z) (a⁻¹ • w) ((hD z).1 hz) ((hD w).1 hw)
  refine ⟨a * b * a⁻¹, ?_, ?_⟩
  · intro y hy
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hy
    simp only [mul_smul, inv_smul_smul, hb t ht]
  · simpa only [mul_smul, smul_inv_smul] using congrArg (a • ·) he

theorem rightRegular_map (h : GraphAction Γ A) (a : A)
    {n : ℕ} {x : V} (p : BasedWalk Γ n x) (hp : RightRegular (A := A) p) :
    RightRegular (A := A) (p.map (h.hom a)) := by
  have he : ∀ z, Forward (p.map (h.hom a)) z ↔ Forward p (a⁻¹ • z) := by
    intro z
    simpa only [smul_inv_smul] using forward_map_iff h a (z := a⁻¹ • z) p
  unfold RightRegular
  rw [BasedWalk.vertices_map]
  exact transport_transitive a p.vertices _ _ he hp

theorem leftRegular_map (h : GraphAction Γ A) (a : A)
    {n : ℕ} {x : V} (p : BasedWalk Γ n x) (hp : LeftRegular (A := A) p) :
    LeftRegular (A := A) (p.map (h.hom a)) := by
  have he : ∀ z, Backward (p.map (h.hom a)) z ↔ Backward p (a⁻¹ • z) := by
    intro z
    simpa only [smul_inv_smul] using backward_map_iff h a (z := a⁻¹ • z) p
  unfold LeftRegular
  rw [BasedWalk.vertices_map]
  exact transport_transitive a p.vertices _ _ he hp

theorem rightRegular_of_vertices_eq {n : ℕ} {x y : V}
    (p : BasedWalk Γ n x) (q : BasedWalk Γ n y) (he : p.vertices = q.vertices)
    (hp : RightRegular (A := A) p) : RightRegular (A := A) q := by
  have hxy : x = y := Option.some.inj (by
    simpa only [BasedWalk.head_vertices] using congrArg List.head? he)
  subst y
  exact (BasedWalk.vertices_injective n x he) ▸ hp

theorem leftRegular_of_vertices_eq {n : ℕ} {x y : V}
    (p : BasedWalk Γ n x) (q : BasedWalk Γ n y) (he : p.vertices = q.vertices)
    (hp : LeftRegular (A := A) p) : LeftRegular (A := A) q := by
  have hxy : x = y := Option.some.inj (by
    simpa only [BasedWalk.head_vertices] using congrArg List.head? he)
  subst y
  exact (BasedWalk.vertices_injective n x he) ▸ hp

theorem rightRegular_of_conjugate (h : GraphAction Γ A)
    {n : ℕ} {x y : V} (p : BasedWalk Γ n x) (q : BasedWalk Γ n y)
    (a : A) (he : p.vertices.map (a • ·) = q.vertices)
    (hp : RightRegular (A := A) p) : RightRegular (A := A) q :=
  rightRegular_of_vertices_eq (p.map (h.hom a)) q
    ((BasedWalk.vertices_map _ _).trans he) (rightRegular_map h a p hp)

theorem leftRegular_of_conjugate (h : GraphAction Γ A)
    {n : ℕ} {x y : V} (p : BasedWalk Γ n x) (q : BasedWalk Γ n y)
    (a : A) (he : p.vertices.map (a • ·) = q.vertices)
    (hp : LeftRegular (A := A) p) : LeftRegular (A := A) q :=
  leftRegular_of_vertices_eq (p.map (h.hom a)) q
    ((BasedWalk.vertices_map _ _).trans he) (leftRegular_map h a p hp)

/-- Left regularity of an arc implies left regularity of every nonempty prefix. -/
theorem leftRegular_take {n k : ℕ} {x : V} (p : BasedWalk Γ n x)
    (hk : 0 < k) (hkn : k ≤ n) (hp : LeftRegular (A := A) p) :
    LeftRegular (A := A) (p.take k hkn) := by
  intro z w hz hw
  have he : ∀ t, Backward (p.take k hkn) t ↔ Backward p t := by
    intro t
    cases k with
    | zero => omega
    | succ k =>
      cases n with
      | zero => omega
      | succ n => rfl
  obtain ⟨a, ha, heq⟩ := hp z w ((he z).1 hz) ((he w).1 hw)
  refine ⟨a, ?_, heq⟩
  intro y hy
  apply ha y
  rw [BasedWalk.vertices_take] at hy
  exact List.mem_of_mem_take hy

end Theory.GroupAction.CubicTree
