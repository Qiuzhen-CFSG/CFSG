module
public import Theory.GroupAction.CubicTree.ArcTransport

/-!
# Endpoint regularity under equivariant graph isomorphisms

An equivariant graph isomorphism identifies the pointwise path stabilizers
and their forward extension actions. Hence it preserves right regularity.
The proof transports the literal vertex lists and the forward neighbors.
Application: reversing the source vertex classes in Goldschmidt (1980),
(2.12) and the setup of Sections 5--6.
-/

@[expose] public section
namespace Theory.GroupAction.CubicTree
open SimpleGraph SimpleGraph.BasedWalk
variable {V W A : Type*} [Group A] [MulAction A V] [MulAction A W]
variable {Γ : SimpleGraph V} {Δ : SimpleGraph W}

private theorem penultimate_graphIso (e : Γ ≃g Δ) {n : ℕ} {v : V}
    (p : BasedWalk Γ (n+1) v) : (p.map e.toHom).penultimate = e p.penultimate := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih => exact ih p.2

private theorem forward_graphIso (e : Γ ≃g Δ) {n : ℕ} {v w : V}
    (p : BasedWalk Γ n v) : Forward (p.map e.toHom) (e w) ↔ Forward p w := by
  cases n with
  | zero => exact e.map_rel_iff
  | succ n =>
    simp only [Forward, BasedWalk.endpoint_map, penultimate_graphIso]
    exact and_congr e.map_rel_iff (not_congr e.injective.eq_iff)

/-- An equivariant graph isomorphism preserves right arc regularity. -/
theorem rightRegular_graphIso_iff (e : Γ ≃g Δ)
    (he : ∀ (a : A) (v : V), e (a • v) = a • e v)
    {n : ℕ} {v : V} (p : BasedWalk Γ n v) :
    RightRegular (A := A) (p.map e.toHom) ↔ RightRegular (A := A) p := by
  constructor
  · intro h z w hz hw
    obtain ⟨a,ha,haw⟩ := h (e z) (e w) ((forward_graphIso e p).2 hz)
      ((forward_graphIso e p).2 hw)
    refine ⟨a,?_,e.injective (by rw [he]; exact haw)⟩
    intro y hy
    apply e.injective
    rw [he]
    exact ha (e y) (by rw [BasedWalk.vertices_map]; exact List.mem_map.mpr ⟨y,hy,rfl⟩)
  · intro h z w hz hw
    obtain ⟨z,rfl⟩ := e.surjective z
    obtain ⟨w,rfl⟩ := e.surjective w
    obtain ⟨a,ha,haw⟩ := h z w ((forward_graphIso e p).1 hz)
      ((forward_graphIso e p).1 hw)
    refine ⟨a,?_,by rw [← he,haw]⟩
    intro y hy
    rw [BasedWalk.vertices_map] at hy
    obtain ⟨y,hyp,rfl⟩ := List.mem_map.mp hy
    change a • e y = e y
    rw [← he,ha y hyp]

end Theory.GroupAction.CubicTree
