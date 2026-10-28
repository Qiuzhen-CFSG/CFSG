module

public import Mathlib.GroupTheory.SemidirectProduct

/-!
# Homomorphisms from a product of two group images

Compatible homomorphisms on factors glue when they agree on their overlap.
The proof descends the semidirect-product lift through its surjective map to
the ambient group. This is the elementary gluing argument used in
Aschbacher–Smith, *The Classification of Quasithin Groups*, F.2.11.
-/

public section

namespace Theory.GroupTheory
variable {A N B H : Type*} [Group A] [Group N] [Group B] [Group H]

/-- Compatible maps on two factors descend from their semidirect product when
all ambiguity in the factorization lies in their common image. -/
theorem exists_hom_of_factorization
    (φ : A →* MulAut N) (i : A →* B) (j : N →* B)
    (f : A →* H) (g : N →* H)
    (hi : ∀ a n, j (φ a n) = i a * j n * (i a)⁻¹)
    (hf : ∀ a n, g (φ a n) = f a * g n * (f a)⁻¹)
    (hoverlap : ∀ a n, i a = j n → f a = g n)
    (hfactor : ∀ b, ∃ a n, i a * j n = b) :
    ∃ F : B →* H, (∀ a, F (i a) = f a) ∧ (∀ n, F (j n) = g n) := by
  let p : N ⋊[φ] A →* B := SemidirectProduct.lift j i (fun a => by
    ext n
    exact hi a n)
  let q : N ⋊[φ] A →* H := SemidirectProduct.lift g f (fun a => by
    ext n
    exact hf a n)
  have hp : Function.Surjective p := by
    intro b
    obtain ⟨a, n, rfl⟩ := hfactor b
    exact ⟨SemidirectProduct.inr a * SemidirectProduct.inl n, by simp [p]⟩
  have hk : p.ker ≤ q.ker := by
    intro z hz
    change j z.left * i z.right = 1 at hz
    change g z.left * f z.right = 1
    have he : i (z.right⁻¹) = j z.left := by
      rw [map_inv]
      exact (eq_inv_of_mul_eq_one_left hz).symm
    rw [← hoverlap _ _ he, map_inv, inv_mul_cancel]
  let F := p.liftOfSurjective hp ⟨q, hk⟩
  have hF (z) : F (p z) = q z :=
    p.liftOfRightInverse_comp_apply _ _ _ z
  refine ⟨F, ?_, ?_⟩
  · intro a
    simpa [p, q] using hF (SemidirectProduct.inr a)
  · intro n
    simpa [p, q] using hF (SemidirectProduct.inl n)
end Theory.GroupTheory
