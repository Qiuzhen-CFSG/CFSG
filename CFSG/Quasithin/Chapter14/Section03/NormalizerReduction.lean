module

public import Theory.GroupTheory.PermutingConjugateClosure

/-!
# The normalizer reduction in §14.3

Aschbacher–Smith, *The Classification of Quasithin Groups*, §14.3,
Lemma 14.3.8 (combined manuscript, 1 March 2004, printed p. 992).

Starting with `H ≤ N(V₁)`, the two generation identities
`V₂ = ⟨V₁^L₂⟩` and `V = ⟨V₂^L₁⟩` propagate normalization to `V₂` and then
to `V`. The normalizer containment `N(V) ≤ M` finishes the argument.
The generation identities are explicit inputs here; their specialization to
the natural module belongs to the chapter setup.
-/

open scoped Pointwise
open Subgroup

namespace CFSG.Quasithin.Chapter14

variable {G : Type*} [Group G]

/-- The normalizer argument of Lemma 14.3.8, with the natural-module
generation identities supplied explicitly. No finiteness is needed for this
group-theoretic implication. -/
public theorem lemma_14_3_8_of_generation
    (H L₁ L₂ V₁ V₂ V M : Subgroup G)
    (hH : H ≤ normalizer (V₁ : Set G))
    (hL₁ : (H : Set G) * (L₁ : Set G) = (L₁ : Set G) * (H : Set G))
    (hL₂ : (H : Set G) * (L₂ : Set G) = (L₂ : Set G) * (H : Set G))
    (hV₂ : V₂ = closure {x : G | ∃ l : L₂, ∃ v : V₁,
      x = (l : G) * (v : G) * (l : G)⁻¹})
    (hV : V = closure {x : G | ∃ l : L₁, ∃ v : V₂,
      x = (l : G) * (v : G) * (l : G)⁻¹})
    (hM : normalizer (V : Set G) ≤ M) : H ≤ M := by
  have hH₂ : H ≤ normalizer (V₂ : Set G) := by
    rw [hV₂]
    exact le_normalizer_conjugate_closure_of_mul_subset H L₂ V₁ hH hL₂.le
  apply le_trans _ hM
  rw [hV]
  exact le_normalizer_conjugate_closure_of_mul_subset H L₁ V₂ hH₂ hL₁.le

end CFSG.Quasithin.Chapter14
