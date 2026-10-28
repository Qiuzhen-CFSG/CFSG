module

public import CFSG.Quasithin.Chapter13.Section05.LocalSteps
public import Theory.GroupTheory.NormalizerActionControl

/-!
# The action-to-normalizer step in 13.5.5

In the six-letter case, the point-fixer action of L₁T on V₃ and the
centralizer bound C_G(V₃) ≤ M_V give the exact intersection
N_G(V₁) ∩ N_G(V₃) ≤ M_V. The order-two line is fixed pointwise.
Applying the existing conjugate-span argument then proves V₃ < U_H.
The five-letter branch instead uses N_G(V₃) ≤ M_V from 13.2.3(2).

The natural action calculation and the global centralizer bound are
explicit inputs here. They must be supplied from 13.2/13.3 and 13.5.4
in the full source assembly; this file does not assert those results.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
13.5.5 and 13.5.9, printed pp.916,918.
-/

public section
open Subgroup
namespace CFSG.Quasithin.Chapter13.Section05
variable {G : Type*} [Group G]

/-- The precise M_V bound from the natural point-fixer action of L₁T.
The target is N_M(V), not merely M or N_G(V). -/
theorem normalizer_intersection_le_MV_of_point_fixer_action
    (V V₁ V₃ L₁ T M : Subgroup G) (hcard : Nat.card V₁ = 2)
    (hlocal : L₁ ⊔ T ≤ M ⊓ normalizer (V : Set G))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (haction : ∀ a : MulAut V₃,
      (∀ v : V₃, v.val ∈ V₁ → a v = v) →
      ∃ p ∈ L₁ ⊔ T, ∀ v : V₃, (a v).val = p * v.val * p⁻¹) :
    normalizer (V₁ : Set G) ⊓ normalizer (V₃ : Set G) ≤
      M ⊓ normalizer (V : Set G) :=
  normalizer_intersection_le_of_point_fixer_action V₁ V₃ (L₁ ⊔ T)
    (M ⊓ normalizer (V : Set G)) hcard hlocal hcentral haction

/-- The literal H_z consumer of the point-fixer calculation: the inputs
of the existing 13.5.9 deduction are discharged by the preceding bound. -/
theorem seed_lt_UH_of_point_fixer_action
    (V V₁ V₃ L₁ T M H : Subgroup G) (hcard : Nat.card V₁ = 2)
    (hlocal : L₁ ⊔ T ≤ M ⊓ normalizer (V : Set G))
    (hcentral : centralizer (V₃ : Set G) ≤ M ⊓ normalizer (V : Set G))
    (haction : ∀ a : MulAut V₃,
      (∀ v : V₃, v.val ∈ V₁ → a v = v) →
      ∃ p ∈ L₁ ⊔ T, ∀ v : V₃, (a v).val = p * v.val * p⁻¹)
    (hH : H ∈ Section08.Source.Hz L₁ T (normalizer (V₁ : Set G)) M) :
    V₃ < Section08.Source.UH H V₃ :=
  seed_lt_UH_of_mem_Hz L₁ T V₁ V₃ M H hH
    ((normalizer_intersection_le_MV_of_point_fixer_action V V₁ V₃ L₁ T M
      hcard hlocal hcentral haction).trans inf_le_left)

end CFSG.Quasithin.Chapter13.Section05
end
