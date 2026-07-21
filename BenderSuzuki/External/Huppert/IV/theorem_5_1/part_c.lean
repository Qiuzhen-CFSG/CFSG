/-
Authors: OpenAI
-/

module

public import BenderSuzuki.External.Huppert.IV.theorem_5_1.part_b

/-!
# Huppert IV.5.1(c)

The Burnside witness element normalizes, but does not centralize, the chosen
`q`-subgroup.
-/

namespace BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u

/-- Huppert IV.5.1(c): the prime-power element normalizes but does not centralize
its witness `q`-subgroup. -/
public theorem huppert_IV_5_1_c_witness_normalizes_not_centralizes
    {Q : Type u} [Group Q] {q r : ℕ} (A : Subgroup Q) (x : Q)
    (hr : r.Prime) (hr_ne_q : r ≠ q)
    (x_p : IsPElement (p := r) x)
    (x_norm : x ∈ Subgroup.normalizer (A : Set Q))
    (x_not_cent : x ∉ Subgroup.centralizer (A : Set Q)) :
    r.Prime ∧ r ≠ q ∧ IsPElement (p := r) x ∧
      x ∈ Subgroup.normalizer (A : Set Q) ∧
        x ∉ Subgroup.centralizer (A : Set Q) :=
  ⟨hr, hr_ne_q, x_p, x_norm, x_not_cent⟩

end External
end BenderSuzuki