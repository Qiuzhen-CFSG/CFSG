/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.External.Huppert.IV.theorem_5_1.part_a
public import Submission.BenderSuzuki.External.Huppert.IV.theorem_5_1.part_b
public import Submission.BenderSuzuki.External.Huppert.IV.theorem_5_1.part_c

/-!
# Huppert IV.5.1 (Burnside)

Book-order entry file for Burnside IV.5.1.  The theorem is exposed through the
three source clauses (a)--(c).
-/

namespace BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u

/-- Huppert IV.5.1 (Burnside), full witness form. -/
public theorem huppert_IV_5_1_prime_power_witness_of_fields
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q) (M : Subgroup Q)
    (M_p : IsPGroup q M)
    (M_le_S : M ≤ (S : Subgroup Q))
    (S_le_normalizer_M : (S : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q))
    (M_le_T : M ≤ (T : Subgroup Q))
    (not_T_le_normalizer_M :
      ¬ (T : Subgroup Q) ≤ Subgroup.normalizer (M : Set Q)) :
    ∃ A : Subgroup Q,
      IsPGroup q A ∧
        ∃ r : ℕ,
          r.Prime ∧ r ≠ q ∧
            ∃ x : Q,
              IsPElement (p := r) x ∧
                x ∈ Subgroup.normalizer (A : Set Q) ∧
                  x ∉ Subgroup.centralizer (A : Set Q) :=
  huppert_IV_5_1_a_prime_power_witness_of_fields
    (Q := Q) (q := q) S T M M_p M_le_S S_le_normalizer_M M_le_T not_T_le_normalizer_M

end External
end BenderSuzuki
