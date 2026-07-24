/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.External.Huppert.IV.theorem_5_2

/-!
# Huppert IV.5.3

Book-order entry file for the non-`p`-normal witness extracted from IV.5.1 and
IV.5.2.
-/

namespace BenderSuzuki
namespace External

universe u

/-- Huppert IV.5.3, non-`p`-normal witness form. -/
public theorem huppert_IV_5_3_witness_of_not_pNormal
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S : Sylow q Q) (hnot_pnormal : ¬ ∀ T : Sylow q Q, centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q) → centerIn (G := Q) (S : Subgroup Q) = centerIn (G := Q) (T : Subgroup Q)) :
    ∃ A : Subgroup Q,
      IsPGroup q A ∧
        ∃ r : ℕ,
          r.Prime ∧ r ≠ q ∧
            ∃ x : Q,
              IsPElement (p := r) x ∧
                x ∈ Subgroup.normalizer (A : Set Q) ∧
                  x ∉ Subgroup.centralizer (A : Set Q) :=
  hkt_huppert_iv53_witness_of_not_pNormal (Q := Q) (q := q) S hnot_pnormal

end External
end BenderSuzuki
