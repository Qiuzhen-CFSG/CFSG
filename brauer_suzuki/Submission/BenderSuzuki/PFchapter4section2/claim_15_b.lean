/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.PFchapter4section2.Basic

namespace BenderSuzuki
namespace PFchapter4section2

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (15)(b) -/

public theorem claim_15_b
    (E : Type*) [Field E] (m : ℕ) (zeta alpha beta : E)
    (tau : E → E) (u d : ℕ → E)
    (_sigma : E → E) (_hseq_zeta_ne_one : zeta ≠ 1) (_hseq_alpha_ne_zero : alpha ≠ 0)
    (_hseq_beta_ne_zero : beta ≠ 0) (_hseq_tau_nonzero : ∀ x : E, x ≠ 0 → tau x ≠ 0)
    (hseq_zeta_order : orderOf zeta = m)
    (_hseq_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (_hseq_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (_hseq_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hseq_terminal_stop : ∃ r : ℕ, 1 ≤ r ∧ r ≤ m - 1 ∧ u r = alpha)
    (hseq_terminal_order : ∀ r : ℕ, 1 ≤ r → r ≤ m - 1 → u r = alpha →
      alpha = beta ^ r + (beta⁻¹) ^ r ∧ zeta ^ (r + 1) = 1) :
    u (m - 1) = alpha ∧ alpha = beta ^ (m - 1) + (beta⁻¹) ^ (m - 1) := by
  rcases hseq_terminal_stop with ⟨r, hr_one, hr_le, hur⟩
  rcases hseq_terminal_order r hr_one hr_le hur with
    ⟨halpha_sum, hzeta_pow⟩
  have hdiv : m ∣ r + 1 := by
    rw [← hseq_zeta_order, orderOf_dvd_iff_pow_eq_one]
    exact hzeta_pow
  have hm_le : m ≤ r + 1 :=
    Nat.le_of_dvd (by omega) hdiv
  have hr_succ_le : r + 1 ≤ m := by
    omega
  have hr_eq : r = m - 1 := by
    omega
  constructor
  · simpa [hr_eq] using hur
  · simpa [hr_eq] using halpha_sum

end PFchapter4section2
end BenderSuzuki
