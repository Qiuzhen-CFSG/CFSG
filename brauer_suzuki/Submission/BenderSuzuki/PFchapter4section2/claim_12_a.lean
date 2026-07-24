/-
Authors: OpenAI
-/

module

public import Submission.BenderSuzuki.PFchapter4section2.Basic

namespace BenderSuzuki
namespace PFchapter4section2

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (12)(a) -/

public theorem claim_12_a
    (E : Type*) [Field E] [CharP E 2] (m n : ℕ) (zeta alpha beta : E)
    (theta sigma tau : E → E) (u v d : ℕ → E)
    (hcoord_zeta_ne_one : zeta ≠ 1) (hcoord_beta_ne_zero : beta ≠ 0)
    (hcoord_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hcoord_recurrence_v : ∀ i : ℕ, u i ≠ alpha →
      v (i + 1) = v i + u (i + 1) * (d i * sigma (d i))⁻¹)
    (hcoord_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hcoord_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0) :
    beta + beta⁻¹ = alpha := by
  have _ := m
  have _ := n
  have _ := theta
  have _ := hcoord_zeta_ne_one
  have _ := hcoord_recurrence_u
  have _ := hcoord_recurrence_v
  have _ := hcoord_recurrence_d
  exact
    (alpha_eq_beta_add_inv_of_characteristic_root
      hcoord_beta_ne_zero hcoord_beta_characteristic_root).symm

end PFchapter4section2
end BenderSuzuki
