/-
Authors: OpenAI
-/

module

public import BenderSuzuki.PFchapter4section2.Basic

namespace BenderSuzuki
namespace PFchapter4section2

/-! # Peterfalvi, Part II, Chapter IV, Section 2, Claim (12)(b) -/

public theorem claim_12_b
    (E : Type*) [Field E] (m n q : ℕ) (zeta alpha beta : E)
    (theta sigma tau frob : E → E) (baseField : Set E) (u v d : ℕ → E)
    (hcoord_zeta_ne_one : zeta ≠ 1) (hcoord_beta_ne_zero : beta ≠ 0)
    (hcoord_recurrence_u : ∀ i : ℕ, u i ≠ alpha → u (i + 1) = (alpha + u i)⁻¹)
    (hcoord_recurrence_v : ∀ i : ℕ, u i ≠ alpha →
      v (i + 1) = v i + u (i + 1) * (d i * sigma (d i))⁻¹)
    (hcoord_recurrence_d : ∀ i : ℕ, u i ≠ alpha →
      d (i + 1) = d i * zeta * tau ((u (i + 1))⁻¹ ^ 2))
    (hcoord_beta_characteristic_root : beta ^ 2 + alpha * beta + 1 = 0)
    (hfrob_fixed_field : ∀ x : E, x ∈ baseField ↔ frob x = x)
    (hfrob_q_power : ∀ x : E, frob x = x ^ q)
    (hfrob_preserves_characteristic_root :
      ∀ x : E, x ^ 2 + alpha * x + 1 = 0 →
        (frob x) ^ 2 + alpha * (frob x) + 1 = 0)
    (hcharacteristic_roots :
      ∀ x : E, x ^ 2 + alpha * x + 1 = 0 → x = beta ∨ x = beta⁻¹) :
    beta ∉ baseField → beta⁻¹ = frob beta := by
  have _ := m
  have _ := n
  have _ := theta
  have _ := hcoord_zeta_ne_one
  have _ := hcoord_beta_ne_zero
  have _ := hcoord_recurrence_u
  have _ := hcoord_recurrence_v
  have _ := hcoord_recurrence_d
  intro hbeta_not_mem
  have _ := hfrob_q_power
  have hfrob_root :
      (frob beta) ^ 2 + alpha * (frob beta) + 1 = 0 :=
    hfrob_preserves_characteristic_root beta hcoord_beta_characteristic_root
  have hnot_fixed : frob beta ≠ beta := by
    intro hfixed
    exact hbeta_not_mem ((hfrob_fixed_field beta).2 hfixed)
  rcases hcharacteristic_roots (frob beta) hfrob_root with hfixed | hinv
  · exact (hnot_fixed hfixed).elim
  · exact hinv.symm

end PFchapter4section2
end BenderSuzuki


