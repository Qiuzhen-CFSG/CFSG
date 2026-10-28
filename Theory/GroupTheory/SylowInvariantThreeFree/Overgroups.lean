module
public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Sylow

/-!
# From three-free Sylow overgroups to normalized subgroups

If every overgroup of a full Sylow two-subgroup S with order prime to
three is S itself, every three-free subgroup normalized by S lies in S.
The normalized product has order dividing the product of the factor
orders. This provides the finite-group step of the binary linear model
calculation used in Aschbacher--Smith 8.3.8, printed p.725.
-/

public section
open Subgroup
namespace Theory.GroupTheory
variable {G : Type*} [Group G] [Finite G]

/-- The absence of proper three-free Sylow overgroups controls every
three-free subgroup normalized by that same Sylow subgroup. -/
theorem isPGroup_of_three_free_sylow_overgroups
    (S : Sylow 2 G) (V : Subgroup G)
    (hnorm : (S : Subgroup G) ≤ normalizer (V : Set G))
    (hthree : ¬ 3 ∣ Nat.card V)
    (hmodel : ∀ H : Subgroup G, (S : Subgroup G) ≤ H →
      ¬ 3 ∣ Nat.card H → H = (S : Subgroup G)) : IsPGroup 2 V := by
  have hSthree : ¬ 3 ∣ Nat.card S := by
    obtain ⟨n, hn⟩ := S.isPGroup'.exists_card_eq
    rw [hn]
    intro hd
    exact (by decide : ¬ 3 ∣ 2) (Nat.prime_three.dvd_of_dvd_pow hd)
  have hjoin : ¬ 3 ∣ Nat.card (V ⊔ (S : Subgroup G) : Subgroup G) := by
    intro hd
    have hprod := card_mul_eq_card_inf_mul_card_sup_of_normalizes V
      (S : Subgroup G) hnorm
    have hdprod : 3 ∣ Nat.card V * Nat.card S := by
      rw [hprod]
      exact dvd_mul_of_dvd_right hd _
    exact (Nat.prime_three.dvd_mul.mp hdprod).elim hthree hSthree
  have he := hmodel (V ⊔ (S : Subgroup G)) le_sup_right hjoin
  exact S.isPGroup'.to_le (he ▸ le_sup_left)

end Theory.GroupTheory
