module
public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic
/-!
# Overgroups meeting a normal subgroup of order ten

An order-two subgroup of a normal subgroup of order ten is either preserved
by an overgroup or that overgroup contains the whole normal subgroup. The
intersection has order two or ten. This is the subgroup calculation behind
the marked-five uniqueness argument of Aschbacher--Smith15.2.5.
-/
public section
open Subgroup
namespace Subgroup
variable {D : Type*} [Group D] [Finite D]
theorem contains_or_normalizes_of_normal_ten (K R A : Subgroup D) [K.Normal]
    (hK : Nat.card K = 10) (hR : Nat.card R = 2) (hRK : R ≤ K) (hRA : R ≤ A) :
    K ≤ A ∨ A ≤ normalizer (R : Set D) := by
  have hRI : R ≤ A ⊓ K := le_inf hRA hRK
  have hdiv : Nat.card (A ⊓ K : Subgroup D) ∣ 10 := hK ▸ card_dvd_of_le inf_le_right
  have htwo : 2 ∣ Nat.card (A ⊓ K : Subgroup D) := hR ▸ card_dvd_of_le hRI
  have hc : Nat.card (A ⊓ K : Subgroup D) = 2 ∨ Nat.card (A ⊓ K : Subgroup D) = 10 := by
    have hm := Nat.mem_divisors.mpr ⟨hdiv,(by decide : 10 ≠ 0)⟩
    rw [show Nat.divisors 10 = {1,2,5,10} by decide] at hm
    simp only [Finset.mem_insert,Finset.mem_singleton] at hm
    rcases hm with h | h | h | h
    · rw [h] at htwo
      norm_num at htwo
    · exact Or.inl h
    · rw [h] at htwo
      norm_num at htwo
    · exact Or.inr h
  rcases hc with hc | hc
  · right
    have he : R = A ⊓ K := eq_of_le_of_card_ge hRI (by rw [hc,hR])
    rw [he]
    exact (le_inf A.le_normalizer le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  · left
    have he : A ⊓ K = K := eq_of_le_of_card_ge inf_le_right (by rw [hc,hK])
    exact he ▸ (show A ⊓ K ≤ A from inf_le_left)
end Subgroup
