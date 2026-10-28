module

public import Theory.Representation.AlternatingSevenConjugatePair.ElementaryGeometry

/-!
# The two four-groups in the standard alternating Sylow subgroup

The even parts of the two elementary groups of order eight are the only
rank-two elementary groups in the standard Sylow subgroup of A₇. They share
(01)(23), but the indicated generators from the two groups do not commute.
The regular four-group is centralized by (456). These explicit permutations
supply the fixed-space argument, without an assumed subgroup-family label.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004, H.8,
printed p.389/PDF p.400.
-/

@[expose] public section
open Equiv Subgroup
open Representation.BinaryOffender
namespace Representation.AlternatingSevenConjugatePair.FixedFamily
open ElementaryGeometry
local instance (g : S7) : Decidable (g ∈ alternatingGroup (Fin 7)) :=
  inferInstanceAs (Decidable (Perm.sign g = 1))

abbrev pairFour : Subgroup S7 := pairElementary ⊓ alternatingGroup (Fin 7)
abbrev regularFour : Subgroup S7 := fourTwoElementary ⊓ alternatingGroup (Fin 7)
local instance (g : S7) : Decidable (g ∈ pairFour) :=
  inferInstanceAs (Decidable (g ∈ pairElementary ∧ g ∈ alternatingGroup (Fin 7)))
local instance (g : S7) : Decidable (g ∈ regularFour) :=
  inferInstanceAs (Decidable (g ∈ fourTwoElementary ∧ g ∈ alternatingGroup (Fin 7)))
def centralInvolution : S7 := swap01 * swap23
def pairInvolution : S7 := swap01 * swap45
def cubic : S7 := swap (4 : Fin 7) 5 * swap 5 6

theorem pairFour_elementary : IsElementaryTwo pairFour := by
  apply pairElementary_isElementaryTwo.of_le inf_le_left
  intro h
  have hc := pairElementary_even_card
  rw [h, Subgroup.card_bot] at hc
  omega

theorem regularFour_elementary : IsElementaryTwo regularFour := by
  apply fourTwoElementary_isElementaryTwo.of_le inf_le_left
  intro h
  have hc := fourTwoElementary_even_card
  rw [h, Subgroup.card_bot] at hc
  omega

theorem pairFour_rank : rank pairFour = 2 := by
  rw [rank, pairElementary_even_card]; decide

theorem regularFour_rank : rank regularFour = 2 := by
  rw [rank, fourTwoElementary_even_card]; decide

theorem four_group_coverage (A : Subgroup S7) (hA : IsElementaryTwo A)
    (hAT : A ≤ sylowTwo) (hAL : A ≤ alternatingGroup (Fin 7)) (hr : rank A = 2) :
    A = pairFour ∨ A = regularFour := by
  have hc : Nat.card A = 4 := by
    rw [hA.card_eq_two_pow_rank, hr]
    decide
  rcases elementary_le_representative hA.2 hAT with hp | hf
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge (le_inf hp hAL) (by
      rw [hc, pairElementary_even_card]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge (le_inf hf hAL) (by
      rw [hc, fourTwoElementary_even_card]))

theorem centralInvolution_mem : centralInvolution ∈ pairFour ∧
    centralInvolution ∈ regularFour := by decide +kernel
theorem centralInvolution_order : orderOf centralInvolution = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)
theorem pairInvolution_mem : pairInvolution ∈ pairFour := by decide +kernel
theorem pairInvolution_order : orderOf pairInvolution = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)
theorem crossSwap_mem_regularFour : crossSwap ∈ regularFour := by decide +kernel
theorem crossSwap_order : orderOf crossSwap = 2 :=
  orderOf_eq_prime (by decide +kernel) (by decide +kernel)
theorem pair_cross_noncommute : pairInvolution * crossSwap ≠ crossSwap * pairInvolution :=
  by decide +kernel
theorem cubic_even : cubic ∈ alternatingGroup (Fin 7) := by decide +kernel
theorem cubic_cube : cubic ^ 3 = 1 := by decide +kernel
theorem cubic_ne_one : cubic ≠ 1 := by decide +kernel

theorem regularFour_commutes_cubic : ∀ a ∈ regularFour, a * cubic = cubic * a := by
  rintro _ ⟨⟨v, rfl⟩, hv⟩
  exact (by decide +kernel : ∀ v : Triple, secondWord v ∈ alternatingGroup (Fin 7) →
    secondWord v * cubic = cubic * secondWord v) v hv

end Representation.AlternatingSevenConjugatePair.FixedFamily
