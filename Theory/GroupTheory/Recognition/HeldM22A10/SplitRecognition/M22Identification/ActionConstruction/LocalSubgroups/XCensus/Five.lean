module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic

/-!
# Small alternating-quotient facts for the X census

The kernel checks the power tests on the sixty actual even permutations.
They give the counts 15, 20 and 24 for orders two, three and five and show
that each involution inverts a five-element. The latter allows the existing
fixed-space theorem to be applied to the actual F action, without selecting
an unrelated four-dimensional permutation module.

Source: the A5 quotient in Janko (1968), Section 8, Lemma 17, pp.16--17.
-/

namespace Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups.XCensus
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

public theorem a5_orders (a : alternatingGroup (Fin 5)) :
    orderOf a = 1 ∨ orderOf a = 2 ∨ orderOf a = 3 ∨ orderOf a = 5 := by
  have h : ∀ a : alternatingGroup (Fin 5),
      a = 1 ∨ (a ^ 2 = 1 ∧ a ≠ 1) ∨ (a ^ 3 = 1 ∧ a ≠ 1) ∨
        (a ^ 5 = 1 ∧ a ≠ 1) := by decide +kernel
  simpa only [orderOf_eq_one_iff, orderOf_eq_prime_iff] using h a

public theorem a5_count_two : Nat.card {a : alternatingGroup (Fin 5) // orderOf a = 2} = 15 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ => orderOf_eq_prime_iff)),
    Nat.card_eq_fintype_card]
  decide +kernel
public theorem a5_count_three : Nat.card {a : alternatingGroup (Fin 5) // orderOf a = 3} = 20 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ => orderOf_eq_prime_iff)),
    Nat.card_eq_fintype_card]
  decide +kernel
public theorem a5_count_five : Nat.card {a : alternatingGroup (Fin 5) // orderOf a = 5} = 24 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun _ => orderOf_eq_prime_iff)),
    Nat.card_eq_fintype_card]
  decide +kernel
public theorem a5_involution_inverts_five (a : alternatingGroup (Fin 5)) (ha : orderOf a = 2) :
    ∃ b : alternatingGroup (Fin 5), orderOf b = 5 ∧ a * b * a⁻¹ = b⁻¹ := by
  have h : ∀ a : alternatingGroup (Fin 5), a ^ 2 = 1 → a ≠ 1 →
      ∃ b : alternatingGroup (Fin 5), b ^ 5 = 1 ∧ b ≠ 1 ∧ a * b * a⁻¹ = b⁻¹ := by
    decide +kernel
  obtain ⟨b, hb, hb1, hab⟩ := h a (orderOf_eq_prime_iff.mp ha).1
    (orderOf_eq_prime_iff.mp ha).2
  exact ⟨b, orderOf_eq_prime hb hb1, hab⟩
end Theory.GroupTheory.HeldM22A10.M22Identification.ActionConstruction.LocalSubgroups.XCensus
