module
public import Mathlib.GroupTheory.Perm.Centralizer
public import Mathlib.Tactic

/-!
# Cubic-plane obstructions in seven and eight point involution centralizers

The cycle-type centralizer formula gives orders 240 and 48 in S₇,
and 1440, 192, 96 and 384 in S₈. None of the former orders is divisible
by nine; none of the latter is divisible by both nine and 64. This
excludes a faithful E₉ centralizing the original Sylow-central involution
in the A₇ and A₈ rows of Aschbacher--Smith, proof of 12.6.26, p.832.

Only the permutation calculation is asserted here. The chapter consumer
constructs the action through the actual component central quotient and
supplies its original Sylow-centrality.
-/

public section
open Subgroup Equiv.Perm
namespace alternatingGroup

/-- Involutions in S₇ have centralizers of order indivisible by nine. -/
theorem seven_not_nine_dvd_involution_centralizer
    (x : Equiv.Perm (Fin 7)) (hx : orderOf x = 2) :
    ¬ 9 ∣ Nat.card (centralizer ({x} : Set (Equiv.Perm (Fin 7)))) := by
  obtain ⟨k,hk⟩ := cycleType_prime_order (hx ▸ Nat.prime_two)
  rw [hx] at hk
  have hb := x.sum_cycleType_le
  rw [hk,Multiset.sum_replicate] at hb
  simp only [nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] at hb
  have hkb : k ≤ 2 := by omega
  rw [nat_card_centralizer,hk]
  interval_cases k <;> norm_num [Nat.factorial]

/-- A centralizer in S₈ cannot contain both an E₉ and a group of order 64. -/
theorem eight_not_nine_and_sixtyFour_dvd_involution_centralizer
    (x : Equiv.Perm (Fin 8)) (hx : orderOf x = 2)
    (hnine : 9 ∣ Nat.card (centralizer ({x} : Set (Equiv.Perm (Fin 8))))) :
    ¬ 64 ∣ Nat.card (centralizer ({x} : Set (Equiv.Perm (Fin 8)))) := by
  obtain ⟨k,hk⟩ := cycleType_prime_order (hx ▸ Nat.prime_two)
  rw [hx] at hk
  have hb := x.sum_cycleType_le
  rw [hk,Multiset.sum_replicate] at hb
  simp only [nsmul_eq_mul,Nat.cast_id,Fintype.card_fin] at hb
  have hkb : k ≤ 3 := by omega
  rw [nat_card_centralizer,hk] at hnine ⊢
  interval_cases k <;> norm_num [Nat.factorial] at *

end alternatingGroup
