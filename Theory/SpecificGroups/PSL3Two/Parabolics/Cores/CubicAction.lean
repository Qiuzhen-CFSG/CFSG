module

public import Theory.SpecificGroups.PSL3Two.Parabolics.Cores.ModelAction
import Mathlib.Tactic
/-!
# Cubic irreducibility of the symmetric-four core

A cubic permutation centralizes no nonidentity involution in S₄. Thus a
subgroup of its four-core preserved by that cubic cannot have order two;
Lagrange's theorem leaves only the trivial subgroup and the full core.
The result transports through any actual S₄ isomorphism.

Source application: Aschbacher–Smith, J.2.4(1), printed p.434 (PDF p.445).
-/

open Subgroup
set_option maxRecDepth 10000 in
private theorem cubic_moves_involution :
    ∀ c x : Equiv.Perm (Fin 4), c ^ 3 = 1 → c ≠ 1 →
      x ^ 2 = 1 → x ≠ 1 → c * x * c⁻¹ ≠ x := by
  decide +kernel

namespace Matrix.PSL3Two.ParabolicCoreModel
variable {G : Type*} [Group G] [Finite G]
/-- A subgroup of the four-core invariant under a cubic is trivial or the full core. -/
public theorem cubic_invariant_core (e : G ≃* Equiv.Perm (Fin 4))
    (c : G) (hc : orderOf c = 3) (N : Subgroup G)
    (hN : N ≤ pCore 2 G) (hn : c ∈ normalizer (N : Set G)) :
    N = ⊥ ∨ N = pCore 2 G := by
  have hcard := (core_data e).2
  have hd : Nat.card N ∣ 4 := hcard ▸ card_dvd_of_le hN
  have hcases : Nat.card N = 1 ∨ Nat.card N = 2 ∨ Nat.card N = 4 := by
    obtain ⟨k, hk, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (show Nat.card N ∣ 2 ^ 2 from hd)
    interval_cases k
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  rcases hcases with h | h | h
  · exact Or.inl (card_eq_one.mp h)
  · exfalso
    obtain ⟨x, hx, hall⟩ := (Nat.card_eq_two_iff' (1 : N)).mp h
    let y : N := ⟨c * x * c⁻¹, (mem_normalizer_iff.mp hn x).mp x.property⟩
    have hy : y ≠ 1 := by
      intro he
      apply hx
      apply Subtype.ext
      have he' : c * (x : G) * c⁻¹ = 1 := congrArg Subtype.val he
      have hh := congrArg (fun z : G => c⁻¹ * z * c) he'
      simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel_right, mul_one,
        inv_mul_cancel, coe_one] using hh
    have he : c * (x : G) * c⁻¹ = x := congrArg Subtype.val (hall y hy)
    have hx2 : (x : G) ^ 2 = 1 := by
      have hp := pow_card_eq_one' (x := x)
      rw [h] at hp
      exact congrArg Subtype.val hp
    apply cubic_moves_involution (e c) (e x)
      (by rw [← map_pow, ← hc, pow_orderOf_eq_one, map_one])
      (by intro hh; have := e.injective (hh.trans e.map_one.symm); simp_all)
      (by rw [← map_pow, hx2, map_one])
      (by intro hh; exact hx (Subtype.ext (e.injective (hh.trans e.map_one.symm))))
    simpa only [map_mul, map_inv] using congrArg e he
  · exact Or.inr (eq_of_le_of_card_ge hN (by omega))
end Matrix.PSL3Two.ParabolicCoreModel
