module

public import Theory.PPrimeCore
public import Mathlib.GroupTheory.Perm.Fin

/-!
# The odd core of the symmetric group on four letters

An odd-order subgroup of S₄ has order dividing three. If it is normal, each
product of an element with one of its conjugates also has cube one. A
kernel-checked calculation on the 24 permutations shows that only the identity
has this property. Thus S₄ has no nontrivial normal subgroup of odd order.

This is the small fixed-group calculation used in Aschbacher–Smith, combined
manuscript (1 March 2004), E.6.19, printed p.252 (PDF p.263).
-/

open Subgroup
namespace SymmetricFour

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem cube_conjugate_test : ∀ g : Equiv.Perm (Fin 4),
    g ^ 3 = 1 → (∀ s, (g * (s * g * s⁻¹)) ^ 3 = 1) → g = 1 := by
  decide +kernel

/-- The actual four-point symmetric group has trivial odd core. -/
public theorem oddCore_eq_bot : pPrimeCore 2 (Equiv.Perm (Fin 4)) = ⊥ := by
  let O := pPrimeCore 2 (Equiv.Perm (Fin 4))
  have hc : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card
  have hd : Nat.card O ∣ 2 ^ 3 * 3 := by
    have h := O.card_subgroup_dvd_card
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial] at h ⊢
    exact h
  have hd3 : Nat.card O ∣ 3 := hc.symm.pow_right 3 |>.dvd_of_dvd_mul_left hd
  have hp (g : Equiv.Perm (Fin 4)) (hg : g ∈ O) : g ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((O.orderOf_dvd_natCard hg).trans hd3)
  apply eq_bot_iff.mpr
  intro g hg
  apply mem_bot.mpr
  exact cube_conjugate_test g (hp g hg) (fun s => hp _
    (O.mul_mem hg ((inferInstance : O.Normal).conj_mem g hg s)))

end SymmetricFour
