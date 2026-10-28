module

public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.PGroup
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Algebra.Group.Conj
import Mathlib.Tactic.Group

/-!
# Centralization through a fixed coprime prime layer

Suppose that X fixes a p-subgroup P pointwise and [J,X] lies in P.
If p is prime to |X|, then X centralizes J. For j in J and x in X,
the commutator d = [j,x] commutes with x. The identity
d x = j x j⁻¹ implies d^|X| = 1. Since d has p-power order, d = 1.

Neither solvability of J nor normality of J in the ambient group is needed.
This supplies the two successive coprime-action steps in Aschbacher–Smith,
*The Classification of Quasithin Groups*, Lemma 8.2.9, printed p.720.
-/

namespace Subgroup
open scoped commutatorElement

/-- An actor fixing a coprime prime layer also fixes every subgroup whose
commutators with that actor lie in the layer. -/
public theorem le_centralizer_of_fixed_coprime_prime_layer
    {G : Type*} [Group G] (X J P : Subgroup G) {p : ℕ}
    (hP : IsPGroup p P) (hcop : Nat.Coprime p (Nat.card X))
    (hfix : X ≤ centralizer (P : Set G)) (hcomm : ⁅J, X⁆ ≤ P) :
    X ≤ centralizer (J : Set G) := by
  intro x hx j hj
  let d : G := ⁅j, x⁆
  have hd : d ∈ P := hcomm (commutator_mem_commutator hj hx)
  have hc : Commute d x := hfix hx d hd
  have hxpow : x ^ Nat.card X = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨x, hx⟩ : X)))
  have hdpow : d ^ Nat.card X = 1 := by
    have he : d * x = j * x * j⁻¹ := by
      dsimp [d, commutatorElement_def]
      group
    have hh : (d * x) ^ Nat.card X = 1 := by
      rw [he, conj_pow, hxpow]
      group
    simpa only [hc.mul_pow, hxpow, mul_one] using hh
  obtain ⟨k, hk⟩ := hP.exists_pow_pow_eq_one (⟨d, hd⟩ : P)
  have hone : (⟨d, hd⟩ : P) = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes (hcop.pow_left k)
      (orderOf_dvd_of_pow_eq_one hk)
      (orderOf_dvd_of_pow_eq_one
        (show (⟨d, hd⟩ : P) ^ Nat.card X = 1 from Subtype.ext hdpow)))
  have he : ⁅j, x⁆ = 1 := congrArg Subtype.val hone
  exact commutatorElement_eq_one_iff_mul_comm.mp he

end Subgroup
