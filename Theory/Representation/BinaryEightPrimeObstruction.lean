module

public import Theory.Representation.NonsplitFour
public import Theory.Representation.ElementaryAbelianAction
import Mathlib.Tactic

/-!
# Prime obstructions to small binary representations

No prime at least eleven congruent to three or five modulo eight divides
`|GL₈(2)|`. The general linear group order formula gives the prime divisors
2, 3, 5, 7, 17, 31 and 127. The order in every dimension at most eight divides
this order, so the same obstruction holds for a faithful binary representation
or a faithful action on an elementary abelian group of order at most 256.

This supplies the final representation obstruction in Aschbacher–Smith,
*The Classification of Quasithin Groups*, combined 1 March 2004 manuscript,
Theorem 6.1.27, printed p.679. The order argument avoids the stronger
minimal-degree theorem cited there. Construction of the faithful action and
the bound on the module order are separate group-theoretic obligations.
-/

@[expose] public section

namespace Representation.BinaryEight

open Matrix
open scoped IsMulCommutative

/-- Orders in the smaller dimensions divide the order in dimension eight. -/
theorem card_binary_GL_dvd_eight {d : ℕ} (hd : d ≤ 8) :
    Nat.card (GL (Fin d) (ZMod 2)) ∣ Nat.card (GL (Fin 8) (ZMod 2)) := by
  rw [Matrix.card_GL_field, Matrix.card_GL_field]
  interval_cases d <;> norm_num [Fin.prod_univ_succ]

/-- The complete list of possible prime divisors of the matrix group order. -/
theorem prime_divisors_binary_GL_eight {p : ℕ} (hp : p.Prime)
    (hdiv : p ∣ Nat.card (GL (Fin 8) (ZMod 2))) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 17 ∨ p = 31 ∨ p = 127 := by
  have hc : Nat.card (GL (Fin 8) (ZMod 2)) =
      2 ^ 28 * 3 ^ 5 * 5 ^ 2 * 7 ^ 2 * 17 * 31 * 127 := by
    rw [Matrix.card_GL_field]
    norm_num [Fin.prod_univ_succ]
  rw [hc] at hdiv
  simp only [hp.dvd_mul] at hdiv
  have hp1 := hp.ne_one
  rcases hdiv with (((((h | h) | h) | h) | h) | h) | h
  all_goals try replace h := hp.dvd_of_dvd_pow h
  all_goals
    have heq := (Nat.dvd_prime (by norm_num)).mp h
    rcases heq with heq | heq
    · exact (hp1 heq).elim
    · subst p; simp

/-- A faithful representation in dimension at most eight excludes every
prime divisor in the indicated congruence classes above seven. -/
theorem no_injective_representation
    {A V : Type*} [Group A] [Finite A] [AddCommGroup V]
    [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) A V) (hρ : Function.Injective ρ)
    (hd : Module.finrank (ZMod 2) V ≤ 8) {p : ℕ} (hp : p.Prime)
    (hmin : 11 ≤ p) (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hdiv : p ∣ Nat.card A) : False := by
  have hGL := Representation.card_dvd_card_GL_of_injective ρ hρ
  have hpGL := hdiv.trans (hGL.trans (card_binary_GL_dvd_eight hd))
  have h := prime_divisors_binary_GL_eight hp hpGL
  rcases h with h | h | h | h | h | h | h <;> subst p <;> omega

/-- The same obstruction for an actual group action, using the canonical
binary vector-space structure of an elementary abelian two-group. -/
theorem no_faithful_action
    {A V : Type*} [Group A] [Group V] [Finite A] [Finite V]
    [IsElementaryAbelian 2 V] [MulDistribMulAction A V] [FaithfulSMul A V]
    (hV : Nat.card V ≤ 256) {p : ℕ} (hp : p.Prime)
    (hmin : 11 ≤ p) (hmod : p % 8 = 3 ∨ p % 8 = 5)
    (hdiv : p ∣ Nat.card A) : False := by
  let ρ := Representation.ofElementaryAbelianAction (A := A) (G := V) (p := 2)
  have hρ : Function.Injective ρ := by
    intro a b hab
    apply FaithfulSMul.eq_of_smul_eq_smul (α := V)
    intro v
    exact Additive.ofMul.injective (LinearMap.congr_fun hab (Additive.ofMul v))
  have hd : Module.finrank (ZMod 2) (Additive V) ≤ 8 := by
    have hc : Nat.card (Additive V) ≤ 256 := (Nat.card_congr Additive.toMul).trans_le hV
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)] at hc
    norm_num only [Nat.card_zmod] at hc
    exact (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).mp hc
  exact no_injective_representation ρ hρ hd hp hmin hmod hdiv

end Representation.BinaryEight
