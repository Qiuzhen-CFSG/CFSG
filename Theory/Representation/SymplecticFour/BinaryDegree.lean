module

public import Theory.NumberTheory.BinaryPrimitiveDivisor.EvenDegree
public import Theory.Representation.BinaryPrimeDegree
public import Theory.SpecificGroups.SymplecticFour.Sylow.AmbientOrder

/-!
# The binary degree of the symplectic four-space group

A primitive prime at binary degree 4m divides q⁴−1 and hence the order
q⁴(q²−1)(q⁴−1) of the actual Sp₄ matrix group, where q=2^m. Every faithful
binary representation consequently has dimension at least 4m. The proof
covers every positive m and needs no irreducibility or recognition input.
Source: Aschbacher–Smith E.2.13(4), printed p.225.
-/

public section
open Subgroup
namespace Representation.SymplecticFour
open Theory.SpecificGroups.SymplecticFour
variable {F W : Type*} [Field F] [Finite F] [AddCommGroup W]
  [Module (ZMod 2) W] [FiniteDimensional (ZMod 2) W]

theorem prime_dvd_card_of_orderOf_two {n p : ℕ} (_hn : 0 < n)
    (hF : Nat.card F = 2 ^ n) (_hp : p.Prime)
    (ho : orderOf (2 : ZMod p) = 4 * n) : p ∣ Nat.card (Sp F) := by
  have hpow : (2 : ZMod p) ^ (4 * n) = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
  have hdiv : p ∣ 2 ^ (4 * n) - 1 := by
    apply (Nat.modEq_iff_dvd' (Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)) : 1 ≤ 2 ^ (4 * n))).mp
    apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
    simpa only [Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hpow.symm
  rw [card_sp, hF, ← pow_mul, mul_comm n 4]
  exact dvd_mul_of_dvd_right hdiv _

theorem finrank_ge {n : ℕ} (hn : 0 < n) (hF : Nat.card F = 2 ^ n)
    (ρ : Representation (ZMod 2) (Sp F) W) (hρ : Function.Injective ρ) :
    4 * n ≤ Module.finrank (ZMod 2) W := by
  obtain ⟨p,hp,ho⟩ := Theory.NumberTheory.exists_prime_orderOf_two_four_mul hn
  have hp2 : p ≠ 2 := by
    intro he
    subst p
    rw [show (2 : ZMod 2) = 0 by decide, orderOf_zero] at ho
    omega
  have hd := BinaryPrimeDegree.orderOf_le_finrank ρ hρ hp hp2
    (prime_dvd_card_of_orderOf_two hn hF hp ho)
  rwa [ho] at hd
end Representation.SymplecticFour
