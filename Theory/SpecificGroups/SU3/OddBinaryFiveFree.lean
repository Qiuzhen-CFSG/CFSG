module
public import Theory.SpecificGroups.SU3.BinarySylowOrder
public import Theory.SpecificGroups.SU3.PrimeCentralKernel

/-!
# Five is absent from SU₃ over odd binary exponents

For odd n, 2ⁿ is 2 or 3 modulo five. The order formula for PSU₃(2ⁿ)
therefore has no factor five. The actual special-to-projective kernel
has order dividing three, so the full SU₃ also has order prime to five.
The stored Hermitian form and its quadratic Frobenius are retained.

Source: Huppert II.10.12; the unitary exception in Aschbacher--Smith
A.2.1(1b), printed p.33. Its application to the Mathieu pumpup in 4.2.13
is in ChapterA.Section02.Statements.UnitaryExceptionFiveFree.
-/

public noncomputable section
open Subgroup Theory.GroupTheory BenderSuzuki.MatrixGroups

private theorem odd_power_two_mod_five {n : ℕ} (hn : Odd n) :
    2 ^ n % 5 = 2 ∨ 2 ^ n % 5 = 3 := by
  obtain ⟨k,rfl⟩ := hn
  induction k with
  | zero => decide
  | succ k ih =>
    have he : 2 * (k + 1) + 1 = (2*k+1)+2 := by omega
    rw [he,pow_add,Nat.mul_mod]
    rcases ih with ih | ih <;> norm_num [ih]

private theorem unitary_order_five_free {n : ℕ} (hn : Odd n) :
    ¬ 5 ∣ ((2^n)^3+1)*(2^n)^3*((2^n)^2-1) := by
  have hq : 1 ≤ (2^n)^2 := Nat.one_le_pow _ _ (Nat.one_le_pow _ _ (by decide))
  have hsub : ((2^n)^2-1)%5 = (((2^n)^2)%5+4)%5 := by omega
  rw [Nat.dvd_iff_mod_eq_zero,Nat.mul_mod,Nat.mul_mod,hsub]
  rcases odd_power_two_mod_five hn with hm | hm <;>
    norm_num [Nat.add_mod,Nat.mul_mod,Nat.pow_mod,hm]

namespace BenderSuzuki.MatrixGroups.HermitianForm
open OddPrimeSylow.NormalizedOuter
/-- The full special unitary group has order prime to five when n is odd. -/
theorem special_card_five_free_of_odd_binary
    {F : Type*} [Field F] [Finite F] (J : HermitianForm 3 F)
    {n : ℕ} (hn : Odd n) (hc : Nat.card F = (2^n)^2)
    (hj : ∀ x, J.conj x = x^(2^n)) : ¬ 5 ∣ Nat.card J.specialSubgroup := by
  have hn0 : 0 < n := hn.pos
  have hf : Nat.card {x : F // J.conj x = x} = 2^n :=
    FiniteField.card_fixed_of_quadratic_frobenius J.conj 2 n hn0 hc hj
  obtain ⟨e⟩ := FormTransport.exists_projectiveEquiv J (2^n) hc hf
  obtain ⟨_,_,_,_,_,_,_,_,horder,_⟩ :=
    BenderSuzuki.External.huppert_II_10_12 (FormTransport.standardForm J) (2^n) hc hf rfl
  have hd : Nat.gcd 3 (2^n+1) ∣ ((2^n)^3+1)*(2^n)^3*((2^n)^2-1) := by
    have h3 : Nat.gcd 3 (2^n+1) ∣ (2^n)^3+1 :=
      (Nat.gcd_dvd_right 3 (2^n+1)).trans (by
        refine ⟨(2^n)^2-2^n+1,?_⟩
        have hp : 2^n ≤ (2^n)^2 := Nat.le_self_pow (by decide) _
        nlinarith [Nat.sub_add_cancel hp])
    exact (dvd_mul_of_dvd_left h3 _).mul_right _
  have hp : ¬ 5 ∣ Nat.card (ProjectiveSpecialUnitaryMatrixGroup J) := by
    rw [Nat.card_congr e.toEquiv,horder]
    exact fun h => unitary_order_five_free hn (h.trans (Nat.div_dvd_of_dvd hd))
  rw [card_eq_card_quotient_mul_card_subgroup J.specialToProjective.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective J.specialToProjective
      J.specialToProjective_surjective).toEquiv]
  intro hd
  rcases (by decide : Nat.Prime 5).dvd_mul.mp hd with h | h
  · exact hp h
  · exact (by decide : ¬ 5 ∣ 3) (h.trans J.card_specialToProjective_ker_dvd_three)
end BenderSuzuki.MatrixGroups.HermitianForm

