module

public import Theory.SpecificGroups.ClassicalUnitary.FiveParabolicTorus.Cover
public import Mathlib.Data.Nat.Factorization.PrimePow

/-!
# The unitary-five cover in even characteristic

For any even fixed-field size q, choose an odd prime dividing q + 1.
The diagonal norm-one torus has rank three in the centralizer of the
actual coordinate-swap involution of SU5(q). Hence SU5(q) is not quasithin.
Transport through an orthonormal basis proves the same statement for the
original Hermitian form and its special unitary group.

Source: Aschbacher--Smith, *The Classification of Quasithin Groups*,
A.2.18, printed p.40, the special-unitary covering branch. The proof uses
an involution centralizer of the cover itself.
-/

public section

open BenderSuzuki.MatrixGroups Matrix
namespace Theory.SpecificGroups.UnitaryFive
variable {F : Type*} [Field F] [Finite F]

/-- Every even-parameter SU5 in identity coordinates fails quasithinness. -/
theorem not_quasithin_special_even [CharP F 2]
    (J : HermitianForm 5 F) (hJ : J.form = 1) {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (heven : Even q) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) :
    ¬ IsQuasithin J.specialSubgroup := by
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  obtain ⟨p, hp, hd⟩ := Nat.exists_prime_and_dvd (show q + 1 ≠ 1 by omega)
  have hn : p ≠ 2 := by
    rintro rfl
    obtain ⟨a, ha⟩ := heven
    obtain ⟨b, hb⟩ := hd
    omega
  have ho : Odd p := Nat.odd_iff.mpr (hp.eq_two_or_odd.resolve_left hn)
  intro hqt
  have hr := primeRank_special_swapCentralizer_ge J hJ hcard hq hconj hp hd
  have hb := (Theory.GroupTheory.isQuasithin_iff_twoLocal.mp hqt) _
    (Theory.GroupTheory.isTwoLocal_involution_centralizer (lineSwap_orderOf J hJ)) p hp ho
  exact (Nat.not_succ_le_self 2) (hr.trans hb)

/-- The obstruction holds on every original Hermitian form with even fixed-field size. -/
theorem not_quasithin_special_even_of_form
    (J : HermitianForm 5 F) {q : ℕ}
    (hcard : Nat.card F = q ^ 2) (heven : Even q) (hq : 2 ≤ q)
    (hconj : ∀ x, J.conj x = x ^ q) :
    ¬ IsQuasithin J.specialSubgroup := by
  let : Fintype F := Fintype.ofFinite F
  let : CharP F 2 := by
    apply ringChar.of_eq
    apply (FiniteField.even_card_iff_char_two).mpr
    rw [← Nat.card_eq_fintype_card, hcard]
    exact Nat.mod_eq_zero_of_dvd
      (even_iff_two_dvd.mp (heven.pow_of_ne_zero (by decide : (2 : ℕ) ≠ 0)))
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  have hprime : IsPrimePow q := by
    apply (isPrimePow_pow_iff (by decide : (2 : ℕ) ≠ 0)).mp
    simpa only [← Nat.card_eq_fintype_card, hcard] using FiniteField.isPrimePow_card F
  have hfixed : Nat.card {x : F // J.conj x = x} = q := by
    obtain ⟨p, n, hp, hn, rfl⟩ := (isPrimePow_nat_iff q).mp hprime
    let : Fact p.Prime := ⟨hp⟩
    exact FiniteField.card_fixed_of_quadratic_frobenius J.conj p n hn hcard hconj
  obtain ⟨P, hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    5 J q hcard hfixed
  intro hqt
  exact not_quasithin_special_even (HermitianForm.IdentityGram.identityGram J) rfl
    hcard heven hq hconj
    (Theory.GroupTheory.isQuasithin_of_equiv (HermitianForm.IdentityGram.specialEquiv J P hP) hqt)

end Theory.SpecificGroups.UnitaryFive
