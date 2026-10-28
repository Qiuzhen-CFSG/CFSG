module

public import Theory.SpecificGroups.ClassicalOrthogonal.Minus.OddFourComparison.HermitianModel
public import Theory.FieldTheory.QuadraticFrobeniusFixed.Transport
import Mathlib.Algebra.Field.ULift

/-!
# A quadratic extension with its literal Frobenius fixed field

A field of order `p^n` is compared with the fixed subfield of the `n`-th
Frobenius on `GF(p^(2n))`. A universe lift keeps the extension in the input
field's universe. The cardinalities give degree two over that fixed field.
This supplies the coefficient field for the negative-determinant Hermitian
model; no group image or exceptional isomorphism is assumed.

Sources: GLS3 §2.7; Aschbacher–Smith A.2.17, printed pp.38–39.
-/

public noncomputable section
namespace ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport
universe u
/-- The quadratic field and its actual fixed field, in the original universe. -/
theorem exists_quadraticField (F : Type u) [Field F] [Finite F] :
    ∃ (E : Type u) (_ : Field E) (_ : Finite E) (σ : E ≃+* E),
      Function.Involutive σ ∧ Nat.card E = (Nat.card F) ^ 2 ∧
      Nat.card (HermitianModel.fixedField σ) = Nat.card F ∧
      Module.finrank (HermitianModel.fixedField σ) E = 2 := by
  let : Fintype F := Fintype.ofFinite F
  obtain ⟨p, n, hp, hn, hq⟩ := (isPrimePow_nat_iff (Fintype.card F)).mp
    (FiniteField.isPrimePow_card F)
  let : Fact p.Prime := ⟨hp⟩
  let E := ULift.{u} (GaloisField p (2 * n))
  let : Fintype E := Fintype.ofFinite E
  let σ := iterateFrobeniusEquiv E p n
  have hcard : Nat.card E = (p ^ n) ^ 2 := by
    rw [Nat.card_ulift, GaloisField.card p (2 * n) (by omega), ← pow_mul]
    congr 1
    omega
  have hinv : Function.Involutive σ := by
    intro x
    change iterateFrobeniusEquiv E p n (iterateFrobeniusEquiv E p n x) = x
    rw [← iterateFrobeniusEquiv_add_apply, iterateFrobeniusEquiv_def, ← two_mul]
    have hce : p ^ (2 * n) = Fintype.card E := by
      rw [← Nat.card_eq_fintype_card, hcard, ← pow_mul, Nat.mul_comm n 2]
    rw [hce]
    exact FiniteField.pow_card x
  have hfix : Nat.card (HermitianModel.fixedField σ) = p ^ n :=
    FiniteField.card_fixed_of_quadratic_frobenius σ p n hn hcard
      (fun x => iterateFrobeniusEquiv_def E p n x)
  have hdim : Module.finrank (HermitianModel.fixedField σ) E = 2 := by
    have h := Module.natCard_eq_pow_finrank (K := HermitianModel.fixedField σ) (V := E)
    rw [hcard, hfix] at h
    exact (Nat.pow_right_injective (Nat.one_lt_pow (by omega) hp.one_lt)) h.symm
  have hq' : p ^ n = Nat.card F := by simpa only [Nat.card_eq_fintype_card] using hq
  exact ⟨E, inferInstance, inferInstance, σ, hinv, hcard.trans (by rw [hq']),
    hfix.trans hq', hdim⟩

end ClassicalOrthogonal.Minus.OddFourComparison.QuadraticTransport
