module

public import BenderSuzuki.MatrixGroups.Unitary
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.Algebra.IsPrimePow

/-!
# Standard finite Hermitian spaces

Every prime power `q` supplies a field of order `q²` with its involution
`x ↦ x^q` and the identity Hermitian matrix in every dimension. The involution
law is the finite-field identity `x^(q²) = x`; the identity matrix certifies
nondegeneracy. This discharges the form-existence condition in finite unitary
group models, without a recognition or classification assumption.

Source: GLS3, §2.7, the unitary groups (`refs/KGroup/GLS3/chapter2.tex`).
-/

@[expose] public section

namespace BenderSuzuki.MatrixGroups

/-- A standard Hermitian space exists for every finite-field parameter. -/
theorem exists_standardHermitianForm (n q : ℕ) (hq : IsPrimePow q) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (J : HermitianForm n F),
      Nat.card F = q ^ 2 ∧ (∀ x, J.conj x = x ^ q) := by
  obtain ⟨p, e, hp, he, hq⟩ := (isPrimePow_nat_iff q).mp hq
  let : Fact p.Prime := ⟨hp⟩
  let F := GaloisField p (e * 2)
  let : Fintype F := Fintype.ofFinite F
  have hcard : Nat.card F = q ^ 2 := by
    rw [GaloisField.card p (e * 2) (by omega), pow_mul, hq]
  let σ : F ≃+* F := iterateFrobeniusEquiv F p e
  have hσ (x : F) : σ x = x ^ q := by
    change x ^ (p ^ e) = x ^ q
    rw [hq]
  let J : HermitianForm n F :=
    { conj := σ
      conj_involutive := by
        intro x
        rw [hσ, hσ, ← pow_mul, ← pow_two, ← hcard, Nat.card_eq_fintype_card]
        exact FiniteField.pow_card x
      form := 1
      form_hermitian := by
        intro i j
        by_cases h : i = j <;> simp [Matrix.one_apply, h, Ne.symm]
      form_nondegenerate := by simp }
  exact ⟨F, inferInstance, inferInstance, J, hcard, hσ⟩

end BenderSuzuki.MatrixGroups
