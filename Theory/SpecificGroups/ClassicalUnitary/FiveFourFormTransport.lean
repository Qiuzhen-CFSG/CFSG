module

public import Theory.LinearAlgebra.Hermitian.IdentityGramEquivalence
public import Theory.FieldTheory.QuadraticFrobeniusFixed
public import Theory.SpecificGroups.ClassicalUnitary.FiveFlag

/-!
# Arbitrary Hermitian forms for PSU₅(4)

Fourth-power Frobenius on a field of order sixteen has four fixed elements.
Huppert II.10.4 then gives an orthonormal basis for every nondegenerate
Hermitian form. The existing matrix-conjugation equivalence descends to
the actual images in PGL, retaining the scalar quotient.

This completes the form-change step for the PSU₅(4) case of
Aschbacher–Smith, Theorem 0.1.2(1), printed p.4. It does not assert local
rank bounds or characteristic two. The projective conjugation step uses
the general `IdentityGramEquivalence` API.
-/

namespace Theory.SpecificGroups.UnitaryFive

open BenderSuzuki.MatrixGroups
open HermitianForm.IdentityGram

variable {F : Type*} [Field F] [Finite F]

/-- Fourth-power Frobenius on a field of sixteen elements fixes four elements. -/
public theorem fixed_card_four {n : ℕ} (J : HermitianForm n F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) :
    Nat.card {x : F // J.conj x = x} = 4 := by
  classical
  let K := GaloisField 2 4
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = 16 := GaloisField.card 2 4 (by decide)
  let e : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcard.trans hK.symm)
  let σ := iterateFrobeniusEquiv K 2 2
  have he (x : F) : J.conj x = x ↔ σ (e x) = e x := by
    rw [hconj, iterateFrobeniusEquiv_def, ← map_pow]
    exact e.injective.eq_iff.symm
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv he)).trans
    (GaloisField.card_fixedBy_quadraticFrobenius 2 2 (by decide))

/-- The matrix-field cardinality supplies characteristic two. -/
public theorem charP_two_of_card_sixteen (hcard : Nat.card F = 16) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  apply (FiniteField.even_card_iff_char_two).mpr
  rw [← Nat.card_eq_fintype_card, hcard]

/-- An arbitrary allowed Hermitian form gives the same projective group as
the identity Gram matrix for its stored involution. -/
public theorem projective_equiv_identity_four (J : HermitianForm 5 F)
    (hcard : Nat.card F = 16) (hconj : ∀ x, J.conj x = x ^ 4) :
    Nonempty (ProjectiveSpecialUnitaryMatrixGroup J ≃*
      ProjectiveSpecialUnitaryMatrixGroup (identityGram J)) := by
  obtain ⟨P, hP⟩ := BenderSuzuki.External.huppert_II_10_4_a_orthonormal_basis
    5 J 4 hcard (fixed_card_four J hcard hconj)
  exact ⟨projectiveEquiv J P hP⟩

/-- The actual projective image is finite, without an additional model assumption. -/
public theorem finite_projective (J : HermitianForm 5 F) :
    Finite (ProjectiveSpecialUnitaryMatrixGroup J) := by
  let : Finite (GL (Fin 5) F) := Finite.of_injective Units.val Units.val_injective
  exact Finite.of_surjective (project J) (project_surjective J)

end Theory.SpecificGroups.UnitaryFive
