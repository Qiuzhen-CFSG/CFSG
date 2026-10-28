module

public import Theory.FieldTheory.QuadraticFrobeniusFixed

/-!
# Fixed-field cardinality under finite-field transport

An isomorphism with GF(p^(2n)) intertwines the prescribed p^n power map
with quadratic Frobenius. Transporting its fixed points therefore gives
exactly p^n elements. This is the usual finite-field subfield theorem and
keeps the fixed-field and matrix-field orders separate in unitary models.
The transport argument generalizes `Source.Unitary.fixed_card` from
`CFSG/Quasithin/ChapterF/Section01/RankOneBorels/Unitary/FieldParameters.lean`.
-/

public section
namespace FiniteField
variable {F : Type*} [Field F] [Finite F]
/-- Transport the quadratic Frobenius fixed-field cardinality to an arbitrary
finite field with the prescribed power map. -/
theorem card_fixed_of_quadratic_frobenius (σ : F ≃+* F) (p n : ℕ) [Fact p.Prime] (hn : 0 < n)
    (hcard : Nat.card F = (p ^ n) ^ 2)
    (hσ : ∀ x, σ x = x ^ (p ^ n)) :
    Nat.card {x : F // σ x = x} = p ^ n := by
  classical
  let K := GaloisField p (2 * n)
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = (p ^ n) ^ 2 := by
    rw [GaloisField.card p (2 * n) (by omega), ← pow_mul]
    congr 1
    omega
  let e : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcard.trans hK.symm)
  let τ := iterateFrobeniusEquiv K p n
  have he (x : F) : σ x = x ↔ τ (e x) = e x := by
    rw [hσ, iterateFrobeniusEquiv_def, ← map_pow]
    exact e.injective.eq_iff.symm
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv he)).trans
    (GaloisField.card_fixedBy_quadraticFrobenius p n (by omega))
end FiniteField
