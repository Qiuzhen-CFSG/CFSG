module

public import BenderSuzuki.MatrixGroups.Unitary
public import Theory.FieldTheory.QuadraticFrobeniusFixed

/-!
# Field parameters for the unitary alternatives in F.1.3

The source parameter q = 2^n is the fixed-field order; the matrix field has
q² elements. A finite-field isomorphism transports the stored involution to
quadratic Frobenius, giving exactly q fixed elements. The even field order
also supplies characteristic two. Both arguments include n = 1 and impose
no restriction on the nondegenerate Hermitian Gram matrix.

Source: Aschbacher–Smith, printed pp.259–260; the fixed-field calculation
uses `GaloisField.card_fixedBy_quadraticFrobenius`.
-/

open BenderSuzuki.MatrixGroups

namespace CFSG.Quasithin.ChapterF.Source.Unitary

variable {F : Type*} [Field F] [Finite F]

/-- The stored involution has the source fixed-field cardinality. -/
public theorem fixed_card (J : HermitianForm 3 F) (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2)
    (hconj : ∀ x, J.conj x = x ^ (2 ^ n)) :
    Nat.card {x : F // J.conj x = x} = 2 ^ n := by
  classical
  let K := GaloisField 2 (2 * n)
  let : Fintype F := Fintype.ofFinite F
  let : Fintype K := Fintype.ofFinite K
  have hK : Nat.card K = (2 ^ n) ^ 2 := by
    rw [GaloisField.card 2 (2 * n) (by omega), ← pow_mul]
    congr 1
    omega
  let e : F ≃+* K := FiniteField.ringEquivOfCardEq (by
    simpa only [← Nat.card_eq_fintype_card] using hcard.trans hK.symm)
  let σ := iterateFrobeniusEquiv K 2 n
  have he (x : F) : J.conj x = x ↔ σ (e x) = e x := by
    rw [hconj, iterateFrobeniusEquiv_def, ← map_pow]
    exact e.injective.eq_iff.symm
  exact (Nat.card_congr (e.toEquiv.subtypeEquiv he)).trans
    (GaloisField.card_fixedBy_quadraticFrobenius 2 n (by omega))

/-- The matrix field in the even unitary alternatives has characteristic two. -/
public theorem charP_two (n : ℕ) (hn : 0 < n)
    (hcard : Nat.card F = (2 ^ n) ^ 2) : CharP F 2 := by
  let : Fintype F := Fintype.ofFinite F
  apply ringChar.of_eq
  apply (FiniteField.even_card_iff_char_two).mpr
  rw [← Nat.card_eq_fintype_card, hcard]
  have he : Even (2 ^ n) := (even_two.pow_of_ne_zero (by omega))
  exact Nat.mod_eq_zero_of_dvd
    (even_iff_two_dvd.mp (he.pow_of_ne_zero (by decide : (2 : ℕ) ≠ 0)))

end CFSG.Quasithin.ChapterF.Source.Unitary
