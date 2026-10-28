module
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Algebra.Ring.Action.End
public import Mathlib.Tactic

/-!
# The fixed field of quadratic Frobenius

For nonzero n, the fixed subfield of the n-th Frobenius on GF(p^(2n))
has cardinality p^n. The theorem uses the actual fixed subfield of the
existing iterateFrobeniusEquiv; it does not choose a replacement involution.
The characteristic may be two.

The divisibility n | 2n gives a genuine embedding of GF(p^n), whose image
is fixed by Frobenius. This bounds the fixed-field cardinality below.
Every element of the fixed field is a root of X^(p^n)-X, whose degree
bounds the cardinality above.

This standard finite-field subfield calculation supplies the coordinates
for ABG II.2 Lemma1(vi), article p17. Its statement and dependencies are
independent of Hermitian forms or group-classification models.
-/

namespace GaloisField

public theorem card_fixedBy_quadraticFrobenius (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    Nat.card (FixedBy.subfield (GaloisField p (2 * n))
      (iterateFrobeniusEquiv (GaloisField p (2 * n)) p n)) = p ^ n := by
  classical
  let F := GaloisField p (2 * n)
  let k := FixedBy.subfield F (iterateFrobeniusEquiv F p n)
  let K := GaloisField p n
  let : Fintype k := Fintype.ofFinite k
  let : Fintype K := Fintype.ofFinite K
  have hp : 1 < p := (Fact.out : p.Prime).one_lt
  have h2n : 2 * n ≠ 0 := Nat.mul_ne_zero (by decide) hn
  obtain ⟨e⟩ := FiniteField.nonempty_algHom_of_finrank_dvd
    (F := ZMod p) (K := K) (L := F) (by
      change Module.finrank (ZMod p) (GaloisField p n) ∣
        Module.finrank (ZMod p) (GaloisField p (2 * n))
      rw [GaloisField.finrank p hn, GaloisField.finrank p h2n]
      exact dvd_mul_left _ _)
  have he : ∀ a : K, e a ∈ k := by
    intro a
    change iterateFrobeniusEquiv F p n (e a) = e a
    rw [iterateFrobeniusEquiv_def, ← map_pow]
    congr 1
    rw [← GaloisField.card p n hn]
    simpa only [Nat.card_eq_fintype_card] using FiniteField.pow_card a
  let ek : K → k := fun a => ⟨e a, he a⟩
  have heki : Function.Injective ek := fun a b h => e.injective (congrArg Subtype.val h)
  have hlo : p ^ n ≤ Nat.card k := by
    rw [← GaloisField.card p n hn]
    exact Nat.card_le_card_of_injective ek heki
  have hhi : Nat.card k ≤ p ^ n := by
    let P : Polynomial k := Polynomial.X ^ (p ^ n) - Polynomial.X
    have hP : P ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero k hn hp
    have hroot : (Finset.univ : Finset k).val ⊆ P.roots := by
      intro a _
      rw [Polynomial.mem_roots hP]
      simp only [P, Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow,
        Polynomial.eval_X]
      apply sub_eq_zero.mpr
      apply Subtype.ext
      exact a.property
    have hd := Polynomial.card_le_degree_of_subset_roots hroot
    have hdeg : P.natDegree ≤ p ^ n := by
      exact (Polynomial.natDegree_sub_le _ _).trans (by
        simp [Nat.one_le_pow n p (by omega : 0 < p)])
    simpa only [Finset.card_univ, ← Nat.card_eq_fintype_card] using hd.trans hdeg
  exact le_antisymm hhi hlo

end GaloisField

