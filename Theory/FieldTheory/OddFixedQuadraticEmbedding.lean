module
public import Mathlib.FieldTheory.Fixed
public import Mathlib.Algebra.Ring.Action.Subobjects
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.Tactic

/-!
# Quadratic finite-field embeddings fixed by an odd automorphism subgroup

For an odd-order subgroup A of the actual automorphism group of GF(p^(2n)),
with n nonzero, there is a nonzero k such that n=k*|A| and an embedding
GF(p^(2k)) into GF(p^(2n)) fixed pointwise by A. The characteristic p may
be two; the oddness hypothesis concerns only the automorphism subgroup.

Use the canonical coefficient action restricted to A and its actual fixed
subfield K. Artin's theorem gives [GF(p^(2n)):K]=|A|. Write |K|=p^r;
the cardinality formula then gives 2n=r*|A|. Since |A| is odd, r is even,
say 2k, and n=k*|A|. Uniqueness of finite fields of a given cardinality
identifies GF(p^(2k)) with K, and its inclusion into the original field
provides the required pointwise fixed embedding.

This is the finite-field step for the unitary fixed-Sylow construction in
ABG II.3 Proposition 3(iv), article pages 27–28. No replacement field action
or assumed fixed-field embedding is introduced.
-/

namespace GaloisField

public theorem exists_fixed_quadratic_embedding_of_odd
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0)
    (A : Subgroup (GaloisField p (2 * n) ≃+* GaloisField p (2 * n)))
    (hA : Odd (Nat.card A)) :
    ∃ k : ℕ, k ≠ 0 ∧ n = k * Nat.card A ∧
      ∃ e : GaloisField p (2 * k) →+* GaloisField p (2 * n),
        ∀ (σ : A) x, σ.val (e x) = e x := by
  classical
  let F := GaloisField p (2 * n)
  let : Finite (F ≃+* F) :=
    Finite.of_injective (fun e : F ≃+* F => (e : F → F)) DFunLike.coe_injective
  let := Fintype.ofFinite A
  let : FaithfulSMul A F := ⟨fun h => Subtype.ext (RingEquiv.ext h)⟩
  let K := FixedPoints.subfield A F
  let := Fintype.ofFinite K
  have hdegree : Module.finrank K F = Nat.card A := by
    simpa only [K, Nat.card_eq_fintype_card] using FixedPoints.finrank_eq_card A F
  have hcardF : Nat.card F = Nat.card K ^ Nat.card A := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := F), hdegree]
  obtain ⟨r, _, hr⟩ := FiniteField.card K p
  have hcardK : Nat.card K = p ^ (r : ℕ) := by
    simpa only [Nat.card_eq_fintype_card] using hr
  have hpowers : p ^ (2 * n) = p ^ ((r : ℕ) * Nat.card A) := by
    rw [← GaloisField.card p (2 * n) (Nat.mul_ne_zero (by decide) hn)]
    change Nat.card F = _
    rw [hcardF, hcardK, pow_mul]
  have hdeg : 2 * n = (r : ℕ) * Nat.card A :=
    (pow_right_inj₀ (Fact.out : p.Prime).pos (Fact.out : p.Prime).ne_one).mp hpowers
  have hrEven : Even (r : ℕ) := by
    have heven : Even ((r : ℕ) * Nat.card A) := by
      rw [← hdeg]
      exact even_two_mul n
    exact (Nat.even_mul.mp heven).resolve_right (Nat.not_even_iff_odd.mpr hA)
  obtain ⟨k, hk⟩ := hrEven
  have hk0 : k ≠ 0 := by
    intro h
    simp [h] at hk
  have hn_eq : n = k * Nat.card A := by
    rw [hk] at hdeg
    nlinarith
  have hKcard : Nat.card K = Nat.card (GaloisField p (2 * k)) := by
    rw [hcardK, GaloisField.card p (2 * k) (Nat.mul_ne_zero (by decide) hk0), hk,
      ← two_mul]
  let := Fintype.ofFinite (GaloisField p (2 * k))
  let eK : GaloisField p (2 * k) ≃+* K :=
    FiniteField.ringEquivOfCardEq (by
      simpa only [← Nat.card_eq_fintype_card] using hKcard.symm)
  refine ⟨k, hk0, hn_eq, K.subtype.comp eK.toRingHom, ?_⟩
  intro σ x
  exact (eK x).property σ

end GaloisField
