module
public import ABG.ChapterII.Section2.UnitaryQuadraticCoordinates
public import Theory.FieldTheory.OddFixedQuadraticEmbedding
public import ABG.ChapterII.Section2.UnitaryOddExtensionEmbedding

/-!
# Unitary coordinates fixed by odd coefficient automorphisms

For odd prime p and nonzero n, an odd-order subgroup A of the full
automorphism group of GF(p^(2n)) fixes a pair z,t with norm(z)=-1,
t nonzero, and conjugate(t)=-t, for the original unitary involution.
These coordinates make the SU2--SL2 change-of-basis matrix A-fixed and
support the coefficient-compatible identification in ABG II.3 Proposition 3,
article page 27. The small fields q=3 and q=9 are retained.

The actual A-fixed quadratic embedding supplies GF(p^(2k)) inside the
original field, with n=k|A|. Choose the already proved unitary coordinates
in that smaller field and map them through the embedding. Stored-involution
compatibility under odd extensions transfers the norm and anti-fixed
equations; field injectivity preserves nonzeroness. Every embedded element
is A-fixed, so the resulting coordinates satisfy all conditions without
an assumed fixed basis or a replacement action or Hermitian form.
-/

namespace ABG

public theorem exists_unitary_coordinates_fixed_by_odd_coefficients
    (p n : ℕ) [Fact p.Prime] (hp : Odd p) (hn : n ≠ 0)
    (A : Subgroup (GaloisField p (2 * n) ≃+* GaloisField p (2 * n)))
    (hA : Odd (Nat.card A)) :
    ∃ z t : GaloisField p (2 * n),
      z * (unitaryForm 2 p n hn).conj z = -1 ∧
      t ≠ 0 ∧ (unitaryForm 2 p n hn).conj t = -t ∧
      ∀ σ : A, σ.val z = z ∧ σ.val t = t := by
  obtain ⟨k, hk, hnk, e, he⟩ :=
    GaloisField.exists_fixed_quadratic_embedding_of_odd p n hn A hA
  obtain ⟨⟨z, t, hz, ht0, ht⟩, _⟩ := unitaryQuadraticCoordinates p k hp hk
  refine ⟨e z, e t, ?_, (map_ne_zero e).mpr ht0, ?_, ?_⟩
  · rw [unitary_conj_odd_extension p k n hk hn (Nat.card A) hA hnk e z,
      ← map_mul, hz, map_neg, map_one]
  · rw [unitary_conj_odd_extension p k n hk hn (Nat.card A) hA hnk e t,
      ht, map_neg]
  · intro σ
    exact ⟨he σ z, he σ t⟩

end ABG

