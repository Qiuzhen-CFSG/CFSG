module
public import ABG.ChapterII.Section2.UnitaryScalarModels
public import Theory.FieldTheory.RootsOfUnityCard

/-!
# Order of the norm-one scalar subgroup in GU2

The image of the actual norm-one scalar embedding is cyclic of order
`p^n+1`. This is the scalar-factor calculation in ABG Chapter II,
Section 2, article pages 16-17, used in Lemma 1(v) and II.3 Proposition 3.
Centrality is already supplied by `GU2Scalar_range_le_center`; identification
with the full unitary center is a separate structural statement.

The elementary factorization of `q^2-1` shows that `q+1` divides the order
of the multiplicative group of `GF(q^2)`. The shared finite-field
roots-of-unity theorem gives exactly `q+1` roots. The proved scalar
injection identifies that cyclic root group with its actual GU2 image,
transferring cardinality and cyclicity without a recognition assumption.
-/

namespace ABG

public theorem GU2Scalar_structure
    (p n : ℕ) [Fact p.Prime] (hn : n ≠ 0) :
    IsCyclic (GU2Scalar p n hn).range ∧
      Nat.card (GU2Scalar p n hn).range = p ^ n + 1 := by
  have hdiv : p ^ n + 1 ∣ Nat.card (GaloisField p (2 * n)) - 1 := by
    rw [GaloisField.card p (2 * n) (Nat.mul_ne_zero (by decide) hn)]
    have hpow : p ^ (2 * n) = (p ^ n) ^ 2 := by rw [← pow_mul, Nat.mul_comm n 2]
    rw [hpow]
    refine ⟨p ^ n - 1, ?_⟩
    simpa only [one_pow] using (Nat.sq_sub_sq (p ^ n) 1)
  let e := MonoidHom.ofInjective (GU2Scalar_injective p n hn)
  have hcyc : IsCyclic (GU2Scalar p n hn).range :=
    isCyclic_of_surjective e.toMonoidHom e.surjective
  refine ⟨hcyc, ?_⟩
  exact (Nat.card_congr e.symm.toEquiv).trans
    (FiniteField.card_rootsOfUnity_of_dvd (GaloisField p (2 * n)) (p ^ n + 1) hdiv)

end ABG
