module

public import Theory.AlgebraicGroup.CoordinateRing.Hopf.PolynomialArtinSchreierCocycle

/-!
# Consumer for polynomial Artin--Schreier straightening

The consumer keeps the pure polynomial API honest: it composes unrestricted
straightening with algebraically-closed elimination, instantiates
straightening for the zero cocycle, and separately checks elimination on an
arbitrary additive polynomial.  Geometric modules can use these results
without importing a primitive-curve or classification chain.
-/

open scoped Polynomial Polynomial.Bivariate

namespace Theory.AlgebraicGroup

noncomputable section

universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Straightening and additive elimination compose to leave only a linear
Artin--Schreier residual term. -/
public theorem polynomial_artin_schreier_linear_consumer
    {p : ℕ} [Fact p.Prime] [CharP k p]
    {C : BivariatePolynomial k} {f : Polynomial k}
    (hnormalized : IsNormalizedPolynomialCocycle C)
    (hsymmetric : IsSymmetricPolynomialCocycle C)
    (hcocycle : IsAdditivePolynomialTwoCocycle C)
    (hartin : C ^ p - C = additiveCoboundary f) :
    ∃ h q : Polynomial k, ∃ a : k,
      C = additiveCoboundary h ∧
      f - (h ^ p - h) - (q ^ p - q) = Polynomial.C a * Polynomial.X := by
  obtain ⟨h, P, hC, hP, hPadd⟩ :=
    polynomial_artin_schreier_cocycle_straightening
      hnormalized hsymmetric hcocycle hartin
  obtain ⟨q, a, hlinear⟩ := additivePolynomial_congruent_linear P hPadd
  refine ⟨h, q, a, hC, ?_⟩
  rw [← hP]
  exact hlinear

public theorem zero_polynomial_artin_schreier_consumer
    {p : ℕ} [Fact p.Prime] [CharP k p] :
    ∃ h P : Polynomial k,
      (0 : BivariatePolynomial k) = additiveCoboundary h ∧
      P = (0 : Polynomial k) - (h ^ p - h) ∧
      IsAdditivePolynomial P := by
  apply polynomial_artin_schreier_cocycle_straightening
      (C := (0 : BivariatePolynomial k)) (f := (0 : Polynomial k))
  · rw [isNormalizedPolynomialCocycle_iff]
    constructor <;> intro x <;> simp
  · rw [isSymmetricPolynomialCocycle_iff]
    intro x y
    simp
  · rw [isAdditivePolynomialTwoCocycle_iff]
    intro x y z
    simp
  · rw [additiveCoboundary_zero]
    simp [(Fact.out : p.Prime).ne_zero]

public theorem additive_polynomial_elimination_consumer
    {p : ℕ} [Fact p.Prime] [CharP k p]
    (P : Polynomial k) (hP : IsAdditivePolynomial P) :
    ∃ h : Polynomial k, ∃ a : k,
      P - (h ^ p - h) = Polynomial.C a * Polynomial.X :=
  additivePolynomial_congruent_linear P hP

end
end Theory.AlgebraicGroup
