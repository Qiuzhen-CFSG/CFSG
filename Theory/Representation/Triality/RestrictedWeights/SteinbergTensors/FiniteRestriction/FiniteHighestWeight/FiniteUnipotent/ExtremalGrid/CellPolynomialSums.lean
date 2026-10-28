module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.PolynomialSums
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.RegularFunctions
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Spaces

/-!
# Polynomial sums on the literal finite cells

A proved coordinate equivalence and an actual covariant regular function allow
the finite-field coefficient calculation to supply `HasNonzeroCellSum`.
The comparison equation is pointwise on the literal cell inclusion. Existence
of that coordinate map, the global section, and its polynomial bounds remain
explicit inputs; these lemmas do not assert extremal interpolation.

Source context: Steinberg, `Chapter2St2.tex`, Sections 13.2(d) and 13.3(a).
-/

@[expose] public noncomputable section
open scoped BigOperators Classical
open Theory.AlgebraicGroup

namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
universe u
variable {k : Type u} [Field k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- A nonzero top coefficient yields a nonzero sum of the actual regular function. -/
theorem hasNonzeroCellSum_of_polynomial (S : Geometry K) (n : ℕ)
    (P Q : Set S.roots.Root) (chi : TorusWeight S.torus)
    {σ : Type*} [Fintype σ] (F : σ → Type*)
    [∀ i, Field (F i)] [∀ i, Fintype (F i)] (ι : ∀ i, F i →+* k)
    (e : (∀ i, F i) ≃ finiteCell S n Q)
    (f : covariantSpace S P chi) (p : MvPolynomial σ k)
    (heval : ∀ x, f.val (cellInclusion S n Q (e x)) =
      MvPolynomial.eval (fun i => ι i (x i)) p)
    (hp : ∀ d ∈ p.support, d ≠ PolynomialSums.topExponent F →
      ∃ i, d i < Fintype.card (F i) - 1)
    (hc : p.coeff (PolynomialSums.topExponent F) ≠ 0) :
    HasNonzeroCellSum S n P Q chi := by
  classical
  let := Fintype.ofEquiv (∀ i, F i) e
  refine ⟨f, ?_⟩
  rw [finsum_eq_sum_of_fintype, ← e.sum_comp]
  simp only [heval]
  exact PolynomialSums.grid_sum_ne_zero_of_top_coefficient F ι p hp hc

/-- A positive weighted degree bound also suffices for the actual cell sum. -/
theorem hasNonzeroCellSum_of_weighted_polynomial (S : Geometry K) (n : ℕ)
    (P Q : Set S.roots.Root) (chi : TorusWeight S.torus)
    {σ : Type*} [Fintype σ] (F : σ → Type*)
    [∀ i, Field (F i)] [∀ i, Fintype (F i)] (ι : ∀ i, F i →+* k)
    (e : (∀ i, F i) ≃ finiteCell S n Q)
    (f : covariantSpace S P chi) (p : MvPolynomial σ k)
    (heval : ∀ x, f.val (cellInclusion S n Q (e x)) =
      MvPolynomial.eval (fun i => ι i (x i)) p)
    (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (hp : ∀ d ∈ p.support,
      (∑ i, w i * d i) ≤ ∑ i, w i * (Fintype.card (F i) - 1))
    (hc : p.coeff (PolynomialSums.topExponent F) ≠ 0) :
    HasNonzeroCellSum S n P Q chi := by
  classical
  let := Fintype.ofEquiv (∀ i, F i) e
  refine ⟨f, ?_⟩
  rw [finsum_eq_sum_of_fintype, ← e.sum_comp]
  simp only [heval]
  rw [PolynomialSums.grid_sum_eq_top_coefficient_of_weighted_bound F ι p w hw hp]
  exact mul_ne_zero hc (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid
