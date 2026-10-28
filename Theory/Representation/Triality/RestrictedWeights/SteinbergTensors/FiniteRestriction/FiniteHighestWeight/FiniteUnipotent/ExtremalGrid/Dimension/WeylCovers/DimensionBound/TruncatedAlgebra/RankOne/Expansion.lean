module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws
/-!
# Finite polynomial expansions of root actions

A finite basis bounds the degrees of all matrix entries of a rational root
curve. Taking the largest of these degrees gives an operator-valued polynomial
expansion and vanishing of all subsequent coefficients. The bound depends on
the representation; it is not a restricted-weight or characteristic-power
bound. This supplies finite sums for the rank-one Gauss calculations.

Source: polynomiality of rational additive-group actions, as used in
Steinberg, Representations of algebraic groups (1963), §§2–3.
-/

public noncomputable section
open Theory.AlgebraicGroup
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
open AlgebraicTensor.RestrictedStep
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Polynomiality supplies a finite expansion; the bound depends on the
representation and is not asserted to be smaller than a characteristic power. -/
theorem rankOne_curveCoefficient_expansion (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x : Morphism (KPlus k) K) :
    ∃ N : ℕ, (∀ j, N ≤ j → curveCoefficient rho hr x j = 0) ∧
      ∀ t : k, (rho.action (x.onPoints (kPlusPoint t))).val =
        ∑ j ∈ Finset.range N, t ^ j • curveCoefficient rho hr x j := by
  classical
  let b := Module.finBasis k V
  let p := fun ij : Fin (Module.finrank k V) × Fin (Module.finrank k V) =>
    curvePolynomial rho hr x (b.coord ij.1) (b ij.2)
  let N := Finset.univ.sup (fun ij => (p ij).natDegree) + 1
  have hN (i j : Fin (Module.finrank k V)) : (p (i, j)).natDegree < N := by
    exact Nat.lt_succ_of_le (Finset.le_sup (f := fun ij => (p ij).natDegree) (Finset.mem_univ (i, j)))
  refine ⟨N, ?_, ?_⟩
  · intro j hj
    apply b.ext
    intro a
    apply b.repr.injective
    ext i
    simp only [LinearMap.zero_apply, map_zero, Finsupp.zero_apply]
    change (b.coord i) (curveCoefficient rho hr x j (b a)) = 0
    rw [dual_curveCoefficient]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_lt_of_le (hN i a) hj)
  · intro t
    apply b.ext
    intro a
    apply b.repr.injective
    ext i
    change (b.coord i) ((rho.action (x.onPoints (kPlusPoint t))).val (b a)) = _
    rw [← curvePolynomial_eval]
    change (p (i, a)).eval t = (b.coord i) ((∑ j ∈ Finset.range N,
      t ^ j • curveCoefficient rho hr x j) (b a))
    rw [Polynomial.eval_eq_sum, Polynomial.sum_over_range' _ (f := fun j c => c * t ^ j) (fun j => zero_mul (t ^ j)) N (hN i a)]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      dual_curveCoefficient, smul_eq_mul, mul_comm]
    rfl

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
