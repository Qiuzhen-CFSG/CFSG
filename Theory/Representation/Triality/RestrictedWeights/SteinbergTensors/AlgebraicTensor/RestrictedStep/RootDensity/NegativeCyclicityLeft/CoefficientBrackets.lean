module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.Triangular
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.CoefficientBrackets.Relations
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.CoefficientBrackets.ChevalleyExchanges
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.CoefficientBrackets.CartanClosure

/-!
# D4 root and Cartan coefficient brackets

For every finite-dimensional rational representation of the given D4 geometry
in characteristic two, positive-negative coefficient brackets belong to the
sum of the positive, Cartan and negative operator spaces. Simple Cartan brackets
with negative coefficients belong to the negative operator space.

The actual Chevalley relations give the simply laced root exchanges. Polynomial
comparison transfers them to exact nonopposite coefficient relations, while the
root-group law gives square-zero first coefficients. Jacobi and induction on
the D4 roots then put every opposite bracket in the simple Cartan span and
establish the Cartan commutation calculation. All coefficient premises are
discharged here, without a characteristic-zero differential or a highest-vector
assumption. These are the brackets used by the triangular word induction.

Sources: GLS3 §1.12, Theorem 2.8.5 and Corollary 2.8.6(a); Steinberg,
*Representations of Algebraic Groups* (1963), §§2 and 4.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The actual first root coefficients satisfy the exact nonopposite D4
relations in characteristic two. -/
theorem nonopposite_coefficient_relations (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ) :
    HasNonoppositeCoefficientRelations S ρ hρ :=
  nonopposite_coefficients_of_exchanges S ρ hρ (nonopposite_root_exchanges S)

/-- Every opposite-root coefficient bracket lies in the span of the four
simple Cartan brackets. -/
theorem opposite_commutator_mem_cartan (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α : S.roots.Root) :
    rootOperator S ρ hρ α * rootOperator S ρ hρ (S.roots.neg α) -
      rootOperator S ρ hρ (S.roots.neg α) * rootOperator S ρ hρ α ∈
        cartanOperators S ρ hρ :=
  opposite_commutator_mem_cartan_of_relations S ρ hρ
    (nonopposite_coefficient_relations S ρ hρ) α

/-- A positive-negative coefficient bracket belongs to the full triangular
operator sum, including the opposite-root case. -/
theorem positive_negative_commutator_mem (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (α β : PositiveRoot S) :
    rootOperator S ρ hρ α.val * rootOperator S ρ hρ (S.roots.neg β.val) -
      rootOperator S ρ hρ (S.roots.neg β.val) * rootOperator S ρ hρ α.val ∈
        nonnegativeOperators S ρ hρ ⊔ negativeOperators S ρ hρ :=
  positive_negative_commutator_mem_of_relations S ρ hρ
    (nonopposite_coefficient_relations S ρ hρ)
    (opposite_commutator_mem_cartan S ρ hρ) α β

/-- Bracketing a negative root coefficient with a simple Cartan operator
preserves the span of negative root coefficients. -/
theorem cartan_negative_commutator_mem (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (i : Fin 4) (β : PositiveRoot S) :
    cartanOperator S ρ hρ i * rootOperator S ρ hρ (S.roots.neg β.val) -
      rootOperator S ρ hρ (S.roots.neg β.val) * cartanOperator S ρ hρ i ∈
        negativeOperators S ρ hρ :=
  cartan_negative_commutator_mem_of_relations S ρ hρ
    (nonopposite_coefficient_relations S ρ hρ) i β

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft
