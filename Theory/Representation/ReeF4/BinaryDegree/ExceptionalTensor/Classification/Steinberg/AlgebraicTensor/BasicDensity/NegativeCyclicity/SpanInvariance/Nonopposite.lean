module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Triangular
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Nonopposite.PolynomialTransfer
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Nonopposite.RootRelations

/-!
# Nonopposite commutators from actual carrier exchanges

The polynomial transfer compares actual representation coefficients in the
two root parameters. Its output is zero or the coefficient of the short sum
root. A short root is either positive or negative, so its coefficient belongs
to the sum of the two operator spaces used by the triangular word induction.

The group collection input remains explicit. In particular, this module does
not yet assert the unconditional nonopposite commutator theorem: that requires
constructing `Nonopposite.ShortRootExchange` for each nonopposite pair in the
actual algebraic carrier, including the vanishing long-sum branch.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §§2, 4, 10 and the first part of 11.1(1);
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
namespace NegativeCyclicity.SpanInvariance
noncomputable section

variable {F : Type*} [Field F] [IsAlgClosed F]
local instance nonoppositeSpanInvarianceNeg : InvolutiveNeg F4Chevalley.Root :=
  typeF4RootPairing.indexNeg

/-- Each actual short-root coefficient belongs to one of the two triangular
operator spaces. -/
theorem short_coeff_mem_positive_sup_negative {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (t : F4Chevalley.Root) (ht : ¬ IsLongRoot t) :
    p.coeff t 1 ∈ positiveOperators p ⊔ negativeOperators p := by
  by_cases hp : typeF4RootPairing_base.IsPos t
  · exact (show positiveOperators p ≤ positiveOperators p ⊔ negativeOperators p from
      le_sup_left) (Submodule.subset_span ⟨⟨t, hp⟩, rfl⟩)
  · exact (show negativeOperators p ≤ positiveOperators p ⊔ negativeOperators p from
      le_sup_right) (Submodule.subset_span ⟨⟨t, ht, hp⟩, rfl⟩)

/-- Genuine carrier collection implies the desired containment for actual
representation coefficients, without a highest-weight assumption. The
nonopposite root relation itself is a separate prerequisite. -/
theorem nonopposite_commutator_mem_of_root_exchange {B : AlgebraicFactor F}
    (p : RootExpansion B.action) (r : PositiveRoot) (s : ShortNegativeRoot)
    (h : Nonopposite.ShortRootExchange (F := F) r.val s.val) :
    p.coeff r.val 1 * p.coeff s.val 1 - p.coeff s.val 1 * p.coeff r.val 1 ∈
      positiveOperators p ⊔ negativeOperators p := by
  rcases Nonopposite.coeff_commutator_short_or_zero p r.val s.val h with
    hz | ⟨t, ht, _hsum, he⟩
  · rw [hz]
    exact Submodule.zero_mem _
  · rw [he]
    exact short_coeff_mem_positive_sup_negative p t ht

/-- Every nonopposite positive/negative-short pair has its actual coefficient
commutator in the triangular operator sum. -/
theorem nonopposite_commutator_mem {F : Type*} [Field F] [IsAlgClosed F] [CharP F 2]
    {B : AlgebraicFactor F} (p : RootExpansion B.action) (r : PositiveRoot)
    (s : ShortNegativeRoot) (hne : s.val ≠ -r.val) :
    p.coeff r.val 1 * p.coeff s.val 1 - p.coeff s.val 1 * p.coeff r.val 1 ∈
      positiveOperators p ⊔ negativeOperators p := by
  exact nonopposite_commutator_mem_of_root_exchange p r s
    (Nonopposite.nonopposite_root_exchange r s hne)

end
end NegativeCyclicity.SpanInvariance
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
