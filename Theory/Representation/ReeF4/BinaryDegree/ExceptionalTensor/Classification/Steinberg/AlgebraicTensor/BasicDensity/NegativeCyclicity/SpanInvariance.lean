module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.Basic
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Triangular
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Weyl
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Cartan
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Nonopposite

/-!
# Root-operator invariance of the negative short-word span

The highest strings determine the simple Cartan action on the highest vector.
Triangular commutation then proves positive-root stability, and Weyl closure
and reflection induction prove stability under every root coefficient.

The actual carrier exchanges and the faithful tangent transfer establish the
nonopposite, opposite short-root, and simple Cartan coefficient identities.
They discharge every commutator premise in the final theorem, which proves
invariance under all first-degree root operators. No differential
irreducibility or short-root density is required. Equality with the whole
factor is the separate cyclicity step in Steinberg 11.1(1).

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §§2, 4 and the first part of 11.1(1), pp. 52–53;
DOI 10.1017/S0027763000011016.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F] [CharP F 2]
local instance spanInvarianceAssemblyNeg : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg

namespace NegativeCyclicity.SpanInvariance

/-- Triangular identities for actual coefficients imply full root-operator
invariance; the simple Cartan action on the highest vector is proved here. -/
theorem rootOperatorInvariant_of_triangular_commutators {B : AlgebraicFactor F}
    (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v)
    (hroot : ∀ r : PositiveRoot, ∀ s : ShortNegativeRoot,
      p.coeff r.val 1 * p.coeff s.val 1 - p.coeff s.val 1 * p.coeff r.val 1 ∈
        nonnegativeOperators p ⊔ negativeOperators p)
    (hcartan : ∀ i, ∀ s : ShortNegativeRoot,
      cartanOperator p i * p.coeff s.val 1 - p.coeff s.val 1 * cartanOperator p i ∈
        negativeOperators p) :
    p.IsRootOperatorInvariant (p.shortNegativeSpan v) := by
  apply rootOperatorInvariant_of_positive_stable p hv
  apply positive_stable_of_commutators p hv _ hroot hcartan
  intro i
  change (p.coeff (typeF4SimpleRootIndex i) 1 * p.coeff (-typeF4SimpleRootIndex i) 1 -
    p.coeff (-typeF4SimpleRootIndex i) 1 * p.coeff (typeF4SimpleRootIndex i) 1) v ∈ _
  rw [simple_cartan_on_highest p hv]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton v))

/-- Separate the nonopposite root brackets from the opposite-root and Cartan
identities. All hypotheses concern the actual first coefficients, and none
assumes invariance of the negative word span. -/
theorem rootOperatorInvariant_of_chevalley_relations {B : AlgebraicFactor F}
    (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v)
    (hnonopp : ∀ r : PositiveRoot, ∀ s : ShortNegativeRoot, s.val ≠ -r.val →
      p.coeff r.val 1 * p.coeff s.val 1 - p.coeff s.val 1 * p.coeff r.val 1 ∈
        positiveOperators p ⊔ negativeOperators p)
    (hopp : ∀ r : ShortPositiveRoot,
      p.coeff r.val 1 * p.coeff (-r.val) 1 - p.coeff (-r.val) 1 * p.coeff r.val 1 ∈
        cartanOperators p)
    (hcartan : ∀ i, ∀ s : ShortNegativeRoot,
      cartanOperator p i * p.coeff s.val 1 - p.coeff s.val 1 * cartanOperator p i ∈
        negativeOperators p) :
    p.IsRootOperatorInvariant (p.shortNegativeSpan v) := by
  apply rootOperatorInvariant_of_triangular_commutators p hv _ hcartan
  intro r s
  by_cases he : s.val = -r.val
  · have hr : ¬ IsLongRoot r.val := (isShortRoot_neg_iff r.val).mp (by
      rw [← he]
      exact s.property.1)
    rw [he]
    exact (show cartanOperators p ≤ nonnegativeOperators p ⊔ negativeOperators p from
      le_trans le_sup_right le_sup_left) (hopp ⟨r.val, hr, r.property⟩)
  · exact (show positiveOperators p ⊔ negativeOperators p ≤
        nonnegativeOperators p ⊔ negativeOperators p from sup_le_sup le_sup_left le_rfl)
      (hnonopp r s he)

end NegativeCyclicity.SpanInvariance

/-- Every first-degree root operator preserves the span of negative short-root
words on a basic highest vector, including the empty word. This also holds for
the zero basic weight. -/
theorem RootExpansion.isRootOperatorInvariant_shortNegativeSpan {B : AlgebraicFactor F}
    (p : RootExpansion B.action) {b : BasicWeight} {v : B.Space}
    (hv : B.IsBasicHighestWeightVector b v) :
    p.IsRootOperatorInvariant (p.shortNegativeSpan v) := by
  exact NegativeCyclicity.SpanInvariance.rootOperatorInvariant_of_chevalley_relations p hv
    (NegativeCyclicity.SpanInvariance.nonopposite_commutator_mem p)
    (NegativeCyclicity.SpanInvariance.opposite_short_commutator_mem_cartan p)
    (NegativeCyclicity.SpanInvariance.cartan_commutator_mem_negative p)

end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
