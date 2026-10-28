module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.HighestLine
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.Cyclic
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.CartanHighest
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.Conjugation
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.NegativeCyclicityLeft.CoefficientBrackets
/-!
# Negative cyclicity from actual D4 coefficient identities

The torus and signed simple roots generate the actual point group. The
root algebra is normalized by that group, so the restricted simple strings make
its highest-vector cyclic submodule group-invariant, hence full. Independently,
triangular bracket identities place that cyclic submodule inside the negative
word span. The simple Cartan eigenvalues needed for this step are proved from
the actual Weyl words and the left highest-string calculation.

The final theorem discharges root-algebra normalization and both whole-module
bracket containments using the actual characteristic-two coefficient identities.
It proves negative cyclicity uniformly for every binary weight, including all
fifteen nonzero ones. The conditional reduction is retained as a reusable API.
No unique-positive-primitive or differential-irreducibility premise is used.

Source: Steinberg, *Representations of Algebraic Groups* (1963), §§2 and 4;
the infinitesimal argument underlying GLS3 Theorem 2.8.5 and Corollary 2.8.6(a).
The Borel and raw root words are unchanged, and weights use `E_left(a)=E_raw(-a)`.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
open NegativeCyclicityLeft

/-- Actual normalization and triangular coefficient relations imply negative
cyclicity for any restricted left highest weight. The three coefficient
premises must still be proved before this yields unconditional cyclicity. -/
theorem negativeRootSpan_eq_top_of_left_basic_highWeight_of_coefficient_relations
    (S : D4Geometry K) (ρ : RationalRepresentation K V) (hρ : IsIrreducibleRepresentation ρ)
    {a : BasicWeight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding (coefficient a)))
    (hnorm : RootConjugationStable S ρ hρ.1)
    (hroot : ∀ α β : PositiveRoot S,
      rootOperator S ρ hρ.1 α.val * rootOperator S ρ hρ.1 (S.roots.neg β.val) -
        rootOperator S ρ hρ.1 (S.roots.neg β.val) * rootOperator S ρ hρ.1 α.val ∈
          nonnegativeOperators S ρ hρ.1 ⊔ negativeOperators S ρ hρ.1)
    (hcartan : ∀ i, ∀ β : PositiveRoot S,
      cartanOperator S ρ hρ.1 i * rootOperator S ρ hρ.1 (S.roots.neg β.val) -
        rootOperator S ρ hρ.1 (S.roots.neg β.val) * cartanOperator S ρ hρ.1 i ∈
          negativeOperators S ρ hρ.1) :
    negativeRootSpan S ρ hρ.1 v = ⊤ := by
  have hU : IsRootOperatorInvariant S ρ hρ.1 (negativeRootSpan S ρ hρ.1 v) := by
    apply rootOperatorInvariant_of_triangular_commutators S ρ hρ.1 hv _ hroot hcartan
    intro i
    rw [cartanOperator_on_highest S ρ hρ.1 hv i]
    exact (Submodule.span k {v}).smul_mem _ (Submodule.subset_span (Set.mem_singleton v))
  apply top_unique
  exact (cyclicRootSpan_eq_top_of_conjugation S ρ hρ hv hnorm).ge.trans
    (cyclicRootSpan_le S ρ hρ.1 v _ hU (mem_negativeRootSpan S ρ hρ.1 v))

/-- A restricted left highest vector generates its entire irreducible rational
representation under words in the actual negative first root coefficients.
This holds for every binary weight, including all fifteen nonzero weights,
with no additional coefficient or primitive-line hypotheses. -/
theorem negativeRootSpan_eq_top_of_left_basic_highWeight
    (S : D4Geometry K) (ρ : RationalRepresentation K V) (hρ : IsIrreducibleRepresentation ρ)
    {a : BasicWeight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding (coefficient a))) :
    negativeRootSpan S ρ hρ.1 v = ⊤ :=
  negativeRootSpan_eq_top_of_left_basic_highWeight_of_coefficient_relations S ρ hρ hv
    (root_conjugation_stable S ρ hρ.1)
    (positive_negative_commutator_mem S ρ hρ.1)
    (cartan_negative_commutator_mem S ρ hρ.1)
end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
