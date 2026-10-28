module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.HighestLine
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft.WeightNilpotence
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft.Duality
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft.DualHighestWeight
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity.PositivePrimitivesLeft.Opposition

/-!
# D4 positive primitives and joint nilpotence from negative cyclicity

Negative-root spanning from a left highest vector gives joint positive-word
nilpotence through finite integral torus weights. For an irreducible module
of nonzero basic highest weight, the pinned D4 opposition representative and
the actual rational dual's highest weight give a nondegenerate contravariant
form by checked highest-weight uniqueness. Root adjointness then identifies
the positive primitive space with the highest line.

The final theorem discharges opposition, dual highest weight and pairing
existence. Negative-root spanning remains its explicit hypothesis, to be
supplied by the root-density assembly.

Source: the infinitesimal argument underlying GLS3 Theorem 2.8.5 and Corollary
2.8.6(a), Steinberg (1963), §§2, 4 and 11.1; left-action conventions are those
of Steinberg (1968), equation (6.1) and §13.1.
-/

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
open PositivePrimitivesLeft

/-- Left highest-weight negative cyclicity implies genuine joint positive nilpotence. -/
theorem hasNilpotentPositiveAction_of_left_highWeight_negative_span (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {μ : Weight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding μ))
    (hspan : negativeRootSpan S ρ hρ v = ⊤) : HasNilpotentPositiveAction S ρ hρ :=
  hasNilpotentPositiveAction_of_negative_span S ρ hρ hv.2.2 hspan

/-- The two positive-action conclusions, retaining existence of the actual form. -/
theorem positivePrimitives_of_left_highWeight_contravariantPairing (S : D4Geometry K)
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    {μ : Weight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding μ))
    (hspan : negativeRootSpan S ρ hρ v = ⊤)
    (hpair : HasContravariantPairing S ρ hρ) :
    positiveRootKernel S ρ hρ = Submodule.span k {v} ∧ HasNilpotentPositiveAction S ρ hρ :=
  ⟨positiveRootKernel_eq_span_of_contravariantPairing S ρ hρ hv hspan hpair,
    hasNilpotentPositiveAction_of_left_highWeight_negative_span S ρ hρ hv hspan⟩

/-- Rational-duality assembly. Opposition and the genuine highest weight of
the rational dual remain explicit mathematical obligations. -/
theorem positivePrimitives_of_left_highWeight_opposition_dual [CharP k 2]
    (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsIrreducibleRepresentation ρ) (O : Opposition S)
    {μ : Weight} {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding μ))
    (hspan : negativeRootSpan S ρ hρ.1 v = ⊤)
    (hdual : ∃ f, HasHighWeight (dualRepresentation ρ hρ.1) S.borel S.torus f
      (S.leftWeightEmbedding μ)) :
    positiveRootKernel S ρ hρ.1 = Submodule.span k {v} ∧
      HasNilpotentPositiveAction S ρ hρ.1 :=
  positivePrimitives_of_left_highWeight_contravariantPairing S ρ hρ.1 hv hspan
    (pairing_of_dual_highWeight S ρ hρ O hv hdual)

/-- For a nonzero left basic highest weight, negative cyclicity implies both
the positive primitive-line equality and uniform vanishing of all sufficiently
long positive root-operator words. All duality and opposition inputs are proved. -/
theorem positivePrimitives_of_left_basic_negative_span [CharP k 2]
    (S : D4Geometry K) (ρ : RationalRepresentation K V)
    (hρ : IsIrreducibleRepresentation ρ) {a : BasicWeight}
    (ha : a ≠ fun _ => false) {v : V}
    (hv : HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding (coefficient a)))
    (hspan : negativeRootSpan S ρ hρ.1 v = ⊤) :
    positiveRootKernel S ρ hρ.1 = Submodule.span k {v} ∧
      HasNilpotentPositiveAction S ρ hρ.1 :=
  positivePrimitives_of_left_highWeight_opposition_dual S ρ hρ (opposition S) hv hspan
    (dualRepresentation_hasHighWeight_of_left_basic_negative_span S ρ hρ ha hv hspan
      (opposition S))

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity
