module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.LeftWeights
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep.RootDensity

/-!
# The corrected restricted root-density obligation

Nonzero binary weights are required at the left embedding. This predicate
specifies the remaining density theorem and does not prove it. The independent
zero-weight proof survives the change of coordinates by neg_zero, without
using the raw orientation obstruction to remove any nonzero case.
Source: Steinberg §13.1, used in GLS3 2.8.5--6.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open Theory.AlgebraicGroup.StandardRootSystem.D4RestrictedWeight
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k 2]
variable {K : Variety k} [AlgebraicGroup K]

/-- Density on each actual binary rational factor, including all nonzero digits. -/
def LeftRestrictedRootDensity (S : D4Geometry K) : Prop :=
  ∀ (A : RationalFactor K) (a : BasicWeight),
    (∃ v, HasHighWeight A.action S.borel S.torus v (S.leftWeightEmbedding (coefficient a))) →
      RestrictedStep.rootOperatorAlgebra S A.action A.irreducible.1 = ⊤

omit [CharP k 2] in
/-- Only the zero branch is discharged by the existing independent line proof. -/
theorem rootOperatorAlgebra_eq_top_of_leftZeroHighWeight (S : D4Geometry K)
    {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : RationalRepresentation K V) (hρ : IsIrreducibleRepresentation ρ)
    (hv : ∃ v, HasHighWeight ρ S.borel S.torus v (S.leftWeightEmbedding 0)) :
    RestrictedStep.rootOperatorAlgebra S ρ hρ.1 = ⊤ := by
  apply RestrictedStep.rootOperatorAlgebra_eq_top_of_zero_highWeight S ρ hρ
  simpa only [S.leftWeightEmbedding_eq_raw, neg_zero] using hv

end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor
