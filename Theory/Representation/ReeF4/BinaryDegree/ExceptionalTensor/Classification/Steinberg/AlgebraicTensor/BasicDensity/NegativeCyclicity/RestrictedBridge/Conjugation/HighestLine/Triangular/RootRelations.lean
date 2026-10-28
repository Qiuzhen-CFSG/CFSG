module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.HighestLine.Triangular.Spanning
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.RestrictedBridge.Conjugation.HighestLine.Triangular.MatrixRelations

/-!
# Actual quotient root commutators lie in the root and Cartan span

The concrete adjoint identity lifts through the injective differential of the
closed matrix inclusion. The differential of the given rational representation
sends root tangents to its canonical first root operators. The resulting
identity in the generated root algebra then passes through its actual action
on the simple quotient. No rational action on the quotient is assumed.

Source: Steinberg, *Representations of Algebraic Groups*, Nagoya Math. J.
22 (1963), §2, structure equations 2.1–2.6;
DOI 10.1017/S0027763000011016.
-/

public section
set_option backward.isDefEq.respectTransparency false
open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
open scoped Matrix
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
open SpanInvariance.CartanTransfer Geometry.ExceptionalMorphism
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]
local instance : InvolutiveNeg F4Chevalley.Root := typeF4RootPairing.indexNeg
attribute [local instance] LieRing.ofAssociativeRing

namespace HighestLine

private def coordinateTangent : F4Chevalley.BasisIndex →
    IdentityPointDerivation (F4Chevalley.Carrier (k := F))
  | Sum.inr r => rootTangent r
  | Sum.inl i => ⁅rootTangent (F := F) (i : F4Chevalley.Root),
      rootTangent (F := F) (-i : F4Chevalley.Root)⁆

private theorem matrixDifferential_coordinateTangent (j : F4Chevalley.BasisIndex) :
    matrixDifferential (coordinateTangent (F := F) j) = coordinateOperator (K := F) j := by
  cases j with
  | inr r =>
    rw [coordinateTangent, matrixDifferential_rootTangent]
    rfl
  | inl i =>
    rw [coordinateTangent, LieHom.map_lie, matrixDifferential_rootTangent,
      matrixDifferential_rootTangent, Ring.lie_def,
      F4Chevalley.integralOperators.operator_simple,
      F4Chevalley.integralOperators.operator_neg_simple]
    rfl

private theorem tangent_bracket [CharP F 2] (r s : F4Chevalley.Root) :
    ⁅rootTangent (F := F) r, rootTangent (F := F) s⁆ =
      ∑ j, (coordinateOperator (K := F) (Sum.inr r) *ᵥ Pi.single (Sum.inr s) 1) j •
        coordinateTangent j := by
  apply matrixDifferential_injective
  simp only [LieHom.map_lie, matrixDifferential_rootTangent, map_sum, map_smul,
    matrixDifferential_coordinateTangent, Ring.lie_def]
  exact TriangularMatrices.root_commutator_eq_adjoint r s

private def coordinateGenerator (B : AlgebraicFactor F) : F4Chevalley.BasisIndex → rootAlgebra B
  | Sum.inr r => rootGenerator B r
  | Sum.inl i => rootGenerator B i * rootGenerator B (-i) -
      rootGenerator B (-i) * rootGenerator B i

private theorem coefficient_coordinateTangent {B : AlgebraicFactor F}
    (d : IdentityPointDerivation (F4Chevalley.Carrier (k := F)) →ₗ⁅F⁆ Module.End F B.Space)
    (hd : ∀ r, d (rootTangent r) = EndNode.Multiplicity.rootOperator B r)
    (j : F4Chevalley.BasisIndex) :
    d (coordinateTangent j) = (coordinateGenerator B j : Module.End F B.Space) := by
  cases j with
  | inr r => exact hd r
  | inl i => simp only [coordinateTangent, LieHom.map_lie, hd, Ring.lie_def]; rfl

private theorem generator_bracket [CharP F 2] (B : AlgebraicFactor F)
    (r s : F4Chevalley.Root) :
    rootGenerator B r * rootGenerator B s - rootGenerator B s * rootGenerator B r =
      ∑ j, (coordinateOperator (K := F) (Sum.inr r) *ᵥ Pi.single (Sum.inr s) 1) j •
        coordinateGenerator B j := by
  obtain ⟨p⟩ := rootExpansion_nonempty B.action B.irreducible.1
  obtain ⟨d, hd⟩ := exists_coefficient_lieHom p
  have hd' (r : F4Chevalley.Root) : d (rootTangent r) = EndNode.Multiplicity.rootOperator B r :=
    (hd r).trans (p.coeff_one_eq_rootOperator r)
  apply Subtype.ext
  change _ = (rootAlgebra B).val _
  rw [map_sum]
  have he := congrArg d (tangent_bracket (F := F) r s)
  simpa only [LieHom.map_lie, hd', Ring.lie_def, map_sum, map_smul,
    coefficient_coordinateTangent d hd', Subalgebra.coe_sub, Subalgebra.coe_mul,
    rootGenerator, Subalgebra.coe_smul, Subalgebra.val_apply] using he

end HighestLine

namespace SimpleCyclicQuotient
variable {B : AlgebraicFactor F} {v : B.Space} (Q : SimpleCyclicQuotient B v)

private theorem rootAction_coordinateGenerator_mem (j : F4Chevalley.BasisIndex) :
    Q.rootAction (HighestLine.coordinateGenerator B j) ∈ Q.rootCartanSpan := by
  cases j with
  | inr r =>
    change Q.operator r ∈ Q.rootCartanSpan
    exact Submodule.subset_span (Or.inl ⟨r, rfl⟩)
  | inl i =>
    obtain ⟨i, rfl⟩ := typeF4RootPairing_baseEquiv.surjective i
    have he : Q.rootAction (HighestLine.coordinateGenerator B
        (Sum.inl (typeF4RootPairing_baseEquiv i))) = Q.cartanOperator i := by
      simp only [HighestLine.coordinateGenerator, map_sub, map_mul,
        Q.rootAction_rootGenerator, cartanOperator, typeF4RootPairing_baseEquiv_val]
    rw [he]
    exact Submodule.subset_span (Or.inr ⟨i, rfl⟩)

/-- All actual quotient root brackets are linear combinations of roots and
simple Cartan operators, including brackets of opposite roots. -/
theorem operator_commutator_mem_rootCartanSpan [CharP F 2] (r s : F4Chevalley.Root) :
    Q.operator r * Q.operator s - Q.operator s * Q.operator r ∈ Q.rootCartanSpan := by
  have he := congrArg Q.rootAction (HighestLine.generator_bracket B r s)
  simp only [map_sub, map_mul, map_sum, map_smul, Q.rootAction_rootGenerator] at he
  rw [he]
  exact Q.rootCartanSpan.sum_mem fun j _ =>
    Q.rootCartanSpan.smul_mem _ (Q.rootAction_coordinateGenerator_mem j)

end SimpleCyclicQuotient
end
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.NegativeCyclicity.RestrictedBridge
