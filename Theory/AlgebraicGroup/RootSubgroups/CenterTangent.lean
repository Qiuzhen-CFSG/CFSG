module

public import Theory.AlgebraicGroup.Bor1.CentralizerDifferential

/-!
# The algebraic center tangent

Over an algebraically closed field of characteristic zero, this module
identifies the canonical tangent Lie algebra of the identity component of a
connected algebraic group's center with the center of the ambient tangent Lie
algebra.  The forward inclusion differentiates centrality.  For the reverse
inclusion, characteristic-zero centralizer differential exactness and
identity-component tangent surjectivity lift every pointwise adjoint-fixed
tangent through the center; connected adjoint-fixed tangent integration then
identifies those fixed tangents with the Lie center.

This is the Lie-algebra form of the center case of Bor1 Chapter 3, Sections
9.1--9.2.  Connectedness is essential: a disconnected semidirect product can
act nontrivially on the tangent of its identity component while having an
abelian identity-component Lie algebra.  No root-subgroup classification
theorem is used.

-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

/-- For a connected algebraic group in characteristic zero, the range of the
canonical tangent Lie map from the identity component of the algebraic center
is the center of the ambient canonical tangent Lie algebra. -/
public theorem identityComponentCenterTangent_range_eq_lieCenter
    {G : Variety k} [AlgebraicGroup G] (hG : Variety.IsConnected G) :
    (identityTangentMorphismLieHom
        (ClosedSubgroup.top (G := G)).centralizer.identityComponentAmbient.inclusion).range =
      LieAlgebra.center k (IdentityPointDerivation G) := by
  have htangent : Bor1.identityTangentMorphismLinearMap
      (ClosedSubgroup.top (G := G)).centralizer.identityComponentAmbient.inclusion =
      (identityTangentMorphismLieHom
        (ClosedSubgroup.top (G := G)).centralizer.identityComponentAmbient.inclusion).toLinearMap :=
    rfl
  apply le_antisymm
  · intro D hD
    have hDcentralizer : D ∈ LinearMap.range
        (Bor1.identityTangentMorphismLinearMap
          (ClosedSubgroup.top (G := G)).centralizer.identityComponentAmbient.inclusion) := by
      rw [htangent]
      exact hD
    rw [Bor1.identityComponentCenterTangent_range_eq_lieCenter hG]
      at hDcentralizer
    exact hDcentralizer
  · intro D hD
    have hDcentralizer : D ∈ LinearMap.range
        (Bor1.identityTangentMorphismLinearMap
          (ClosedSubgroup.top (G := G)).centralizer.identityComponentAmbient.inclusion) := by
      rw [Bor1.identityComponentCenterTangent_range_eq_lieCenter hG]
      exact hD
    rw [htangent] at hDcentralizer
    exact hDcentralizer

end Theory.AlgebraicGroup
