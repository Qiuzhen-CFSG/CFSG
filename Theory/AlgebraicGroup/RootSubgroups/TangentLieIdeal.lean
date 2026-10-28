module

public import Theory.AlgebraicGroup.Bor1.RepresentationDifferentialSubspace
public import Theory.AlgebraicGroup.RootSubgroups.TangentAdjoint

/-!
# Conjugation invariance of tangent Lie ideals

Over an algebraically closed field of characteristic zero, every Lie ideal in
the canonical identity tangent Lie algebra of a connected algebraic group is
preserved by conjugation by every group point.

The tangent conjugation representation is rational, and its identity
differential sends `D` to the adjoint operator `E \mapsto [D,E]`.  The bracket
orientation comes from the convolution formula `D * E - E * D`.  Hence a Lie
ideal is stable under every infinitesimal representation operator.  The
characteristic-zero subspace-integration theorem applies the closed
general-linear stabilizer, full-tangent/dimension, and connectedness argument
to promote this infinitesimal stability to pointwise conjugation invariance.
This is the standard adjoint-integration principle and uses no root-subgroup
classification or clause of GLS3 Theorem 1.9.5.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]

/-- Every Lie ideal of the canonical identity tangent Lie algebra of a
connected algebraic group is preserved by each point-conjugation operator. -/
public theorem LieIdeal.identityTangentConjugationLinearMap_mem
    (G : Variety k) [AlgebraicGroup G]
    (I : LieIdeal k (IdentityPointDerivation G))
    (hG : Variety.IsConnected G) (g : G.Point)
    {D : IdentityPointDerivation G} (hD : D ∈ I) :
    identityTangentConjugationLinearMap G g D ∈ I := by
  obtain ⟨b, f, hf⟩ := identityTangentRepresentation_isRational G
  have hI : IsInvariantSubmodule (identityTangentRepresentation G) I.toSubmodule :=
    Bor1.differential_stable_subspace_invariant
      (identityTangentRepresentation G) b f hf I.toSubmodule hG (by
        intro X Y hY
        rw [identityTangentRepresentation_differential_apply G b f hf]
        exact I.lie_mem hY)
  have haction :
      (((identityTangentRepresentation G).action g).1 D) =
        identityTangentConjugationLinearMap G g D := by
    apply Derivation.ext
    intro a
    rw [identityTangentRepresentation_action_apply,
      identityTangentConjugationLinearMap_apply]
  rw [← haction]
  exact hI g D hD

end Theory.AlgebraicGroup
