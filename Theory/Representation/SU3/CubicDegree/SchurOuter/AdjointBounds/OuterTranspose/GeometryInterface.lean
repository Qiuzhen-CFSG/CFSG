module

public import Theory.Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OperatorModels

/-!
# A geometric intertwiner for a central quotient of SU₃

This interface isolates a matrix-group obligation from the original binary
module. For a specified quotient map and automorphism, it asks for an operator
on the literal adjoint model which is conjugate to transpose and intertwines
every pair of representatives related by that automorphism. It makes no
assertion about the original normalizing operator or its scalar ambiguity.

Outer-involution normal form, unitary descent, and Hermitian basis transport
must construct this witness. The scalar-rigidity consumer then compares it
with the actual operator through the given adjoint representation equivalence.

Source: Guralnick--Malle, Classification of 2F-modules II, Proposition 4.11,
internal pp.31--32.
-/

public section
open BenderSuzuki.MatrixGroups Representation
open Representation.SL3.BinaryDefiningFactors

namespace Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose
variable {F K H : Type*} [Field F] [Field K] [Group H]

/-- A transpose-conjugate operator on the adjoint model implementing the
specified automorphism of a quotient, on actual matrix representatives. -/
@[expose] def AdjointGraphIntertwiner (J : HermitianForm 3 F) (ι : F →+* K)
    (p : J.specialSubgroup →* H) (α : MulAut H) : Prop :=
  ∃ S : AdjointSpace K ≃ₗ[K] AdjointSpace K,
    IsTransposeOperator (K := K) (W := AdjointSpace K) S.toLinearMap ∧
      ∀ g h : J.specialSubgroup, p h = α (p g) →
        S.toLinearMap * adjoint J ι g = adjoint J ι h * S.toLinearMap

end Representation.SU3.CubicDegree.SchurOuter.AdjointBounds.OuterTranspose
