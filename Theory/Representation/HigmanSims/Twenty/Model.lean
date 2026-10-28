module

public import Theory.Representation.HigmanSims.Twenty.Absolute
public import Theory.Representation.HigmanSims.Twenty.Comparison
public import Theory.Representation.Quotient

/-!
# The concrete absolutely irreducible HS twenty-space

The checked permutation-module construction supplies a marked homomorphism
from the literal degree-100 HS carrier onto the group of the published
degree-twenty matrices. Pulling back the matrix representation gives the
named action below. Surjectivity transports the proved absolute
irreducibility, including the tensor-product scalar extension.

With simplicity inherited from a source application, the nontrivial image
makes the marked homomorphism an isomorphism and the action faithful. The
generator equations retain the published matrices without a transpose or
inverse.

Source: ATLAS HSG1-p100B0 and HSG1-f2r20B0; the original matrix data and
checked certificate provenance are preserved in `Twenty/source/`.
-/

public section
namespace Sporadic.LeechRelated.HS.Twenty
noncomputable section

/-- The published twenty-dimensional action on the actual HS carrier. -/
@[expose] def carrierRepresentation : Representation (ZMod 2) HS.Carrier Vector :=
  Comparison.markedComparison.action

/-- The actual marked carrier isomorphism, using inherited simplicity. -/
@[expose] def carrierEquiv [IsSimpleGroup HS.Carrier] : HS.Carrier ≃* MatrixCarrier :=
  Comparison.markedComparison.equiv

theorem carrierEquiv_a [IsSimpleGroup HS.Carrier] : carrierEquiv permutationA = a :=
  Comparison.markedComparison.map_a

theorem carrierEquiv_b [IsSimpleGroup HS.Carrier] : carrierEquiv permutationB = b :=
  Comparison.markedComparison.map_b

theorem carrierRepresentation_eq [IsSimpleGroup HS.Carrier] (g : HS.Carrier) :
    carrierRepresentation g = representation (carrierEquiv g) := rfl

theorem carrierRepresentation_a :
    carrierRepresentation permutationA = Matrix.toLinAlgEquiv' aMatrix := by
  change representation (Comparison.markedComparison.hom permutationA) = _
  rw [Comparison.markedComparison.map_a]
  rfl

theorem carrierRepresentation_b :
    carrierRepresentation permutationB = Matrix.toLinAlgEquiv' bMatrix := by
  change representation (Comparison.markedComparison.hom permutationB) = _
  rw [Comparison.markedComparison.map_b]
  rfl

theorem carrierRepresentation_injective [IsSimpleGroup HS.Carrier] :
    Function.Injective carrierRepresentation :=
  Comparison.markedComparison.action_injective

/-- Absolute irreducibility uses the constructed surjection and needs no
simplicity assumption. -/
theorem carrierRepresentation_absolutelyIrreducible :
    carrierRepresentation.IsAbsolutelyIrreducible := by
  constructor
  change Representation.IsIrreducible
    ((Representation.extendScalars (AlgebraicClosure (ZMod 2)) representation).comp
      Comparison.markedComparison.hom)
  exact (Representation.irreducible_comp_surjective_iff
    Comparison.markedComparison.hom Comparison.markedComparison.surjective _).mpr
    absolutelyIrreducible.irreducible_of_closure

end
end Sporadic.LeechRelated.HS.Twenty
