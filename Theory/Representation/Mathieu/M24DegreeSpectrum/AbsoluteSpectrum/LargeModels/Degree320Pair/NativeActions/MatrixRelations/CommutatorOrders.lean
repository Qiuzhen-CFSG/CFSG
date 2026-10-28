module

public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.VariantA
public import Theory.Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.NativeActions.MatrixRelations.CommutatorOrders.VariantB

/-!
# The two degree-320 ATLAS commutator relations

For both literal, untransposed matrix pairs, direct packed multiplication proves
(AB²AB)¹² = 1 and (AB²AB²ABAB)⁵ = 1. These are exactly clauses 3 and 4 of the
shared row presentation. The source inverse elimination is established there;
these certificates do not assume a representation or presentation comparison.

Source: John Bray, ATLAS M24G1-P1. See CommutatorOrders/source/README.md for
reproduction, attribution, and complete-check measurements.
-/

public section
namespace Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate

/-- The twelfth-power commutator relation for each literal ATLAS matrix pair. -/
theorem commutator_order12 (variant : Bool) :
    (matrixA variant * matrixB variant ^ 2 * matrixA variant * matrixB variant) ^ 12 = 1 := by
  cases variant
  · exact CommutatorOrders.commutator_false
  · exact CommutatorOrders.commutator_true

/-- The fifth-power second commutator relation for each literal ATLAS matrix pair. -/
theorem second_commutator_order5 (variant : Bool) :
    (matrixA variant * matrixB variant ^ 2 * matrixA variant * matrixB variant ^ 2 *
      matrixA variant * matrixB variant * matrixA variant * matrixB variant) ^ 5 = 1 := by
  cases variant
  · exact CommutatorOrders.second_commutator_false
  · exact CommutatorOrders.second_commutator_true

/-- Discharge the literal zero-based source clause 3. -/
theorem rowRelatorValues_three (variant : Bool) :
    Degrees12421792.NativeActions.Presentation.rowRelatorValues
      (matrixA variant) (matrixB variant) 3 = 1 :=
  commutator_order12 variant

/-- Discharge the literal zero-based source clause 4. -/
theorem rowRelatorValues_four (variant : Bool) :
    Degrees12421792.NativeActions.Presentation.rowRelatorValues
      (matrixA variant) (matrixB variant) 4 = 1 :=
  second_commutator_order5 variant

end Representation.Mathieu.M24DegreeSpectrum.AbsoluteSpectrum.LargeModels.Degree320Pair.MatrixRelationCertificate
