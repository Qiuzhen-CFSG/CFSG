module

public import Theory.Representation.MathieuCodeRestriction.CocodeLocal.PairResidual

/-!
# H.15.1: stabilizers and displacement at native Mathieu cocode pairs

The native weight-two stabilizers are isomorphic to MulAut M22 and M22,
respectively. These are also the literal displacement-span assertions for
the native M24 and M23 eleven-dimensional cocodes. The stronger assertions retain the actual
solvable residual of the vector stabilizer, mapped by its subtype map.
Their proofs use the perfect embedded M22, the Golay minimum distance, and
code--cocode duality; they assume neither irreducibility nor nonsplitting.

Source: Aschbacher--Smith, combined manuscript of 1 March 2004, H.15.1(1)--(2),
printed p.398, and its use with the perfect residual in 8.1.1, printed p.712.
-/

public section
namespace CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
open MathieuCode Representation.BinaryOffender

/-- H.15.1(1): the native M24 vector stabilizer is Aut(M22). -/
theorem m24_pair_stabilizer {v : Cocode} (hv : v ∈ weightTwoOrbit) :
    Nonempty (cocodeVectorStabilizer cocodeRepresentation v ≃*
      MulAut Sporadic.Mathieu.M22) :=
  weightTwoOrbit_stabilizer_equiv hv

/-- H.15.1(1): the native M23 vector stabilizer is M22. -/
theorem m23_pair_stabilizer {v : Cocode} (hv : v ∈ m23WeightTwoOrbit) :
    Nonempty (cocodeVectorStabilizer m23CocodeRepresentation v ≃*
      Sporadic.Mathieu.M22) :=
  m23WeightTwoOrbit_stabilizer_equiv hv

/-- H.15.1(2) for the native M24 cocode. -/
theorem m24_pair_commutator {v : Cocode} (hv : v ∈ weightTwoOrbit) :
    subspaceCommutator cocodeRepresentation ⊤
      (cocodeVectorStabilizer cocodeRepresentation v) = ⊤ :=
  weightTwoOrbit_stabilizer_commutator hv

/-- H.15.1(2) for the native M23 cocode. -/
theorem m23_pair_commutator {v : Cocode} (hv : v ∈ m23WeightTwoOrbit) :
    subspaceCommutator m23CocodeRepresentation ⊤
      (cocodeVectorStabilizer m23CocodeRepresentation v) = ⊤ :=
  m23WeightTwoOrbit_stabilizer_commutator hv

/-- The stronger M24 residual action required in 8.1.1. -/
theorem m24_pair_residual_commutator {v : Cocode} (hv : v ∈ weightTwoOrbit) :
    subspaceCommutator cocodeRepresentation ⊤
      ((Subgroup.solvableResidual (cocodeVectorStabilizer cocodeRepresentation v)).map
        (cocodeVectorStabilizer cocodeRepresentation v).subtype) = ⊤ :=
  weightTwoOrbit_residual_commutator hv

/-- The stronger M23 residual action required in 8.1.1. -/
theorem m23_pair_residual_commutator {v : Cocode} (hv : v ∈ m23WeightTwoOrbit) :
    subspaceCommutator m23CocodeRepresentation ⊤
      ((Subgroup.solvableResidual (cocodeVectorStabilizer m23CocodeRepresentation v)).map
        (cocodeVectorStabilizer m23CocodeRepresentation v).subtype) = ⊤ :=
  m23WeightTwoOrbit_residual_commutator hv

end CFSG.Quasithin.ChapterH.Section13To16.CocodeLocal
