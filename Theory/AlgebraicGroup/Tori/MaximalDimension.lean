module
public import Theory.AlgebraicGroup.Borel.SelfNormalizer.TorusReduction
public import Theory.AlgebraicGroup.Borel.GeometricConjugacy

/-!
# Dimension of maximal tori from proved Borel conjugacy

Place two maximal tori in Borels, conjugate one Borel to the other using the
complete homogeneous-space proof, and then use connected-solvable torus
conjugacy inside that Borel. Dimensions are invariant under the resulting
two algebraic conjugations. This avoids the unresolved legacy numbered
maximal-torus conjugacy theorem.

The singular-centralizer consumer uses this equality to compare the torus
stored in its actual radical-quotient certificate with the image of the
original torus. Source: Borel, *Linear Algebraic Groups*, IV, 11.3 and 13.11.
-/

public section
namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

private theorem exists_borel_containing_torus (T : ClosedSubgroup G) (hT : IsSubtorus T) :
    ∃ B : ClosedSubgroup G, IsBorelSubgroup B ∧ T ≤ B := by
  have hconn : _root_.IsConnected (T : Set (Variety.Point G)) := by
    let : ConnectedSpace (Variety.Point T.carrierVariety) :=
      connectedSpace_iff_univ.mpr hT.isConnected
    change _root_.IsConnected (T.toSubgroup : Set (Variety.Point G))
    rw [← T.range_inclusion]
    exact isConnected_range T.inclusion.toVariety.continuous
  exact exists_borelSubgroup_containing_connected_solvable T hconn
    (Group.isSolvable_of_comm (isMulCommutative_iff.mp hT.isMulCommutative))

/-- Maximal tori have the same dimension, by the proved geometric Borel
conjugacy and the proved connected-solvable torus conjugacy. -/
theorem maximalTorus_dimension_eq {T S : ClosedSubgroup G}
    (hT : IsMaximalTorus T) (hS : IsMaximalTorus S) :
    Variety.dimension T.carrierVariety = Variety.dimension S.carrierVariety := by
  obtain ⟨B,hB,hTB⟩ := exists_borel_containing_torus T hT.1
  obtain ⟨C,hC,hSC⟩ := exists_borel_containing_torus S hS.1
  obtain ⟨g,hCg⟩ := BorelGeometricConjugacy.conjugacy hB hC
  have hTgC : T.conjugate g ≤ C := by
    rw [hCg]
    exact BorelIntersectionGeometry.conjugate_le hTB g
  obtain ⟨b,_,hSb⟩ := BorelSelfNormalizer.maximalTori_conjugate_inside_borel hC
    (BorelIntersectionGeometry.conjugate_isMaximalTorus hT g) hS hTgC hSC
  calc
    Variety.dimension T.carrierVariety = Variety.dimension (T.conjugate g).carrierVariety :=
      T.conjugate_dimension_eq g
    _ = Variety.dimension S.carrierVariety := by
      rw [hSb]
      exact (T.conjugate g).conjugate_dimension_eq b

end Theory.AlgebraicGroup
