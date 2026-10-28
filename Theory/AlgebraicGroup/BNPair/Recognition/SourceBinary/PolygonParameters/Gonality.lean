module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.GeneralGeometry

/-!
# The marked quotient's allowed Weyl rotation orders

The finite marked quotient supplies the metric datum, thickness and a point.
Feit--Higman therefore restricts its actual rotation order to 2, 3, 4, 6, 8.
The quotient, full Borel and ordered endpoint maps are unchanged. Finiteness
comes from the quotient; the original ambient group need not be finite.

Source: Fong--Seitz I (1J), printed p.6, citing Feit--Higman,
J. Algebra 1 (1964), 114--131. The previously exported spectral constraints
are retained alongside the completed allowed-order theorem.
-/

public noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters.Gonality
open RootCoordinates
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

/-- The odd case's equal parameters, derived from the actual quotient geometry. -/
theorem marked_odd_parameters_eq (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (ho : Odd (rotationOrder Q)) :
    Nat.card (simpleRoot Q split 1) = Nat.card (simpleRoot Q split 0) := by
  have ht := GeneralGeometry.metricDatum_thick Q split
  exact (GeneralGeometry.metricDatum Q split).parameters_eq_of_odd (rotationOrder_ge_two Q)
    (by omega) (by omega) (GeneralGeometry.metricDatum_point Q split) ho

/-- The actual even polygon's point adjacency minimal polynomial. -/
theorem marked_even_minpoly (Q : MarkedQuotient P) (split : SplitData Q.tits)
    {half : ℕ} (hh : 2≤half) (he : rotationOrder Q=2*half) :
    minpoly ℝ ((GeneralGeometry.metricDatum Q split).distanceMatrix 1) =
      SimpleGraph.PolygonParameters.Gonality.evenAnnihilator half
        (Nat.card (simpleRoot Q split 1)) (Nat.card (simpleRoot Q split 0)) := by
  have ht := GeneralGeometry.metricDatum_thick Q split
  exact (GeneralGeometry.metricDatum Q split).even_minpoly_of_eq he hh
    (by omega) (by omega) (GeneralGeometry.metricDatum_point Q split)
/-- Feit--Higman applied to the actual unselected marked quotient. -/
theorem marked_rotationOrder_allowed (Q : MarkedQuotient P) (split : SplitData Q.tits) :
    rotationOrder Q=2 ∨ rotationOrder Q=3 ∨ rotationOrder Q=4 ∨
      rotationOrder Q=6 ∨ rotationOrder Q=8 := by
  have ht := GeneralGeometry.metricDatum_thick Q split
  exact (GeneralGeometry.metricDatum Q split).gonality (rotationOrder_ge_two Q)
    ht.1 ht.2 (GeneralGeometry.metricDatum_point Q split)

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.PolygonParameters.Gonality
