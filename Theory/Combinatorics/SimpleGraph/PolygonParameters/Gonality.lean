module
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.OddExclusion
public import Theory.Combinatorics.SimpleGraph.PolygonParameters.Gonality.EvenExclusion

/-!
# Feit--Higman gonality for finite thick polygons

The literal metric datum determines the distance-polynomial recurrences.
Traces of the simple-root projections are natural-number multiplicities;
these force the relevant shifted angular roots to be rational. Niven's
theorem closes the odd and even exclusions. Thus the gonality is one of
2, 3, 4, 6, 8. Both thickness inequalities and a point witness remain explicit.

Source: Feit--Higman, The nonexistence of certain generalized polygons,
J. Algebra 1 (1964), 114--131, DOI 10.1016/0021-8693(64)90028-6;
Fong--Seitz I (1J), printed p.6. This interface proves the allowed-order
clause; the hexagon and octagon square constraints have separate exports.
-/

public section
namespace SimpleGraph.PolygonParameters.Datum
variable {V : Type*} {G : SimpleGraph V} [Fintype V] {m s t : ℕ}

/-- A finite thick polygon has gonality 2, 3, 4, 6 or 8. -/
theorem gonality (D : Datum G m s t) (hm : 2≤m) (hs : 1<s) (ht : 1<t)
    (hp : ∃ v,D.color v=0) : m=2 ∨ m=3 ∨ m=4 ∨ m=6 ∨ m=8 := by
  rcases Nat.even_or_odd m with he|ho
  · have ha := D.gonality_even_alternatives hm hs ht hp he
    omega
  · exact Or.inr (Or.inl (D.gonality_eq_three_of_odd hm hs ht hp ho))
end SimpleGraph.PolygonParameters.Datum
