module
public import Theory.GroupTheory.Recognition.Brauer.BlockIndex
public import Theory.GroupTheory.Recognition.Brauer.NonincidentCounts
public import Theory.GroupTheory.Recognition.Brauer.IncidentLowerBounds

/-!
# Exact point, line, and incidence counts in Brauer's geometry

For the original Brauer postulates, the geometry has `q^2 + q + 1` points
and lines, and each line has `q + 1` incident points, dually for each point.
This is Brauer, *On finite Desarguesian planes I*, (3A), article p. 121.
The theorem also retains the earlier consequence `q > 1` from (II).
These numerical statements supply the finite counting step in (3B)'s
construction of a projective plane.

The orbit-stabilizer count identifies the number of points with the index
in postulate (IV), giving its upper bound. For any line, the actual point
type partitions into incident and nonincident points. The former has at
least `q + 1` elements by (2G), and the latter has exactly `q^2` elements
by (2C). This forces equality with the upper bound. Both block families
have the same index, and their incident/nonincident partitions then give
the two exact incidence counts. No projective-plane axioms are assumed;
postulate (V) is not needed for these numerical conclusions.
-/

open scoped Pointwise

namespace Theory.GroupTheory

private theorem card_partition {α : Type*} [Finite α] (P : α → Prop) :
    Nat.card {a // P a} + Nat.card {a // ¬ P a} = Nat.card α := by
  classical
  simpa only [Nat.card_sum] using Nat.card_congr (Equiv.sumCompl P)

namespace BrauerPlaneData

/-- Brauer I (3A), together with the earlier nondegeneracy `q > 1`. -/
public theorem plane_counts {G : Type*} [Group G] [Finite G] (D : BrauerPlaneData G) :
    1 < D.toBrauerPlaneSeed.q ∧
    Nat.card D.toBrauerPlaneSeed.Point = D.toBrauerPlaneSeed.q ^ 2 + D.toBrauerPlaneSeed.q + 1 ∧
    Nat.card D.toBrauerPlaneSeed.Line = D.toBrauerPlaneSeed.q ^ 2 + D.toBrauerPlaneSeed.q + 1 ∧
    (∀ l : D.toBrauerPlaneSeed.Line,
      Nat.card {p : D.toBrauerPlaneSeed.Point // p ∈ l} = D.toBrauerPlaneSeed.q + 1) ∧
    (∀ p : D.toBrauerPlaneSeed.Point,
      Nat.card {l : D.toBrauerPlaneSeed.Line // p ∈ l} = D.toBrauerPlaneSeed.q + 1) := by
  let S := D.toBrauerPlaneSeed
  have hupper : Nat.card S.Point ≤ S.q ^ 2 + S.q + 1 := by
    rw [S.block_card_eq_index.1]
    exact D.index_le
  let l0 : S.Line := ⟨S.baseLine, MulAction.mem_orbit_self _⟩
  have hpartition (l : S.Line) :
      Nat.card {p : S.Point // p ∈ l} + S.q ^ 2 = Nat.card S.Point := by
    rw [← S.nonincident_counts.2 l]
    exact card_partition (fun p : S.Point => p ∈ l)
  have hpcount : Nat.card S.Point = S.q ^ 2 + S.q + 1 := by
    have hlower := S.incident_lower_bounds.1 l0
    have hpart := hpartition l0
    omega
  have hlcount : Nat.card S.Line = S.q ^ 2 + S.q + 1 := by
    rw [S.block_card_eq_index.2, ← S.block_card_eq_index.1, hpcount]
  refine ⟨S.block_sizes.2.2, hpcount, hlcount, ?_, ?_⟩
  · intro l
    change Nat.card {p : S.Point // p ∈ l} = S.q + 1
    have hpart := hpartition l
    omega
  · intro p
    change Nat.card {l : S.Line // p ∈ l} = S.q + 1
    have hpart := card_partition (fun l : S.Line => p ∈ l)
    rw [S.nonincident_counts.1 p] at hpart
    omega

end BrauerPlaneData
end Theory.GroupTheory
