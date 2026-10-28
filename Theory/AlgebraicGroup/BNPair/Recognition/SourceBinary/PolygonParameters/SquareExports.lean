module
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.MarkedMetric
public import Theory.AlgebraicGroup.BNPair.Recognition.SourceBinary.PolygonParameters.FinitePolygon

/-!
# Root-product square exports

The marked finite hexagon and octagon graphs discharge the Feit--Higman
square premises in the source orientation.
-/

public noncomputable section
open Subgroup
namespace Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
open Theory.AlgebraicGroup.TitsSystem.SourceBinary
open PolygonParameters
variable {X : Type*} [Group X] {P : Fin 2 → Subgroup X}

theorem hexagon_root_product_isSquare (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q=6) :
    IsSquare (Nat.card (simpleRoot Q split 0) * Nat.card (simpleRoot Q split 1)) := by
  let D := hexagonMetricDatum Q split hm
  have hs : 1 < Nat.card (simpleRoot Q split 1) := simpleRoot_card_gt_one Q split 1
  have ht : 1 < Nat.card (simpleRoot Q split 0) := simpleRoot_card_gt_one Q split 0
  have hp : ∃ v, D.color v=0 := hexagonMetricDatum_point Q split hm
  have h := hexagon_square D hs ht hp
  simpa only [Nat.mul_comm] using h

theorem octagon_twice_root_product_isSquare (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q=8) :
    IsSquare (2 * Nat.card (simpleRoot Q split 0) * Nat.card (simpleRoot Q split 1)) := by
  let D := octagonMetricDatum Q split hm
  have hs : 1 < Nat.card (simpleRoot Q split 1) := simpleRoot_card_gt_one Q split 1
  have ht : 1 < Nat.card (simpleRoot Q split 0) := simpleRoot_card_gt_one Q split 0
  have hp : ∃ v, D.color v=0 := octagonMetricDatum_point Q split hm
  have h := octagon_square D hs ht hp
  simpa only [Nat.mul_right_comm] using h


theorem hexagon_root_product_isSquare_of_ne (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q=6) (i j : Fin 2) (hij : i≠j) :
    IsSquare (Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j)) := by
  have h := hexagon_root_product_isSquare Q split hm
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h
  · change IsSquare (Nat.card (simpleRoot Q split 1) * Nat.card (simpleRoot Q split 0))
    rw [Nat.mul_comm]
    exact h
  · exact (hij rfl).elim

theorem octagon_twice_root_product_isSquare_of_ne (Q : MarkedQuotient P) (split : SplitData Q.tits)
    (hm : rotationOrder Q=8) (i j : Fin 2) (hij : i≠j) :
    IsSquare (2 * Nat.card (simpleRoot Q split i) * Nat.card (simpleRoot Q split j)) := by
  have h := octagon_twice_root_product_isSquare Q split hm
  fin_cases i <;> fin_cases j
  · exact (hij rfl).elim
  · exact h
  · change IsSquare (2 * Nat.card (simpleRoot Q split 1) * Nat.card (simpleRoot Q split 0))
    rw [Nat.mul_right_comm]
    exact h
  · exact (hij rfl).elim

end Theory.AlgebraicGroup.TitsSystem.SourceBinary.RootCoordinates
