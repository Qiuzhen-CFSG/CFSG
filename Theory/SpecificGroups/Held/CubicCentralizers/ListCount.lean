module
public import Theory.SpecificGroups.Held.CubicCentralizers.Support
/-! The complete finite sample is traversed once when checking a neighbor
count. This proved list evaluator avoids repeated finite-set construction in
the cubic-centralizer certificates. -/
public section
namespace Held.CubicCentralizers
open Held.NormalizerGraph
open scoped BigOperators
theorem neighborCount_list (L : List (Fin 2058)) (hL : L.Nodup) (x : Fin 2058) :
    neighborCount L.toFinset x = L.countP (fun y => decide (Adj x y)) := by
  unfold neighborCount
  rw [Finset.sum_boole]
  exact hL.card_eq_countP
end Held.CubicCentralizers
