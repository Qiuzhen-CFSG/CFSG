module

public import Mathlib.Combinatorics.SimpleGraph.CycleGraph
public import Mathlib.Tactic.FinCases

/-!
# The marked opposite-pair action in a six-cycle

An automorphism carrying vertex five to its opposite vertex two carries
vertex zero to one or three. Excluding the opposite color-three vertex
therefore fixes the adjacent image as vertex one. This is the final local
graph step of Aschbacher--Smith J.4.10, printed pp.444--445.
-/

public section
namespace SimpleGraph.SixCycle
private theorem neighbors_two (x:Fin 6) : (cycleGraph 6).Adj x 2 ↔ x=1∨x=3 := by
  fin_cases x <;> decide

/-- A graph automorphism swapping one opposite pair sends the preceding
vertex to its neighbor whenever it does not send it to its own opposite. -/
theorem opposite_swap_neighbor {X:Type*} (Γ:SimpleGraph X) (e:cycleGraph 6≃gΓ)
    (a:Γ≃gΓ) (h5:a (e 5)=e 2) (h03:a (e 0)≠e 3) : a (e 0)=e 1 := by
  have ha:Γ.Adj (e 0) (e 5) := e.map_rel_iff.mpr (by decide)
  have hh:Γ.Adj (a (e 0)) (e 2) := h5 ▸ a.map_rel_iff.mpr ha
  have hi:(cycleGraph 6).Adj (e.symm (a (e 0))) 2 := by
    simpa only [e.symm_apply_apply] using e.symm.map_rel_iff.mpr hh
  rcases (neighbors_two _).mp hi with h|h
  · exact (e.apply_symm_apply _).symm.trans (congrArg e h)
  · exact False.elim (h03 ((e.apply_symm_apply _).symm.trans (congrArg e h)))
end SimpleGraph.SixCycle
