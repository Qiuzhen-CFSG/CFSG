module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.Collinearity
public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.Source
public import Mathlib.Combinatorics.SimpleGraph.Basic

/-!
# The original Asc94 collinearity graph and its local parameters

Construct the graph on the literal conjugacy orbit Wᴳ, using incidence
with Vᴳ. The source configuration is constructed from the original IsType
hypothesis; its actual normalizer quotient, cubic axes, points and lines
are retained throughout. The quotient is A₆, each line has ten points,
each point has four lines and 36 neighbors, and two distinct points
determine at most one line.

The commuting-graph identification, weak closure in D, distance-two
regular action, and final recognition remain separate source obligations.
Source: Aschbacher, *Sporadic Groups* (1994), 45.9–45.10, pp.247–248.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry
variable {G : Type*} [Group G] [Finite G] {z : G} {h : IsType z}
variable {P : Sylow 3 (centralizer z)}
namespace SourceConfiguration
variable (c : SourceConfiguration h P)

def collinearity : SimpleGraph c.points where
  Adj U U' := U'.val ∈ c.neighbors U.val
  symm := by
    constructor
    intro U U' hh
    obtain ⟨_, hne, L, hL, hUL, hU'L⟩ := hh
    exact ⟨U.property, Ne.symm hne, L, hL, hU'L, hUL⟩
  loopless := by
    constructor
    intro U hh
    exact hh.2.1 rfl

def graphNeighborsEquiv (U : c.points) :
    c.collinearity.neighborSet U ≃ c.neighbors U.val where
  toFun U' := ⟨U'.val.val, U'.property⟩
  invFun U' := ⟨⟨U'.val, U'.property.1⟩, U'.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem collinearity_neighbor_card (U : c.points) :
    Nat.card (c.collinearity.neighborSet U) = 36 := by
  rw [Nat.card_congr (c.graphNeighborsEquiv U)]
  exact c.neighbors_card U.property

end SourceConfiguration
end Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry

namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G : Type*} [Group G] [Finite G] {z : G}

/-- Original source construction with all local incidence parameters discharged. -/
theorem original_cubic_incidence (h : IsType z) (P : Sylow 3 (centralizer z)) :
    ∃ c : CubicGeometry.SourceConfiguration h P,
      Nonempty (NormalizerAction.Star c.V ≃* alternatingGroup (Fin 6)) ∧
      (∀ L ∈ c.lines, Nat.card (c.pointsOn L) = 10) ∧
      (∀ U ∈ c.points, Nat.card (c.linesThrough U) = 4) ∧
      (∀ U : c.points, Nat.card (c.collinearity.neighborSet U) = 36) ∧
      (∀ U U' L L' : Subgroup G, U ∈ c.points → U' ∈ c.points →
        L ∈ c.lines → L' ∈ c.lines → U' ≠ U →
        U ≤ L → U ≤ L' → U' ≤ L → U' ≤ L' → L' = L) := by
  obtain ⟨c⟩ := h.original_cubic_source_configuration P
  exact ⟨c, c.quotient_equiv_alternating_six,
    fun _ hL => c.pointsOn_card hL, fun _ hU => c.linesThrough_card hU,
    c.collinearity_neighbor_card,
    fun _ _ _ _ hU hU' hL hL' hne hUL hUL' hU'L hU'L' =>
      c.line_unique hU hU' hL hL' hne hUL hUL' hU'L hU'L'⟩

end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
