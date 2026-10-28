module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.FaithfulAction
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.SourceGlobal
/-!
# The original source group acting faithfully on its connected cubic graph

This packages the literal conjugation action, connectedness and order from
the unchanged IsType hypothesis. It supplies the faithful group action
required after the local graph comparison in Asc94,45.11, pp.248–249.
-/
public section
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G : Type*} [Group G] [Finite G] {z : G}
theorem original_cubic_faithful_action (h : IsType z) (P : Sylow 3 (centralizer z)) :
    ∃c : CubicGeometry.SourceConfiguration h P,
      c.collinearity.Connected ∧ Nat.card c.points=280 ∧
      Function.Injective c.graphAction := by
  obtain ⟨c⟩ := h.original_cubic_source_configuration P
  exact ⟨c,c.collinearity_connected,c.points_card,c.graphAction_injective⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
