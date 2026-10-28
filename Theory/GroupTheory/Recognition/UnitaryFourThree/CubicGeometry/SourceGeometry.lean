module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.LocalDiameter

/-!
# Original-input component geometry

The original IsType hypothesis constructs the cubic source configuration
and proves the component size and diameter without additional geometry
or recognition premises. This consumer is the component part of Asc94
45.10(8)–(10), p.248; global connectedness is a separate obligation.
-/

@[expose] public section
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G : Type*} [Group G] [Finite G] {z : G}

theorem original_cubic_component (h : IsType z) (P : Sylow 3 (centralizer z)) :
    ∃ c : CubicGeometry.SourceConfiguration h P,
      Nat.card {U : c.points // c.collinearity.Reachable ⟨c.W, c.point_mem⟩ U} = 280 ∧
      (∀ U : c.points, c.collinearity.Reachable ⟨c.W, c.point_mem⟩ U ↔
        U = ⟨c.W, c.point_mem⟩ ∨ c.collinearity.Adj ⟨c.W, c.point_mem⟩ U ∨
          c.collinearity.edist ⟨c.W, c.point_mem⟩ U = 2) := by
  obtain ⟨c⟩ := h.original_cubic_source_configuration P
  exact ⟨c, c.component_card, c.reachable_iff_withinTwo⟩

end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
