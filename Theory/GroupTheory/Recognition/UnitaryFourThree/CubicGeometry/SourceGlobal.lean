module
public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.Connected
/-!
# Global source geometry from the original type hypothesis

The original IsType hypothesis now supplies the entire 280-point cubic
geometry and its global group order. The actual two incidence normalizers
generate G. No connectedness, internal fusion, order or recognition premise
is added to the original source input.
Source: Aschbacher, Sporadic Groups (1994),45.10(9)–(10), p.248.
-/
public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G : Type*} [Group G] [Finite G] {z : G}

theorem original_cubic_global_geometry (h : IsType z) (P : Sylow 3 (centralizer z)) :
    ∃ c : CubicGeometry.SourceConfiguration h P,
      c.componentStabilizer=⊤ ∧ c.collinearity.Connected ∧ Nat.card c.points=280 ∧
      normalizer (c.W:Set G)⊔normalizer (c.V:Set G)=⊤ ∧
      ∀U:c.points, U=⟨c.W,c.point_mem⟩ ∨ c.collinearity.Adj ⟨c.W,c.point_mem⟩ U ∨
        c.collinearity.edist ⟨c.W,c.point_mem⟩ U=2 := by
  obtain ⟨c⟩ := h.original_cubic_source_configuration P
  exact ⟨c,c.componentStabilizer_eq_top,c.collinearity_connected,c.points_card,
    c.ambient_eq_normalizers_sup,fun U=>(c.reachable_iff_withinTwo U).mp (c.original_point_reachable U)⟩

theorem ambient_card (h : IsType z) : Nat.card G=3265920 := by
  let P : Sylow 3 (centralizer z) := Classical.choice inferInstance
  obtain ⟨c⟩ := h.original_cubic_source_configuration P
  exact c.ambient_card
end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
