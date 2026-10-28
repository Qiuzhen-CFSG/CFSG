module

public import Theory.GroupTheory.Recognition.UnitaryFourThree.CubicGeometry.ComponentStructure

/-!
# Original-input component subgroup

From the actual IsType hypothesis construct the component stabilizer, its
order, incidence-normalizer generators and full involution-centralizer
containment. Its index is prime to six and its A₆ section makes it
nonsolvable. These are source inputs to the remaining global recognition.

Source: Aschbacher, *Sporadic Groups* (1994),45.10–45.11, pp.247–249.
-/

@[expose] public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
variable {G : Type*} [Group G] [Finite G] {z : G}

theorem original_cubic_component_subgroup (h : IsType z) (P : Sylow 3 (centralizer z)) :
    ∃ c : CubicGeometry.SourceConfiguration h P,
      Nat.card c.componentStabilizer = 3265920 ∧
      c.componentStabilizer = normalizer (c.W : Set G) ⊔ normalizer (c.V : Set G) ∧
      centralizer z ≤ c.componentStabilizer ∧ Odd c.componentStabilizer.index ∧
      ¬3 ∣ c.componentStabilizer.index ∧ ¬Group.IsSolvable c.componentStabilizer := by
  obtain ⟨c⟩ := h.original_cubic_source_configuration P
  exact ⟨c, c.componentStabilizer_card, c.componentStabilizer_eq_normalizers_sup,
    c.centralizer_le_componentStabilizer, c.componentStabilizer_index_odd,
    c.three_not_dvd_componentStabilizer_index, c.componentStabilizer_not_solvable⟩

end Theory.GroupTheory.Recognition.UnitaryFourThree.IsType
