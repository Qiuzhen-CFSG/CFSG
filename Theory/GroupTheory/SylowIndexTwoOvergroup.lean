module
public import Mathlib.GroupTheory.Sylow
public import Mathlib.GroupTheory.Index
/-!
# Two-subgroups above an index-two subgroup of a Sylow subgroup

If Q has index two in a Sylow two-subgroup T, every two-subgroup P
containing Q has relative index at most two. If P is larger than Q,
its order equals that of T, so P is itself an ambient Sylow subgroup.
This statement does not require P to contain T or normalize Q.

Source application: Aschbacher--Smith, original 5.2.2, printed p.648,
where the changed Sylow subgroup is initially Sylow only in a local group.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem card_mul_relIndex_of_le {Q P : Subgroup G} (h : Q ≤ P) :
    Nat.card Q * Q.relIndex P = Nat.card P := by
  simpa only [relIndex_bot_left] using relIndex_mul_relIndex (⊥ : Subgroup G) Q P bot_le h

/-- Enlargement above half of a Sylow two-subgroup is already ambient Sylow. -/
theorem two_group_over_index_two_sylow (T : Sylow 2 G) (Q P : Subgroup G)
    (hQT : Q ≤ (T : Subgroup G)) (hindex : Q.relIndex (T : Subgroup G) = 2)
    (hP : IsPGroup 2 P) (hQP : Q ≤ P) :
    Q.relIndex P ≤ 2 ∧ (P = Q ∨ ∃ U : Sylow 2 G, (U : Subgroup G) = P) := by
  obtain ⟨U,hPU⟩ := hP.exists_le_sylow
  have hUT : Nat.card (U : Subgroup G) = Nat.card (T : Subgroup G) := by
    rw [U.card_eq_multiplicity,T.card_eq_multiplicity]
  have hcT := card_mul_relIndex_of_le hQT
  rw [hindex] at hcT
  have hcP := card_mul_relIndex_of_le hQP
  have hbound : Q.relIndex P ≤ 2 := by
    have hb : Nat.card Q * Q.relIndex P ≤ Nat.card Q * 2 := by
      rw [hcP,hcT]
      exact (card_le_of_le hPU).trans_eq hUT
    exact Nat.le_of_mul_le_mul_left hb (Nat.card_pos (α := Q))
  refine ⟨hbound, ?_⟩
  by_cases he : P = Q
  · exact Or.inl he
  · have hne : Q.relIndex P ≠ 1 := fun hh => he (le_antisymm (relIndex_eq_one.mp hh) hQP)
    have hp : Q.relIndex P ≠ 0 := (Q.subgroupOf P).index_ne_zero_of_finite
    have hi : Q.relIndex P = 2 := by omega
    refine Or.inr ⟨U,?_⟩
    apply (eq_of_le_of_card_ge hPU ?_).symm
    rw [hUT,← hcT,← hcP,hi]
end Subgroup
