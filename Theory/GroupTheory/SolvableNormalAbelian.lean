module

public import Mathlib.GroupTheory.Solvable

/-!
# Abelian normal subgroups of solvable groups

The last nontrivial term of the derived series is abelian and normal.
This extracts the derived-series argument previously local to Fitting theory;
it does not require finiteness.
-/

namespace Group

/-- The last nontrivial derived subgroup is characteristic as well as abelian. -/
public theorem exists_nontrivial_abelian_characteristic (G : Type*) [Group G]
    [Nontrivial G] [hs : IsSolvable G] :
    ∃ A : Subgroup G, A.Characteristic ∧ IsMulCommutative A ∧ A ≠ ⊥ := by
  classical
  obtain h := hs.solvable
  let i := Nat.find h
  have hi : i ≠ 0 := by
    intro hi
    have hbot := Nat.find_spec h
    change derivedSeries G i = ⊥ at hbot
    simp [hi] at hbot
  refine ⟨derivedSeries G (i - 1), inferInstance, ?_,
    Nat.find_min h (Nat.sub_one_lt hi)⟩
  apply Subgroup.le_centralizer_iff_isMulCommutative.mp
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
  rw [← derivedSeries_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)]
  exact Nat.find_spec h

/-- A nontrivial solvable group has a nontrivial abelian normal subgroup. -/
public theorem exists_nontrivial_abelian_normal (G : Type*) [Group G]
    [Nontrivial G] [hs : IsSolvable G] :
    ∃ A : Subgroup G, A.Normal ∧ IsMulCommutative A ∧ A ≠ ⊥ := by
  classical
  obtain h := hs.solvable
  let i := Nat.find h
  have hi : i ≠ 0 := by
    intro hi
    have hbot := Nat.find_spec h
    change derivedSeries G i = ⊥ at hbot
    simp [hi] at hbot
  refine ⟨derivedSeries G (i - 1), derivedSeries_normal _ _, ?_,
    Nat.find_min h (Nat.sub_one_lt hi)⟩
  apply Subgroup.le_centralizer_iff_isMulCommutative.mp
  apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
  rw [← derivedSeries_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)]
  exact Nat.find_spec h

end Group
