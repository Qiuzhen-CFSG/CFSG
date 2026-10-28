module

public import Mathlib.GroupTheory.Nilpotent

namespace Stellmacher.SectionEight

universe u

public theorem eight_six_nilpotent_normal_le_of_commutator_test
    {G : Type u} [Group G] [Group.IsNilpotent G]
    (C Z : Subgroup G) [C.Normal]
    (htest : ∀ U : Subgroup G, U ≤ C → ⁅U, ⊤⁆ ≤ Z → U ≤ Z) :
    C ≤ Z := by
  have hseries (level : ℕ) : C ⊓ Subgroup.upperCentralSeries G level ≤ Z := by
    induction level with
    | zero => simp
    | succ level ih =>
      apply htest _ inf_le_left
      apply le_trans (le_inf ?_ ?_) ih
      · exact (Subgroup.commutator_mono inf_le_left le_rfl).trans
          (Subgroup.commutator_le_left C ⊤)
      · exact (Subgroup.commutator_mono inf_le_right le_rfl).trans
          (Subgroup.commutator_upperCentralSeries_top_le G level)
  obtain ⟨level, hlevel⟩ := Group.IsNilpotent.nilpotent G
  simpa only [hlevel, inf_top_eq] using hseries level

public theorem eight_six_two_subgroup_le_of_commutator_test
    {G : Type u} [Group G] [Finite G]
    (S C Z : Subgroup G) (hS : IsPGroup 2 S)
    (hCS : C ≤ S) (hnormal : S ≤ Subgroup.normalizer (C : Set G))
    (htest : ∀ U : Subgroup G, U ≤ C → ⁅U, S⁆ ≤ Z → U ≤ Z) :
    C ≤ Z := by
  let _ : Group.IsNilpotent S := hS.isNilpotent
  let _ : (C.subgroupOf S).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCS).mpr hnormal
  have hnative : C.subgroupOf S ≤ Z.subgroupOf S := by
    apply eight_six_nilpotent_normal_le_of_commutator_test
    intro U hUC hcomm
    have hU : U.map S.subtype ≤ C :=
      (Subgroup.map_mono hUC).trans_eq (Subgroup.map_subgroupOf_eq_of_le hCS)
    have hUS : ⁅U.map S.subtype, S⁆ ≤ Z := by
      have hmapped := Subgroup.map_mono (f := S.subtype) hcomm
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        Subgroup.range_subtype] at hmapped
      exact hmapped.trans (by
        rintro element ⟨native, hnative, rfl⟩
        exact hnative)
    intro element helement
    exact htest _ hU hUS (Subgroup.mem_map_of_mem S.subtype helement)
  intro element helement
  exact hnative (show (⟨element, hCS helement⟩ : S) ∈ C.subgroupOf S from helement)

end Stellmacher.SectionEight
