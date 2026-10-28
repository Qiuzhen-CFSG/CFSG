module

public import Mathlib.GroupTheory.Nilpotent
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Noncentral second-center elements in nilpotent groups

If the first and second centers agree, the upper central series stabilizes;
nilpotence then forces the group to be abelian. Otherwise adjoining a
second-center element to the center produces an abelian normal subgroup.
Its centralizer is the centralizer of that element, which is therefore normal.

This is the group-theoretic step in the proof that finite nilpotent groups are
monomial; see Serre, *Linear Representations of Finite Groups*, the treatment
of monomial representations. Finiteness is not needed for these group lemmas.
-/

public section

open Subgroup
open scoped commutatorElement

namespace Group
/-- A nonabelian nilpotent group has a noncentral element in its second center. -/
theorem exists_mem_upperCentralSeries_two_not_mem_center
    {G : Type*} [Group G] [IsNilpotent G] (hG : ¬ IsMulCommutative G) :
    ∃ x : G, x ∈ Subgroup.upperCentralSeries G 2 ∧ x ∉ center G := by
  have hZ₂ : ¬ Subgroup.upperCentralSeries G 2 ≤ center G := by
    intro hle
    have heq : Subgroup.upperCentralSeries G 1 = Subgroup.upperCentralSeries G 2 := by
      apply le_antisymm (Subgroup.upperCentralSeries_mono G (by omega))
      simpa using hle
    have htop := Subgroup.upperCentralSeries.eq_top (by omega : 1 ≠ 2) heq
    exact hG (center_eq_top_iff.mp (by simpa using htop))
  exact SetLike.not_le_iff_exists.mp hZ₂

/-- Adjoining one noncentral second-center element to the center gives an
abelian normal subgroup still contained in the second center. -/
theorem exists_abelian_normal_not_le_center
    {G : Type*} [Group G] [IsNilpotent G] (hG : ¬ IsMulCommutative G) :
    ∃ A : Subgroup G, A.Normal ∧ IsMulCommutative A ∧
      center G ≤ A ∧ A ≤ Subgroup.upperCentralSeries G 2 ∧ ¬ A ≤ center G := by
  obtain ⟨x, hx₂, hxZ⟩ := exists_mem_upperCentralSeries_two_not_mem_center hG
  let A := closure (insert x (center G : Set G))
  have hZA : center G ≤ A := fun z hz => subset_closure (Set.mem_insert_of_mem _ hz)
  have hxA : x ∈ A := subset_closure (Set.mem_insert _ _)
  have hA₂ : A ≤ Subgroup.upperCentralSeries G 2 := by
    apply (closure_le _).mpr
    intro z hz
    rcases hz with rfl | hz
    · exact hx₂
    · exact (show center G ≤ Subgroup.upperCentralSeries G 2 by
        simpa using Subgroup.upperCentralSeries_mono G (show 1 ≤ 2 by omega)) hz
  refine ⟨A, ?_, ?_, hZA, hA₂, fun h => hxZ (h hxA)⟩
  · apply commutator_top_right_le_iff.mp
    exact (commutator_mono hA₂ le_rfl).trans
      ((show ⁅Subgroup.upperCentralSeries G 2, (⊤ : Subgroup G)⁆ ≤ center G by
        simpa using Subgroup.commutator_upperCentralSeries_top_le (G := G) 1).trans hZA)
  · apply isMulCommutative_closure
    intro a ha b hb
    rcases ha with rfl | ha
    · rcases hb with rfl | hb
      · rfl
      · exact (mem_center_iff.mp hb _)
    · exact (mem_center_iff.mp ha b).symm

/-- The centralizer of a second-center element is normal. -/
theorem normal_centralizer_singleton_of_mem_upperCentralSeries_two
    {G : Type*} [Group G] (x : G) (hx : x ∈ Subgroup.upperCentralSeries G 2) :
    (centralizer ({x} : Set G)).Normal := by
  let A := closure (insert x (center G : Set G))
  have hZA : center G ≤ A := fun z hz => subset_closure (Set.mem_insert_of_mem _ hz)
  have hA₂ : A ≤ Subgroup.upperCentralSeries G 2 := by
    apply (closure_le _).mpr
    intro z hz
    rcases hz with rfl | hz
    · exact hx
    · exact (show center G ≤ Subgroup.upperCentralSeries G 2 by
        simpa using Subgroup.upperCentralSeries_mono G (show 1 ≤ 2 by omega)) hz
  have hnormal : A.Normal := by
    apply commutator_top_right_le_iff.mp
    exact (commutator_mono hA₂ le_rfl).trans
      ((show ⁅Subgroup.upperCentralSeries G 2, (⊤ : Subgroup G)⁆ ≤ center G by
        simpa using Subgroup.commutator_upperCentralSeries_top_le (G := G) 1).trans hZA)
  let := hnormal
  have heq : centralizer (A : Set G) = centralizer ({x} : Set G) := by
    rw [centralizer_closure]
    ext g
    simp only [mem_centralizer_iff, Set.mem_insert_iff, SetLike.mem_coe,
      Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    exact and_iff_left (fun z hz => (mem_center_iff.mp hz g).symm)
  rw [← heq]
  infer_instance
end Group
