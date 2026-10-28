module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.Model

/-! Kernel-checked cubic candidates for S₄ overgroups of the regular D₈. -/

@[expose] public section
open Equiv Subgroup
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair

def candidate (j : Fin 20) : P8 where
  toFun := ![![0,1,3,5,7,2,4,6],![0,1,5,2,6,3,7,4],![0,1,5,4,7,6,2,3],![0,1,6,7,3,2,5,4],![0,2,6,4,7,5,1,3],![0,3,2,6,5,7,1,4],![0,3,2,6,7,4,1,5],![0,3,4,6,5,2,1,7],![0,3,4,6,7,5,1,2],![0,3,5,6,2,4,1,7],![0,3,5,6,4,7,1,2],![0,3,7,6,2,5,1,4],![0,3,7,6,4,2,1,5],![0,4,3,5,6,2,1,7],![0,5,2,7,3,6,1,4],![0,6,2,1,5,7,3,4],![0,6,3,5,4,2,7,1],![0,6,4,1,5,2,3,7],![0,6,4,1,7,5,3,2],![0,6,5,1,4,7,3,2]] j
  invFun := ![![0,1,5,2,6,3,7,4],![0,1,3,5,7,2,4,6],![0,1,6,7,3,2,5,4],![0,1,5,4,7,6,2,3],![0,6,1,7,3,5,2,4],![0,6,2,1,7,4,3,5],![0,6,2,1,5,7,3,4],![0,6,5,1,2,4,3,7],![0,6,7,1,2,5,3,4],![0,6,4,1,5,2,3,7],![0,6,7,1,4,2,3,5],![0,6,4,1,7,5,3,2],![0,6,5,1,4,7,3,2],![0,6,5,2,1,3,4,7],![0,6,2,4,7,1,5,3],![0,3,2,6,7,4,1,5],![0,7,5,2,4,3,1,6],![0,3,5,6,2,4,1,7],![0,3,7,6,2,5,1,4],![0,3,7,6,4,2,1,5]] j
  left_inv := by fin_cases j <;> decide
  right_inv := by fin_cases j <;> decide

def cubic (j : Fin 4) : P8 where
  toFun := ![![0,2,6,4,7,5,1,3], ![0,4,3,5,6,2,1,7],
    ![0,5,2,7,3,6,1,4], ![0,6,3,5,4,2,7,1]] j
  invFun := ![![0,6,1,7,3,5,2,4], ![0,6,5,2,1,3,4,7],
    ![0,6,2,4,7,1,5,3], ![0,7,5,2,4,3,1,6]] j
  left_inv := by fin_cases j <;> decide
  right_inv := by fin_cases j <;> decide

def Criterion (a : P8) : Prop :=
  a ^ 3 = 1 ∧ a ≠ 1 ∧ (a * r ^ 2) ^ 3 = 1 ∧ (a * r) ^ 4 = 1

private def Conclusion (a : P8) : Prop :=
  ∃ j : Fin 20, ∃ i : Fin 8, a = tWord i * candidate j * (tWord i)⁻¹

private instance (a : P8) : Decidable (Criterion a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))
private instance (a : P8) : Decidable (Conclusion a) :=
  inferInstanceAs (Decidable (∃ _j : Fin 20, ∃ _i : Fin 8, _))

private def Block (i : Fin 8) (j : Fin 7) (k : Fin 6) : Prop :=
  ∀ a ∈ permsOfList ([3,4,5,6,7] : List (Fin 8)),
    let g := swap 0 i * swap 1 j.succ * swap 2 k.succ.succ * a
    Criterion g → Conclusion g

private instance (i : Fin 8) (j : Fin 7) (k : Fin 6) : Decidable (Block i j k) :=
  List.decidableBAll _ _

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem blocks (i : Fin 8) (j : Fin 7) (k : Fin 6) : Block i j k := by
  fin_cases i <;> fin_cases j <;> fin_cases k <;> decide +kernel

private theorem split_perms {i : Fin 8} {l : List (Fin 8)} (a : P8)
    (ha : a ∈ permsOfList (i :: l)) :
    ∃ j ∈ i :: l, ∃ b ∈ permsOfList l, a = swap i j * b := by
  rw [permsOfList] at ha
  rcases List.mem_append.mp ha with h | h
  · exact ⟨i, by simp, a, h, by rw [swap_self]; rfl⟩
  · obtain ⟨j, hj, hj'⟩ := List.mem_flatMap.mp h
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp hj'
    exact ⟨j, List.mem_cons_of_mem _ hj, b, hb, hba.symm⟩

private theorem split_eight (a : P8) :
    ∃ i : Fin 8, ∃ j : Fin 7, ∃ k : Fin 6,
      ∃ b ∈ permsOfList ([3,4,5,6,7] : List (Fin 8)),
        a = swap 0 i * swap 1 j.succ * swap 2 k.succ.succ * b := by
  have ha : a ∈ permsOfList ([0,1,2,3,4,5,6,7] : List (Fin 8)) :=
    mem_permsOfList_of_mem (by intro x _; fin_cases x <;> simp)
  obtain ⟨i, _, b, hb, hab⟩ := split_perms a ha
  obtain ⟨j, hj, c, hc, hbc⟩ := split_perms b hb
  have hj0 : j ≠ 0 := by intro h; subst j; simp at hj
  obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj0
  obtain ⟨k, hk, d, hd, hcd⟩ := split_perms c hc
  have hk0 : k ≠ 0 := by intro h; subst k; simp at hk
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hk0
  have hk1 : k ≠ 0 := by intro h; subst k; simp at hk
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hk1
  exact ⟨i, j, k, d, hd, by rw [hab, hbc, hcd]; simp only [mul_assoc]⟩

/-- Every cubic satisfying the literal S₄ identities belongs to one of twenty
orbits under the fixed regular dihedral subgroup. -/
theorem candidate_catalogue (a : P8) (ha : Criterion a) :
    ∃ j : Fin 20, ∃ i : Fin 8, a = tWord i * candidate j * (tWord i)⁻¹ := by
  obtain ⟨i, j, k, b, hb, rfl⟩ := split_eight a
  exact blocks i j k b hb ha

end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
