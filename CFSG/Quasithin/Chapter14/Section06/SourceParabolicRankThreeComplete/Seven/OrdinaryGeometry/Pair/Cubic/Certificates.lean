module
public import Theory.SpecificGroups.AlternatingSeven.DihedralLocals.Model
/-!
# Cubic complements over the two seven-letter Sylow models

A subgroup of index three over its Sylow two-subgroup is the product of
that Sylow subgroup and a cubic complement. Closure under multiplication
therefore restricts its cubic generator. The checks below enumerate the
seven-letter permutations in blocks of 120 and retain conjugacy by the
same fixed Sylow. The even model has five possibilities, the full model
has three. Subsequent subgroup transport must supply the product premise.

Source: Aschbacher--Smith, original 14.6.10(5), printed p.1029.
The permutation-list decomposition follows DihedralLocals.CubicCatalogue.
-/

@[expose] public section
open Equiv Subgroup AlternatingSeven.DihedralLocals
namespace CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic
abbrev Perm7 := Equiv.Perm (Fin 7)
def oddSwap : Perm7 := swap 4 5
def word (full : Bool) (i : Fin (if full then 16 else 8)) : Perm7 :=
  tWord ⟨i.val % 8, Nat.mod_lt _ (by decide)⟩ * oddSwap ^ (i.val / 8)
def cube (j : Fin 5) : Perm7 :=
  if h : j.val < 4 then cubic ⟨j.val,h⟩ else swap 4 5 * swap 5 6
def Criterion (full : Bool) (a : Perm7) : Prop :=
  a ^ 3 = 1 ∧ a ≠ 1 ∧ ∀ i : Fin (if full then 16 else 8),
    ∃ j : Fin (if full then 16 else 8), ∃ k : Fin 3, a * word full i = word full j * a ^ k.val
def Conclusion (full : Bool) (a : Perm7) : Prop :=
  ∃ j : Fin 5, (full = true → j.val = 0 ∨ j.val = 3 ∨ j.val = 4) ∧
    ∃ i : Fin 8, a = tWord i * cube j * (tWord i)⁻¹
instance (full : Bool) (a : Perm7) : Decidable (Criterion full a) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ ∀ _i : Fin (if full then 16 else 8), ∃ _j : Fin (if full then 16 else 8), ∃ _k : Fin 3, _))
instance (full : Bool) (a : Perm7) : Decidable (Conclusion full a) :=
  inferInstanceAs (Decidable (∃ _j : Fin 5, _ ∧ ∃ _i : Fin 8, _))
def Block (full : Bool) (i : Fin 7) (j : Fin 6) : Prop :=
  ∀ a ∈ permsOfList ([2,3,4,5,6] : List (Fin 7)),
    Criterion full (swap 0 i * swap 1 j.succ * a) →
      Conclusion full (swap 0 i * swap 1 j.succ * a)
instance (full : Bool) (i : Fin 7) (j : Fin 6) : Decidable (Block full i j) := List.decidableBAll _ _
set_option maxRecDepth 4096 in
private theorem blocks_0 (full : Bool) (j : Fin 6) : Block full 0 j := by
  cases full <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem blocks_1 (full : Bool) (j : Fin 6) : Block full 1 j := by
  cases full <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem blocks_2 (full : Bool) (j : Fin 6) : Block full 2 j := by
  cases full <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem blocks_3 (full : Bool) (j : Fin 6) : Block full 3 j := by
  cases full <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem blocks_4 (full : Bool) (j : Fin 6) : Block full 4 j := by
  cases full <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem blocks_5 (full : Bool) (j : Fin 6) : Block full 5 j := by
  cases full <;> fin_cases j <;> decide +kernel

set_option maxRecDepth 4096 in
private theorem blocks_6 (full : Bool) (j : Fin 6) : Block full 6 j := by
  cases full <;> fin_cases j <;> decide +kernel

private theorem blocks (full : Bool) (i : Fin 7) (j : Fin 6) : Block full i j := by
  fin_cases i
  · exact blocks_0 full j
  · exact blocks_1 full j
  · exact blocks_2 full j
  · exact blocks_3 full j
  · exact blocks_4 full j
  · exact blocks_5 full j
  · exact blocks_6 full j

private theorem split_perms {i : Fin 7} {l : List (Fin 7)} (a : Perm7)
    (ha : a ∈ permsOfList (i :: l)) :
    ∃ j ∈ i :: l, ∃ b ∈ permsOfList l, a = swap i j * b := by
  rw [permsOfList] at ha
  rcases List.mem_append.mp ha with h | h
  · exact ⟨i, by simp, a, h, by rw [swap_self]; rfl⟩
  · obtain ⟨j, hj, hj'⟩ := List.mem_flatMap.mp h
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp hj'
    exact ⟨j, List.mem_cons_of_mem _ hj, b, hb, hba.symm⟩

/-- Complete cubic-complement catalogue, with the Sylow conjugator retained. -/
theorem catalogue (full : Bool) (a : Perm7) (ha : Criterion full a) :
    Conclusion full a := by
  have hp : a ∈ permsOfList ([0,1,2,3,4,5,6] : List (Fin 7)) :=
    mem_permsOfList_of_mem (by intro x _; fin_cases x <;> simp)
  obtain ⟨i, _, b, hb, hab⟩ := split_perms a hp
  obtain ⟨j, hj, c, hc, hbc⟩ := split_perms b hb
  have hj0 : j ≠ 0 := by intro h; subst j; simp at hj
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj0
  have he : a = swap 0 i * swap 1 k.succ * c := by rw [hab,hbc,mul_assoc]
  rw [he] at ha ⊢
  exact blocks full i k c hc ha
end CFSG.Quasithin.Chapter14.Section06.Seven.OrdinaryGeometry.Pair.Cubic
