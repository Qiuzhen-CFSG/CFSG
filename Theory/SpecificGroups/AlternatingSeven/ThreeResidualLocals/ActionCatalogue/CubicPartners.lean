module

public import Theory.SpecificGroups.AlternatingSeven.ThreeResidualLocals.Models
import Mathlib.Tactic

/-!
# Cubic partners of a double transposition on seven letters

We classify all permutations `a` with `a³ = (a * fourFlip)³ = 1` under
conjugation by permutations commuting with `fourFlip`. The result retains the
literal permutations: the representatives are `naturalThree`, `diagonalThree`
and `pairedThree` from the shared models.

The table below supplies 48 possible relabellings and their inverses. Its inverse
and commutation identities are kernel checked. Completeness is checked separately:
Mathlib's permutation-list theorem splits every permutation into 42 blocks of
120 elements, and each block is checked in the kernel. Neither a computed group
order nor an unchecked enumeration is used as a coverage assumption.

This supplies the finite action calculation used in the A₇ branch of
Aschbacher–Smith 15.3.43, printed p.1140 (combined manuscript, 1 March 2004).
-/

public section

open Equiv Subgroup
namespace AlternatingSeven.ThreeResidualLocals.ActionCatalogue

private def conjugatorFun : Fin 48 → Fin 7 → Fin 7 :=
  ![
    ![0, 1, 2, 3, 4, 5, 6],
    ![0, 1, 2, 3, 4, 6, 5],
    ![0, 1, 2, 3, 5, 4, 6],
    ![0, 1, 2, 3, 5, 6, 4],
    ![0, 1, 2, 3, 6, 4, 5],
    ![0, 1, 2, 3, 6, 5, 4],
    ![0, 1, 3, 2, 4, 5, 6],
    ![0, 1, 3, 2, 4, 6, 5],
    ![0, 1, 3, 2, 5, 4, 6],
    ![0, 1, 3, 2, 5, 6, 4],
    ![0, 1, 3, 2, 6, 4, 5],
    ![0, 1, 3, 2, 6, 5, 4],
    ![1, 0, 2, 3, 4, 5, 6],
    ![1, 0, 2, 3, 4, 6, 5],
    ![1, 0, 2, 3, 5, 4, 6],
    ![1, 0, 2, 3, 5, 6, 4],
    ![1, 0, 2, 3, 6, 4, 5],
    ![1, 0, 2, 3, 6, 5, 4],
    ![1, 0, 3, 2, 4, 5, 6],
    ![1, 0, 3, 2, 4, 6, 5],
    ![1, 0, 3, 2, 5, 4, 6],
    ![1, 0, 3, 2, 5, 6, 4],
    ![1, 0, 3, 2, 6, 4, 5],
    ![1, 0, 3, 2, 6, 5, 4],
    ![2, 3, 0, 1, 4, 5, 6],
    ![2, 3, 0, 1, 4, 6, 5],
    ![2, 3, 0, 1, 5, 4, 6],
    ![2, 3, 0, 1, 5, 6, 4],
    ![2, 3, 0, 1, 6, 4, 5],
    ![2, 3, 0, 1, 6, 5, 4],
    ![2, 3, 1, 0, 4, 5, 6],
    ![2, 3, 1, 0, 4, 6, 5],
    ![2, 3, 1, 0, 5, 4, 6],
    ![2, 3, 1, 0, 5, 6, 4],
    ![2, 3, 1, 0, 6, 4, 5],
    ![2, 3, 1, 0, 6, 5, 4],
    ![3, 2, 0, 1, 4, 5, 6],
    ![3, 2, 0, 1, 4, 6, 5],
    ![3, 2, 0, 1, 5, 4, 6],
    ![3, 2, 0, 1, 5, 6, 4],
    ![3, 2, 0, 1, 6, 4, 5],
    ![3, 2, 0, 1, 6, 5, 4],
    ![3, 2, 1, 0, 4, 5, 6],
    ![3, 2, 1, 0, 4, 6, 5],
    ![3, 2, 1, 0, 5, 4, 6],
    ![3, 2, 1, 0, 5, 6, 4],
    ![3, 2, 1, 0, 6, 4, 5],
    ![3, 2, 1, 0, 6, 5, 4]
  ]
private def conjugatorInv : Fin 48 → Fin 7 → Fin 7 :=
  ![
    ![0, 1, 2, 3, 4, 5, 6],
    ![0, 1, 2, 3, 4, 6, 5],
    ![0, 1, 2, 3, 5, 4, 6],
    ![0, 1, 2, 3, 6, 4, 5],
    ![0, 1, 2, 3, 5, 6, 4],
    ![0, 1, 2, 3, 6, 5, 4],
    ![0, 1, 3, 2, 4, 5, 6],
    ![0, 1, 3, 2, 4, 6, 5],
    ![0, 1, 3, 2, 5, 4, 6],
    ![0, 1, 3, 2, 6, 4, 5],
    ![0, 1, 3, 2, 5, 6, 4],
    ![0, 1, 3, 2, 6, 5, 4],
    ![1, 0, 2, 3, 4, 5, 6],
    ![1, 0, 2, 3, 4, 6, 5],
    ![1, 0, 2, 3, 5, 4, 6],
    ![1, 0, 2, 3, 6, 4, 5],
    ![1, 0, 2, 3, 5, 6, 4],
    ![1, 0, 2, 3, 6, 5, 4],
    ![1, 0, 3, 2, 4, 5, 6],
    ![1, 0, 3, 2, 4, 6, 5],
    ![1, 0, 3, 2, 5, 4, 6],
    ![1, 0, 3, 2, 6, 4, 5],
    ![1, 0, 3, 2, 5, 6, 4],
    ![1, 0, 3, 2, 6, 5, 4],
    ![2, 3, 0, 1, 4, 5, 6],
    ![2, 3, 0, 1, 4, 6, 5],
    ![2, 3, 0, 1, 5, 4, 6],
    ![2, 3, 0, 1, 6, 4, 5],
    ![2, 3, 0, 1, 5, 6, 4],
    ![2, 3, 0, 1, 6, 5, 4],
    ![3, 2, 0, 1, 4, 5, 6],
    ![3, 2, 0, 1, 4, 6, 5],
    ![3, 2, 0, 1, 5, 4, 6],
    ![3, 2, 0, 1, 6, 4, 5],
    ![3, 2, 0, 1, 5, 6, 4],
    ![3, 2, 0, 1, 6, 5, 4],
    ![2, 3, 1, 0, 4, 5, 6],
    ![2, 3, 1, 0, 4, 6, 5],
    ![2, 3, 1, 0, 5, 4, 6],
    ![2, 3, 1, 0, 6, 4, 5],
    ![2, 3, 1, 0, 5, 6, 4],
    ![2, 3, 1, 0, 6, 5, 4],
    ![3, 2, 1, 0, 4, 5, 6],
    ![3, 2, 1, 0, 4, 6, 5],
    ![3, 2, 1, 0, 5, 4, 6],
    ![3, 2, 1, 0, 6, 4, 5],
    ![3, 2, 1, 0, 5, 6, 4],
    ![3, 2, 1, 0, 6, 5, 4]
  ]
private def conjugator (i : Fin 48) : Perm7 where
  toFun := conjugatorFun i
  invFun := conjugatorInv i
  left_inv := (by decide +kernel : ∀ i x, conjugatorInv i (conjugatorFun i x) = x) i
  right_inv := (by decide +kernel : ∀ i x, conjugatorFun i (conjugatorInv i x) = x) i
private theorem conjugator_commute : ∀ i, conjugator i * fourFlip = fourFlip * conjugator i := by
  decide +kernel
private def PartnerConclusion (a : Perm7) : Prop :=
  ∃ i : Fin 48, (conjugator i * a * (conjugator i)⁻¹ = naturalThree ∨
    conjugator i * a * (conjugator i)⁻¹ = diagonalThree ∨
    conjugator i * a * (conjugator i)⁻¹ = pairedThree)
private instance (a : Perm7) : Decidable (PartnerConclusion a) :=
  inferInstanceAs (Decidable (∃ _i : Fin 48, _))
-- Only the 120 permutations of the last five letters are inspected in each
-- block. The explicit list decision procedure avoids enumerating all of S₇
-- merely to test membership in this list.
private def PartnerBlock (i : Fin 7) (j : Fin 6) : Prop :=
  ∀ a ∈ permsOfList ([2, 3, 4, 5, 6] : List (Fin 7)),
    (swap 0 i * swap 1 j.succ * a) ^ 3 = 1 →
    ((swap 0 i * swap 1 j.succ * a) * fourFlip) ^ 3 = 1 →
    PartnerConclusion (swap 0 i * swap 1 j.succ * a)
private instance (i : Fin 7) (j : Fin 6) : Decidable (PartnerBlock i j) :=
  List.decidableBAll _ _
private theorem partner_blocks (i : Fin 7) (j : Fin 6) : PartnerBlock i j := by
  fin_cases i <;> fin_cases j <;> decide +kernel
private theorem split_perms {i : Fin 7} {l : List (Fin 7)} (a : Perm7)
    (ha : a ∈ permsOfList (i :: l)) :
    ∃ j ∈ i :: l, ∃ b ∈ permsOfList l, a = swap i j * b := by
  rw [permsOfList] at ha
  rcases List.mem_append.mp ha with h | h
  · exact ⟨i, by simp, a, h, by rw [swap_self]; rfl⟩
  · obtain ⟨j, hj, hj'⟩ := List.mem_flatMap.mp h
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp hj'
    exact ⟨j, List.mem_cons_of_mem _ hj, b, hb, hba.symm⟩

-- The first two swap choices give 7 · 6 blocks and cover every permutation;
-- this is proved from Mathlib's exhaustive permutation-list construction.
private theorem split_seven (a : Perm7) :
    ∃ i : Fin 7, ∃ j : Fin 6, ∃ b ∈ permsOfList ([2, 3, 4, 5, 6] : List (Fin 7)),
      a = swap 0 i * swap 1 j.succ * b := by
  have ha : a ∈ permsOfList ([0, 1, 2, 3, 4, 5, 6] : List (Fin 7)) :=
    mem_permsOfList_of_mem (by intro x _; fin_cases x <;> simp)
  obtain ⟨i, _, b, hb, hab⟩ := split_perms a ha
  obtain ⟨j, hj, c, hc, hbc⟩ := split_perms b hb
  have hj0 : j ≠ 0 := by intro h; subst j; simp at hj
  obtain ⟨k, rfl⟩ := Fin.eq_succ_of_ne_zero hj0
  exact ⟨i, k, c, hc, by rw [hab, hbc, mul_assoc]⟩
/-- Every cubic partner of `(0 1)(2 3)` satisfying the A₄ product relation
is conjugate to one of the three model generators by a permutation fixing that
involution under conjugation. -/
theorem cubic_partner_conjugacy (a : Perm7) (ha : a ^ 3 = 1)
    (hab : (a * fourFlip) ^ 3 = 1) :
    ∃ c : Perm7, c * fourFlip * c⁻¹ = fourFlip ∧
      (c * a * c⁻¹ = naturalThree ∨ c * a * c⁻¹ = diagonalThree ∨
        c * a * c⁻¹ = pairedThree) := by
  obtain ⟨i, j, b, hb, rfl⟩ := split_seven a
  obtain ⟨k, hk⟩ := partner_blocks i j b hb ha hab
  refine ⟨conjugator k, ?_, hk⟩
  rw [conjugator_commute, mul_inv_cancel_right]

end AlternatingSeven.ThreeResidualLocals.ActionCatalogue
