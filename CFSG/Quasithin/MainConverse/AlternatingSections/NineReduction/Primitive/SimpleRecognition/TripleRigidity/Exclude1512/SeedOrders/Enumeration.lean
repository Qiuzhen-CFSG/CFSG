module

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.Exclude1512.SeedOrders.Data
public import Theory.GroupTheory.SubgroupClosureFinite
public import Mathlib.GroupTheory.Coset.Card

/-!
# Kernel-checked enumeration of the first nine-point seed

The data give 504 actual permutations. Each row has a checked inverse, and
right multiplication by each generator has a checked successor with a
predecessor. Subgroup closure induction therefore puts the generated subgroup
inside the list. Conversely, the identity is row zero and every other row has
a checked edge from a smaller row, proving membership by strong induction.
A lookup on the images of 0, 1 and 2 recovers each row index, so the list is
injective. These two containments give a bijection and the exact order 504.

All finite checks below use kernel reduction. The data supply witnesses, not
assumptions. Source context: Aschbacher–Smith, `refs/quasithin.pdf`, printed
pp.4 and 482, condition K and the alternating case.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction.Exclude1512.SeedEnumeration

private def allFin {n : Nat} (f : Fin n → Bool) : Bool := (List.finRange n).all f

private theorem allFin_sound {n : Nat} {f : Fin n → Bool} (h : allFin f = true)
    (i : Fin n) : f i = true :=
  List.all_eq_true.mp h i (List.mem_finRange i)

set_option maxRecDepth 4096 in
private theorem inverse_checked : allFin (fun i => allFin (fun x =>
    (inverseRow i (row i x) == x) && (row i (inverseRow i x) == x))) = true := by
  decide +kernel

private theorem inverse_left (i : Fin 504) (x : Fin 9) : inverseRow i (row i x) = x := by
  have h := allFin_sound (allFin_sound inverse_checked i) x
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.1

private theorem inverse_right (i : Fin 504) (x : Fin 9) : row i (inverseRow i x) = x := by
  have h := allFin_sound (allFin_sound inverse_checked i) x
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact h.2

private def perm (i : Fin 504) : Perm where
  toFun := row i
  invFun := inverseRow i
  left_inv := inverse_left i
  right_inv := inverse_right i

private def generator (b : Bool) : Perm := if b then involution false else cycle

set_option maxRecDepth 4096 in
private theorem next_checked : allFin (fun i => allFin (fun x =>
    (row i (generator false x) == row (next i false) x) &&
    (row i (generator true x) == row (next i true) x))) = true := by
  decide +kernel

private theorem perm_next (i : Fin 504) (b : Bool) : perm i * generator b = perm (next i b) := by
  apply Equiv.ext
  intro x
  have h := allFin_sound (allFin_sound next_checked i) x
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  cases b
  · exact h.1
  · exact h.2

set_option maxRecDepth 4096 in
private theorem indices_checked : allFin (fun i =>
    (next (prev i false) false == i) && (next (prev i true) true == i) &&
    (i == 0 || ((parent i).val < i.val && (next (parent i) (letter i) == i))) &&
    (indexOfTriple (row i) == i.val)) = true := by
  decide +kernel

private theorem next_prev (i : Fin 504) (b : Bool) : next (prev i b) b = i := by
  have h := allFin_sound indices_checked i
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  cases b
  · exact h.1.1.1
  · exact h.1.1.2

private theorem parent_lt (i : Fin 504) (hi : i ≠ 0) : (parent i).val < i.val := by
  have h := allFin_sound indices_checked i
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact (h.1.2.resolve_left hi).1

private theorem parent_next (i : Fin 504) (hi : i ≠ 0) : next (parent i) (letter i) = i := by
  have h := allFin_sound indices_checked i
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  exact (h.1.2.resolve_left hi).2

private theorem perm_injective : Function.Injective perm := by
  intro i j h
  have hi := allFin_sound indices_checked i
  have hj := allFin_sound indices_checked j
  simp only [Bool.and_eq_true, beq_iff_eq] at hi hj
  apply Fin.ext
  rw [← hi.2, ← hj.2]
  exact congrArg (fun p : Perm => indexOfTriple p) h


private theorem perm_zero : perm 0 = 1 := by
  apply Equiv.ext
  intro x
  revert x
  decide +kernel

private theorem generator_mem (b : Bool) : generator b ∈ seed false := by
  cases b <;> exact Subgroup.subset_closure (by simp [generator])

private theorem perm_mem (i : Fin 504) : perm i ∈ seed false := by
  have hm : ∀ n, ∀ (hn : n < 504), perm ⟨n, hn⟩ ∈ seed false := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn
      let j : Fin 504 := ⟨n, hn⟩
      change perm j ∈ seed false
      by_cases hj : j = 0
      · rw [hj, perm_zero]
        exact (seed false).one_mem
      · have hp : (parent j).val < n := parent_lt j hj
        have hm := ih (parent j).val hp (parent j).isLt
        have he := perm_next (parent j) (letter j)
        rw [parent_next j hj] at he
        rw [← he]
        exact (seed false).mul_mem hm (generator_mem (letter j))
  exact hm i.val i.isLt

private theorem perm_covers : (seed false : Set Perm) ⊆ Set.range perm := by
  have hgen : Set.range generator = {cycle, involution false} := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      cases b <;> simp [generator]
    · intro hx
      rcases (Set.mem_insert_iff.mp hx) with rfl | hx
      · exact ⟨false, rfl⟩
      · exact ⟨true, (Set.mem_singleton_iff.mp hx).symm⟩
  have h := Theory.GroupTheory.SubgroupEnumeration.closure_range_subset_range_of_transitions
    generator perm 0 next prev perm_zero perm_next next_prev
  rw [hgen] at h
  exact h

/-- The first seed is in bijection with the 504 checked rows. -/
public theorem card_false : Nat.card (seed false) = 504 := by
  let f : Fin 504 → seed false := fun i => ⟨perm i, perm_mem i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j h
      exact perm_injective (congrArg Subtype.val h)
    · intro x
      obtain ⟨i, hi⟩ := perm_covers x.property
      exact ⟨i, Subtype.ext hi⟩
  rw [← Nat.card_eq_of_bijective f hf]
  exact Nat.card_fin 504

end CFSG.Quasithin.MainConverse.NineReduction.Exclude1512.SeedEnumeration
