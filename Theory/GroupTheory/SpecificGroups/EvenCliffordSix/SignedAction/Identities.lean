module

public import Theory.GroupTheory.SpecificGroups.EvenCliffordSix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Reordering identities for the signed six-letter action

The inversion bit is the sum, in characteristic two, of the original and
permuted order bits. Its composition law gives the signed correction's
composition law. Polarizing the correction gives precisely the change in the
multiplication cocycle. Reindexing uses symmetric sums over unordered pairs;
no enumeration of permutations or vectors is involved.

These identities construct the intrinsic action used for Aschbacher–Smith,
combined manuscript (1 March 2004), I.2.2(6), printed pp.410 and 412.
-/

@[expose] public section

namespace EvenCliffordSix
open Finset

section OrderedPairs
variable {ι R : Type*} [Fintype ι] [LinearOrder ι] [AddCommMonoid R]

private def triangle (f : ι → ι → R) : R :=
  ∑ i, ∑ j, if i < j then f i j else 0

private theorem triangle_add (f g : ι → ι → R) :
    triangle (fun i j => f i j + g i j) = triangle f + triangle g := by
  unfold triangle
  simp only [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  by_cases hij : i < j <;> simp [hij]

private theorem sum_off_diagonal (f : ι → ι → R) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = triangle (fun i j => f i j + f j i) := by
  have h (i j : ι) : f i j =
      (if i < j then f i j else 0) + (if j < i then f i j else 0) := by
    rcases lt_trichotomy i j with h | rfl | h
    · simp [h, not_lt_of_gt h]
    · simp [hd]
    · simp [h, not_lt_of_gt h]
  rw [triangle_add]
  calc
    _ = ∑ i, ∑ j, ((if i < j then f i j else 0) +
        (if j < i then f i j else 0)) := by
      apply sum_congr rfl
      intro i _
      exact sum_congr rfl (fun j _ => h i j)
    _ = triangle f + triangle (fun i j => f j i) := by
      simp only [sum_add_distrib, triangle]
      congr 1
      exact sum_comm

private theorem triangle_reindex (p : Equiv.Perm ι)
    (f : ι → ι → R) (hs : ∀ i j, f i j = f j i) :
    triangle (fun i j => f (p i) (p j)) = triangle f := by
  have h (q : Equiv.Perm ι) (g : ι → ι → R)
      (hg : ∀ i j, g i j = g j i) :
      (∑ i, ∑ j, if q i < q j then g i j else 0) = triangle g := by
    rw [sum_off_diagonal (fun i j => if q i < q j then g i j else 0) (by intro i; simp)]
    unfold triangle
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    by_cases hij : i < j
    · have hn : q i ≠ q j := fun he => (ne_of_lt hij) (q.injective he)
      rcases lt_or_gt_of_ne hn with hq | hq <;> simp [hij, hq, not_lt_of_gt hq, hg j i]
    · simp [hij]
  calc
    _ = ∑ i, ∑ j, if p i < p j then f (p i) (p j) else 0 :=
      (h p _ (fun i j => hs (p i) (p j))).symm
    _ = ∑ i, ∑ j, if p i < j then f (p i) j else 0 := by
      apply sum_congr rfl
      intro i _
      exact Equiv.sum_comp p (fun j => if p i < j then f (p i) j else 0)
    _ = _ := Equiv.sum_comp p (fun i => ∑ j, if i < j then f i j else 0)

end OrderedPairs

private def orderBit (i j : Fin 6) : F := if i < j then 1 else 0
private def inversionBit (p : Equiv.Perm (Fin 6)) (i j : Fin 6) : F :=
  orderBit i j + orderBit (p i) (p j)

private theorem inversionBit_diag (p : Equiv.Perm (Fin 6)) (i : Fin 6) :
    inversionBit p i i = 0 := by simp [inversionBit, orderBit]

private theorem inversionBit_symm (p : Equiv.Perm (Fin 6)) (i j : Fin 6) :
    inversionBit p i j = inversionBit p j i := by
  rcases eq_or_ne i j with rfl | hn
  · rfl
  have hp := p.injective.ne hn
  rcases lt_or_gt_of_ne hn with h | h <;>
    rcases lt_or_gt_of_ne hp with k | k <;>
    simp [inversionBit, orderBit, h, k, not_lt_of_gt h, not_lt_of_gt k, CharTwo.add_self_eq_zero]

private theorem inversionBit_mul (p q : Equiv.Perm (Fin 6)) (i j : Fin 6) :
    inversionBit (p * q) i j = inversionBit q i j + inversionBit p (q i) (q j) := by
  simp only [inversionBit, Equiv.Perm.mul_apply]
  rw [show orderBit i j + orderBit (q i) (q j) +
      (orderBit (q i) (q j) + orderBit (p (q i)) (p (q j))) =
      orderBit i j + orderBit (p (q i)) (p (q j)) +
        (orderBit (q i) (q j) + orderBit (q i) (q j)) by abel]
  simp [CharTwo.add_self_eq_zero]

private theorem correction_triangle (p : Equiv.Perm (Fin 6)) (v : V) :
    signedCorrection p v = triangle (fun i j => inversionBit p i j * (v.val i * v.val j)) := by
  unfold signedCorrection triangle
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  by_cases hij : i < j
  · have hn : p i ≠ p j := p.injective.ne (ne_of_lt hij)
    rcases lt_or_gt_of_ne hn with hp | hp <;>
      simp [hij, hp, not_lt_of_gt hp, inversionBit, orderBit, CharTwo.add_self_eq_zero]
  · simp [hij]


/-- Reordering successively by `q` and `p` adds their signed corrections. -/
theorem signedCorrection_comp (p q : Equiv.Perm (Fin 6)) (v : V) :
    signedCorrection (p * q) v = signedCorrection q v +
      signedCorrection p (permuteVector q v) := by
  simp only [correction_triangle, inversionBit_mul, add_mul, triangle_add]
  congr 1
  have h := triangle_reindex q
    (fun i j => inversionBit p i j * ((permuteVector q v).val i * (permuteVector q v).val j))
    (by intro i j; rw [inversionBit_symm p i j, mul_comm ((permuteVector q v).val i)])
  simpa only [permuteVector, Equiv.symm_apply_apply] using h

private theorem cocycle_orderBit (v w : Fin 6 → F) :
    cocycle v w = ∑ i, ∑ j, orderBit i j * (v j * w i) := by
  unfold cocycle
  apply sum_congr rfl
  intro i _
  simp only [orderBit, ite_mul, one_mul, zero_mul]
  exact by simpa only [filter_lt_eq_Ioi] using (sum_filter (s := univ) (fun j => i < j) (fun j => v j * w i))

private theorem cocycle_permute (p : Equiv.Perm (Fin 6)) (v w : V) :
    cocycle (permuteVector p v).val (permuteVector p w).val =
      ∑ i, ∑ j, orderBit (p i) (p j) * (v.val j * w.val i) := by
  rw [cocycle_orderBit]
  symm
  have h := Equiv.sum_comp p (fun i => ∑ j,
    orderBit i j * ((permuteVector p v).val j * (permuteVector p w).val i))
  rw [← h]
  apply sum_congr rfl
  intro i _
  have hj := Equiv.sum_comp p (fun j =>
    orderBit (p i) j * ((permuteVector p v).val j * (permuteVector p w).val (p i)))
  simpa only [permuteVector, Equiv.symm_apply_apply] using hj

private theorem correction_polar (p : Equiv.Perm (Fin 6)) (v w : V) :
    signedCorrection p (v + w) = signedCorrection p v + signedCorrection p w +
      triangle (fun i j => inversionBit p i j * (v.val i * w.val j + w.val i * v.val j)) := by
  simp only [correction_triangle]
  rw [← triangle_add, ← triangle_add]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  dsimp only
  congr 1
  change inversionBit p i j * ((v.val i + w.val i) * (v.val j + w.val j)) = _
  ring

private theorem cocycle_change (p : Equiv.Perm (Fin 6)) (v w : V) :
    cocycle v.val w.val + cocycle (permuteVector p v).val (permuteVector p w).val =
      triangle (fun i j => inversionBit p i j * (v.val i * w.val j + w.val i * v.val j)) := by
  rw [cocycle_orderBit, cocycle_permute]
  simp only [← sum_add_distrib, ← add_mul]
  change (∑ i, ∑ j, inversionBit p i j * (v.val j * w.val i)) = _
  rw [sum_off_diagonal _ (by intro i; rw [inversionBit_diag, zero_mul])]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  dsimp only
  rw [inversionBit_symm p j i]
  congr 1
  ring

/-- The polarization of the reordering sign is the change of group cocycle. -/
theorem signedCorrection_add (p : Equiv.Perm (Fin 6)) (v w : V) :
    signedCorrection p (v + w) = signedCorrection p v + signedCorrection p w +
      cocycle v.val w.val + cocycle (permuteVector p v).val (permuteVector p w).val := by
  rw [correction_polar, ← cocycle_change]
  abel

end EvenCliffordSix
