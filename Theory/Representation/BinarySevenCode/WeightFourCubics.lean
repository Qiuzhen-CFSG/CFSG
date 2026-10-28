module
public import Theory.Representation.BinarySevenCode.PermutationAction
public import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
# Cubic elements in a weight-four stabilizer

A permutation fixing a weight-four binary word preserves its support and
its complement, of sizes four and three. Restriction to these blocks shows
that every odd-order stabilizer element has cube one. The proof uses cycle
lengths and the literal permutation action, with no finite enumeration.

Source application: Aschbacher--Smith, cubic generation of O²(C_L(e)) in
the proper-overcomponent argument of 12.3.12, printed p.811.
-/

public section
namespace BinarySevenCode
open Subgroup

private theorem small_odd_perm_cube {α : Type*} [Fintype α] [DecidableEq α]
    (hcard : Fintype.card α ≤ 4) (a : Equiv.Perm α)
    (hodd : Odd (orderOf a)) : a ^ 3 = 1 := by
  apply Equiv.Perm.pow_prime_eq_one_iff.mpr
  intro c hc
  have hco : Odd c := hodd.of_dvd_nat (Equiv.Perm.dvd_of_mem_cycleType hc)
  have hlo := Equiv.Perm.two_le_of_mem_cycleType hc
  have hhi : c ≤ 4 := ((Multiset.le_sum_of_mem hc).trans a.sum_cycleType_le).trans hcard
  rcases hco with ⟨k,hk⟩
  omega

/-- Odd-order permutations stabilizing a weight-four word have cube one. -/
theorem weight_four_stabilizer_odd_cube (w : EvenWord) (hw : weight w.val = 4)
    (a : Equiv.Perm (Fin 7)) (ha : evenRepresentation a w = w)
    (hodd : Odd (orderOf a)) : a ^ 3 = 1 := by
  classical
  have hval (i : Fin 7) : w.val (a i) = w.val i := by
    have h := congrArg (fun v : EvenWord => v.val (a i)) ha
    simpa only [evenRepresentation_apply, Equiv.symm_apply_apply] using h.symm
  have hsub (p : Fin 7 → Prop) (hcard : Fintype.card {i // p i} ≤ 4)
      (hp : ∀ i, p (a i) ↔ p i) (i : Fin 7) (hi : p i) : (a ^ 3) i = i := by
    let b := a.subtypePerm hp
    have hd : orderOf b ∣ orderOf a := orderOf_dvd_of_pow_eq_one (by
      dsimp [b]
      rw [Equiv.Perm.subtypePerm_pow]
      ext j
      simp only [Equiv.Perm.subtypePerm_apply, pow_orderOf_eq_one, Equiv.Perm.one_apply])
    have hb := small_odd_perm_cube hcard b (hodd.of_dvd_nat hd)
    have hh := congrArg (fun f : Equiv.Perm {j // p j} => (f ⟨i,hi⟩).val) hb
    simpa only [b, Equiv.Perm.subtypePerm_pow, Equiv.Perm.subtypePerm_apply,
      Equiv.Perm.one_apply] using hh
  apply Equiv.ext
  intro i
  change (a ^ 3) i = i
  by_cases hi : w.val i ≠ 0
  · apply hsub (fun i => w.val i ≠ 0) ?_ (fun j => by rw [hval]) i hi
    simpa only [Fintype.card_subtype, weight] using hw.le
  · apply hsub (fun i => ¬ w.val i ≠ 0) ?_ (fun j => by rw [hval]) i hi
    rw [Fintype.card_subtype_compl]
    have hh : Fintype.card {i : Fin 7 // w.val i ≠ 0} = 4 := by
      simpa only [Fintype.card_subtype, weight] using hw
    rw [hh, Fintype.card_fin]
    decide
end BinarySevenCode
