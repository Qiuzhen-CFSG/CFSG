module

public import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Tactic.NormNum

/-!
# Fixed points of squares of permutations of order dividing eight

On a set of cardinality congruent to three modulo four, the square of such a
permutation cannot have just one fixed point. Otherwise every nontrivial cycle
has length four or eight, making the complement of that point divisible by
four. This elementary observation is useful for the degree-27 root group in
Suzuki's unitary recognition argument (1965, Section II).
-/

namespace Equiv.Perm

/-- An eighth-power identity permutation fixing a point on 27 points has a
second fixed point for its square. -/
public theorem exists_ne_sq_apply_eq_self_of_card_twentySeven
    {α : Type*} [Fintype α] (hcard : Fintype.card α = 27)
    (f : Equiv.Perm α) (hf : f ^ 8 = 1) (a : α) (ha : f a = a) :
    ∃ x : α, x ≠ a ∧ (f ^ 2) x = x := by
  classical
  by_contra! h
  have hsq (x : α) (hx : (f ^ 2) x = x) : x = a := by
    by_contra hxa
    exact h x hxa hx
  have hfixed (x : α) (hx : f x = x) : x = a := by
    apply hsq x
    simp [pow_two, hx]
  have hsupp : f.support = Finset.univ.erase a := by
    ext x
    simp only [mem_support, Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hx hxa
      exact hx (by simpa [hxa] using ha)
    · intro hx he
      exact hx (hfixed x he)
  have hfour : 4 ∣ f.support.card := by
    rw [← sum_cycleType]
    apply Multiset.dvd_sum
    intro n hn
    have hn8 : n ∣ 8 := (dvd_of_mem_cycleType hn).trans (orderOf_dvd_of_pow_eq_one hf)
    have hn2 : 2 ≤ n := two_le_of_mem_cycleType hn
    have hne2 : n ≠ 2 := by
      intro he
      obtain ⟨c, hc, hcn⟩ := Multiset.mem_map.mp hn
      have hc' : c ∈ f.cycleFactorsFinset := hc
      obtain ⟨hcycle, hcf⟩ := mem_cycleFactorsFinset_iff.mp hc'
      obtain ⟨x, hx⟩ := hcycle.nonempty_support
      have hc2 : c ^ 2 = 1 := by
        have horder : orderOf c = 2 := hcycle.orderOf.trans (hcn.trans he)
        rw [← horder]
        exact pow_orderOf_eq_one c
      have hcx : c x ∈ c.support := by simpa using hx
      have hx2 : (f ^ 2) x = x := by
        calc
          (f ^ 2) x = f (f x) := by simp [pow_two]
          _ = c (c x) := by rw [← hcf x hx, ← hcf (c x) hcx]
          _ = x := by simpa [pow_two] using congrArg (fun p : Equiv.Perm α => p x) hc2
      have hxa := hsq x hx2
      have hfx : f x ≠ x := mem_support.mp (mem_cycleFactorsFinset_support_le hc' hx)
      exact hfx (by simpa [hxa] using ha)
    have hdiv : n ∈ Nat.divisors 8 := Nat.mem_divisors.mpr ⟨hn8, by decide⟩
    have hd : Nat.divisors 8 = {1, 2, 4, 8} := by decide
    rw [hd] at hdiv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hdiv
    rcases hdiv with rfl | rfl | rfl | rfl <;> omega
  rw [hsupp, Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hcard] at hfour
  norm_num at hfour

end Equiv.Perm
