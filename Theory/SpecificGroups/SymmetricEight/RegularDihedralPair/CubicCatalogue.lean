module

public import Theory.SpecificGroups.SymmetricEight.RegularDihedralPair.CubicEnumeration

/-! The Sylow condition removes the sixteen spurious cubic orbits. The exhaustive
permutation certificate is compiled separately from this group-theoretic step. -/

@[expose] public section
open Equiv Subgroup
namespace Theory.SpecificGroups.SymmetricEight.RegularDihedralPair

private def escapeWord : Fin 20 → List (Fin 3) :=
  ![[2,0,2,2,0,2],[2,0,2,2,0,2],[2,0,2,2,0,2],[2,0,2,2,0,2],[],[2,1,2],[2,1,2,2],[2,0,1,2],[2,0,0,0,2],[2,0,0,2,2],[2,1,0,2],[2,0,0,2,2],[2,0,0,2,2],[],[],[2,1,2,2],[],[2,0,0,2,2],[2,0,0,2,2],[2,0,0,2,2]]

private def Good (j : Fin 20) : Prop := j = 4 ∨ j = 13 ∨ j = 14 ∨ j = 16
private instance (j : Fin 20) : Decidable (Good j) :=
  inferInstanceAs (Decidable (_ ∨ _ ∨ _ ∨ _))

private theorem escapes (j : Fin 20) (hj : ¬ Good j) :
    TreeTest (eval ![r,s,candidate j] (escapeWord j)) ∧
      eval ![r,s,candidate j] (escapeWord j) ∉ twoGroup := by
  decide +revert +kernel

private theorem good_of_mem {X : Subgroup P8} (hX : MaximalTwo X)
    (j : Fin 20) (hj : candidate j ∈ X) : Good j := by
  by_contra hn
  have hm := eval_mem X ![r,s,candidate j]
    (by intro i; fin_cases i; exact hX.1 r_mem; exact hX.1 s_mem; exact hj) (escapeWord j)
  exact (escapes j hn).2 (mem_twoGroup_of_obstruction hX hm
    (treeTest_mem (escapes j hn).1))

private theorem candidate_cubic :
    candidate 4 = cubic 0 ∧ candidate 13 = cubic 1 ∧
    candidate 14 = cubic 2 ∧ candidate 16 = cubic 3 := by decide +kernel

/-- The actual Sylow condition removes the sixteen spurious cubic orbits. -/
theorem cubic_catalogue {X : Subgroup P8} (hX : MaximalTwo X)
    (a : P8) (haX : a ∈ X) (ha : Criterion a) :
    ∃ j : Fin 4, ∃ i : Fin 8, a = tWord i * cubic j * (tWord i)⁻¹ := by
  obtain ⟨q, t, ht⟩ := candidate_catalogue a ha
  have hm : candidate q ∈ X := by
    have htw := hX.1 (tWord_mem t)
    have hh := X.mul_mem (X.mul_mem (X.inv_mem htw) haX) htw
    rw [ht] at hh
    simpa only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one] using hh
  have hg := good_of_mem hX q hm
  rcases hg with hq | hq | hq | hq
  · exact ⟨0, t, by rw [hq] at ht; simpa only [candidate_cubic.1, candidate_cubic.2.1, candidate_cubic.2.2.1, candidate_cubic.2.2.2] using ht⟩
  · exact ⟨1, t, by rw [hq] at ht; simpa only [candidate_cubic.1, candidate_cubic.2.1, candidate_cubic.2.2.1, candidate_cubic.2.2.2] using ht⟩
  · exact ⟨2, t, by rw [hq] at ht; simpa only [candidate_cubic.1, candidate_cubic.2.1, candidate_cubic.2.2.1, candidate_cubic.2.2.2] using ht⟩
  · exact ⟨3, t, by rw [hq] at ht; simpa only [candidate_cubic.1, candidate_cubic.2.1, candidate_cubic.2.2.1, candidate_cubic.2.2.2] using ht⟩


end Theory.SpecificGroups.SymmetricEight.RegularDihedralPair
