module

public import Theory.SpecificGroups.BabyMonster.NormalSubgroups.CentralizerMaximal.Census
public import Theory.GroupTheory.DoubleCosetIndexSpectrum
public import Mathlib.Order.Atoms
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Fin

/-!
# A subdegree criterion for maximality of the Baby Monster centralizer

For the five subdegrees in Breuer–Magaard–Wilson (2019), §5.2,
https://arxiv.org/abs/1902.07758, the only sums containing the fixed-point
subdegree and dividing the full degree are one and the full degree.
An overgroup is a union of double cosets, so its relative index is one of
these sums. Lagrange's formula then makes it either the centralizer or the
whole group.

The arithmetic and this implication are proved here. Existence of the census
for the fixed presentation remains an explicit premise, not an assumed fact
about an already identified Baby Monster.
-/

public section
namespace BabyMonster

/-- The five subdegrees add to the degree of the centralizer coset action. -/
theorem generatorCentralizerSubdegree_sum :
    ∑ i, generatorCentralizerSubdegree i = 13571955000 := by
  decide

set_option maxRecDepth 10000 in
/-- No intermediate union of suborbits containing the fixed point has a size
that divides the degree. This is a kernel-checked finite calculation. -/
theorem generatorCentralizerSubdegree_divisor (s : Finset (Fin 5))
    (hzero : 0 ∈ s)
    (hdiv : (∑ i ∈ s, generatorCentralizerSubdegree i) ∣ 13571955000) :
    (∑ i ∈ s, generatorCentralizerSubdegree i) = 1 ∨
      (∑ i ∈ s, generatorCentralizerSubdegree i) = 13571955000 := by
  have h : ∀ t : Finset (Fin 5), 0 ∈ t →
      (∑ i ∈ t, generatorCentralizerSubdegree i) ∣ 13571955000 →
      (∑ i ∈ t, generatorCentralizerSubdegree i) = 1 ∨
        (∑ i ∈ t, generatorCentralizerSubdegree i) = 13571955000 := by
    decide
  exact h s hzero hdiv

/-- A census for the actual presentation proves the centralizer index. -/
theorem generatorCentralizer_index_of_doubleCosetCensus [Finite Carrier]
    (c : GeneratorCentralizerDoubleCosetCensus) :
    generatorCentralizer.index = 13571955000 :=
  (Subgroup.index_eq_sum_of_fiber_card generatorCentralizer c.label
    generatorCentralizerSubdegree c.card_fiber).trans generatorCentralizerSubdegree_sum

/-- A census for the actual presentation proves maximality without using
simplicity, a normal-subgroup dichotomy, or a named-group identification. -/
theorem generatorCentralizer_isCoatom_of_doubleCosetCensus [Finite Carrier]
    (c : GeneratorCentralizerDoubleCosetCensus) : IsCoatom generatorCentralizer := by
  have hindex := generatorCentralizer_index_of_doubleCosetCensus c
  refine ⟨?_, fun K hK => ?_⟩
  · intro htop
    rw [htop, Subgroup.index_top] at hindex
    contradiction
  · obtain ⟨s, hs, hrel⟩ := Subgroup.relIndex_eq_sum_of_doubleCoset_fibers
      generatorCentralizer K hK.le c.label generatorCentralizerSubdegree c.card_fiber
      (fun x y h => (c.same_label_iff x y).mp h)
    rw [c.label_one] at hs
    have hdiv : (∑ i ∈ s, generatorCentralizerSubdegree i) ∣ 13571955000 := by
      rw [← hindex, ← hrel]
      exact Subgroup.relIndex_dvd_index_of_le hK.le
    rcases generatorCentralizerSubdegree_divisor s hs hdiv with hsmall | hfull
    · exact False.elim (hK.not_ge (Subgroup.relIndex_eq_one.mp (hrel.trans hsmall)))
    · apply Subgroup.index_eq_one.mp
      have hm := Subgroup.relIndex_mul_index hK.le
      rw [hrel, hfull, hindex] at hm
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 13571955000)
        (by simpa only [Nat.mul_one] using hm)

end BabyMonster
