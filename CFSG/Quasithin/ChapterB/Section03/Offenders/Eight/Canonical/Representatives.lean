module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Eight
import Mathlib.Tactic.FinCases

/-!
# Concrete degree-eight elementary abelian representatives

The four disjoint swaps give sixteen distinct binary words. Initial segments
identify the defining closures of `A_m` with groups of order `2^m`. Replacing
the first two swaps by the regular Klein four generators gives the exceptional
rank-four group. All finite word identities are checked by the kernel.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2(1),(2), printed pp. 83–84.
-/

@[expose] public section
namespace CFSG.Quasithin.ChapterB.Offenders.Eight
open Representation.BinaryOffender

abbrev Perm := Equiv.Perm (Fin 8)

/-- Binary words in four generators, in increasing binary order. -/
def cubeWords (a b c d : Perm) (i : Fin 16) : Perm :=
  (if i.val % 2 = 1 then a else 1) *
  (if i.val / 2 % 2 = 1 then b else 1) *
  (if i.val / 4 % 2 = 1 then c else 1) *
  (if i.val / 8 % 2 = 1 then d else 1)

/-- The independent disjoint swaps, indexed by their binary supports. -/
def dWords : Fin 16 → Perm :=
  cubeWords (pairSwap 8 0) (pairSwap 8 1) (pairSwap 8 2) (pairSwap 8 3)

/-- The sixteen words of the exceptional group. -/
def exceptionalWords : Fin 16 → Perm :=
  cubeWords (kleinFirst 8 (by decide)) (kleinSecond 8 (by decide))
    (pairSwap 8 2) (pairSwap 8 3)

def initialWords (m : Fin 5) : Fin (2 ^ m.val) → Perm := fun i =>
  dWords ⟨i.val, lt_of_lt_of_le i.isLt (by have := m.isLt; interval_cases m.val <;> decide)⟩

private def tableSubgroup {k : ℕ} (f : Fin k → Perm)
    (hone : ∃ i, f i = 1)
    (hmul : ∀ i j, ∃ l, f i * f j = f l)
    (hinv : ∀ i, ∃ j, (f i)⁻¹ = f j) : Subgroup Perm where
  carrier := Set.range f
  one_mem' := hone
  mul_mem' := by
    rintro a b ⟨i, rfl⟩ ⟨j, rfl⟩
    obtain ⟨l, hl⟩ := hmul i j
    exact ⟨l, hl.symm⟩
  inv_mem' := by
    rintro a ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hinv i
    exact ⟨j, hj.symm⟩

private def initialTable (m : Fin 5) : Subgroup Perm := tableSubgroup (initialWords m)
  (by fin_cases m <;> exact ⟨0, rfl⟩)
  (by revert m; decide +kernel)
  (by revert m; decide +kernel)

private theorem initialTable_eq (m : Fin 5) :
    initialTable m = disjointTranspositions 8 m.val := by
  apply le_antisymm
  · rintro g ⟨i, rfl⟩
    have ht (j : Fin 4) (hj : j.val < m.val) := pairSwap_mem (n := 8) (m := m.val) j hj
    fin_cases m <;> fin_cases i <;>
      simp only [initialWords, dWords, cubeWords, ite_true, ite_false, Nat.reduceMod,
        Nat.reduceDiv, Nat.reduceEqDiff, mul_one, one_mul]
    all_goals repeat' first | apply Subgroup.mul_mem | exact Subgroup.one_mem _ |
      exact ht 0 (by decide) | exact ht 1 (by decide) |
      exact ht 2 (by decide) | exact ht 3 (by decide)
  · apply (Subgroup.closure_le _).2
    rintro g ⟨i, hi, rfl⟩
    fin_cases m <;> fin_cases i <;> dsimp at hi <;> try omega
    all_goals first
      | (refine ⟨1, ?_⟩; decide)
      | (refine ⟨2, ?_⟩; decide)
      | (refine ⟨4, ?_⟩; decide)
      | (refine ⟨8, ?_⟩; decide)

/-- Membership in `A_m` is exactly membership in its binary word table. -/
theorem mem_disjointTranspositions_iff (m : Fin 5) (g : Perm) :
    g ∈ disjointTranspositions 8 m.val ↔ ∃ i, initialWords m i = g := by
  rw [← initialTable_eq]
  rfl

/-- Distinct binary supports give distinct permutations. -/
theorem dWords_injective : Function.Injective dWords := by decide +kernel

theorem card_disjointTranspositions (m : Fin 5) :
    Nat.card (disjointTranspositions 8 m.val) = 2 ^ m.val := by
  rw [← initialTable_eq]
  have hi : Function.Injective (initialWords m) := by
    intro i j h
    exact Fin.ext (congrArg (fun k : Fin 16 => k.val) (dWords_injective h))
  exact (Nat.card_congr (Equiv.ofInjective _ hi)).symm.trans (by simp)

/-- The rank calculation has no cardinality hypothesis. -/
theorem rank_disjointTranspositions (m : Fin 5) :
    rank (disjointTranspositions 8 m.val) = m.val :=
  rank_eq_of_card_eq_two_pow (card_disjointTranspositions m)

theorem rank_D : rank (D 8) = 4 := rank_disjointTranspositions 4

theorem isElementaryTwo_disjointTranspositions (m : Fin 5) (hm : 0 < m.val) :
    IsElementaryTwo (disjointTranspositions 8 m.val) := by
  apply isElementaryTwo_D8.of_le (disjointTranspositions_le_D _ _)
  intro h
  have hr := rank_disjointTranspositions m
  rw [h, Representation.BinaryOffender.rank_bot] at hr
  omega

private def exceptionalTable : Subgroup Perm := tableSubgroup exceptionalWords
  ⟨0, rfl⟩ (by decide +kernel) (by decide +kernel)

private theorem exceptionalTable_eq : exceptionalTable = exceptional 8 (by decide) := by
  have h0 : kleinFirst 8 (by decide) ∈ exceptional 8 (by decide) :=
    Subgroup.subset_closure (Or.inl (Or.inl rfl))
  have h1 : kleinSecond 8 (by decide) ∈ exceptional 8 (by decide) :=
    Subgroup.subset_closure (Or.inl (Or.inr (Set.mem_singleton _)))
  have h2 : pairSwap 8 2 ∈ exceptional 8 (by decide) :=
    Subgroup.subset_closure (Or.inr ⟨2, le_rfl, rfl⟩)
  have h3 : pairSwap 8 3 ∈ exceptional 8 (by decide) :=
    Subgroup.subset_closure (Or.inr ⟨3, by decide, rfl⟩)
  apply le_antisymm
  · rintro g ⟨i, rfl⟩
    fin_cases i <;>
      simp only [exceptionalWords, cubeWords, ite_true, ite_false, Nat.reduceMod,
        Nat.reduceDiv, Nat.reduceEqDiff, mul_one, one_mul]
    all_goals repeat' first
      | exact h0
      | exact h1
      | exact h2
      | exact h3
      | exact Subgroup.one_mem _
      | apply Subgroup.mul_mem
  · apply (Subgroup.closure_le _).2
    rintro g (hg | ⟨i, hi, rfl⟩)
    · rcases hg with rfl | hg
      · exact ⟨1, by simp [exceptionalWords, cubeWords]⟩
      · rw [Set.mem_singleton_iff] at hg
        subst g
        exact ⟨2, by simp [exceptionalWords, cubeWords]⟩
    · fin_cases i <;> dsimp at hi
      all_goals first
        | omega
        | (refine ⟨4, ?_⟩; decide)
        | (refine ⟨8, ?_⟩; decide)

theorem mem_exceptional_iff (g : Perm) :
    g ∈ exceptional 8 (by decide) ↔ ∃ i, exceptionalWords i = g := by
  rw [← exceptionalTable_eq]
  rfl

theorem card_exceptional : Nat.card (exceptional 8 (by decide)) = 16 := by
  rw [← exceptionalTable_eq]
  exact (Nat.card_congr (Equiv.ofInjective exceptionalWords (by decide +kernel))).symm.trans
    (by simp)

theorem rank_exceptional : rank (exceptional 8 (by decide)) = 4 :=
  rank_eq_of_card_eq_two_pow card_exceptional

theorem isElementaryTwo_exceptional : IsElementaryTwo (exceptional 8 (by decide)) := by
  refine ⟨?_, ?_⟩
  · intro h
    have hc := card_exceptional
    rw [h, Subgroup.card_bot] at hc
    contradiction
  · rw [← exceptionalTable_eq]
    have hc : ∀ i j, exceptionalWords i * exceptionalWords j =
        exceptionalWords j * exceptionalWords i := by decide +kernel
    have hs : ∀ i, exceptionalWords i ^ 2 = 1 := by decide +kernel
    refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
    · rintro ⟨a, i, rfl⟩ ⟨b, j, rfl⟩
      exact Subtype.ext (hc i j)
    · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
      rintro ⟨a, i, rfl⟩
      exact Subtype.ext (hs i)

end CFSG.Quasithin.ChapterB.Offenders.Eight
