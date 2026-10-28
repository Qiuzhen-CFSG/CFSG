module

public import Theory.GroupAction.SemilinearPointStabilizerExceptional.DegreeEight.Permutations
import Mathlib.Tactic.FinCases

/-!
# The degree-eight involution calculation

Let a permutation subgroup on eight points contain the marked seven-cycle,
have order dividing 168, and have fixed-point-free nonidentity involutions.
It either contains the marked linear seed or all its square-one elements commute.

Conjugation by the seven-cycle pairs infinity with zero. The remaining six
points have fifteen perfect matchings. Ten give short involution words fixing
infinity; three recover the marked inversion; the remaining two give commuting
families of seven conjugates. Both families together produce an element of order
five, excluded by the subgroup order. All finite identities are kernel checked.

This is the finite helper for `DegreeEight.equiv_of_involution_calculation`,
supporting the degree-eight endpoint of GLS, Volume 4, Chapter 1, Theorem 3.2
and Lemma 3.9 (`refs/KGroup/GLS4/Chapter1.tex`, lines 305–468). It does not assume
or itself assert recognition of the original field actor.
-/

namespace MulAction.SemilinearPointStabilizer.DegreeEight

/-- The fifteen matchings pairing infinity with zero. -/
private def matchingValues : Fin 15 → Fin 8 → Fin 8 :=
  ![![7, 2, 1, 4, 3, 6, 5, 0],
    ![7, 2, 1, 5, 6, 3, 4, 0],
    ![7, 2, 1, 6, 5, 4, 3, 0],
    ![7, 3, 4, 1, 2, 6, 5, 0],
    ![7, 3, 5, 1, 6, 2, 4, 0],
    ![7, 3, 6, 1, 5, 4, 2, 0],
    ![7, 4, 3, 2, 1, 6, 5, 0],
    ![7, 4, 5, 6, 1, 2, 3, 0],
    ![7, 4, 6, 5, 1, 3, 2, 0],
    ![7, 5, 3, 2, 6, 1, 4, 0],
    ![7, 5, 4, 6, 2, 1, 3, 0],
    ![7, 5, 6, 4, 3, 1, 2, 0],
    ![7, 6, 3, 2, 5, 4, 1, 0],
    ![7, 6, 4, 5, 2, 3, 1, 0],
    ![7, 6, 5, 4, 3, 2, 1, 0]]

private theorem matchingValues_involutive : ∀ k : Fin 15,
    Function.Involutive (matchingValues k) := by
  change ∀ (k : Fin 15) (i : Fin 8), matchingValues k (matchingValues k i) = i
  decide

private def matching (k : Fin 15) : Perm where
  toFun := matchingValues k
  invFun := matchingValues k
  left_inv := matchingValues_involutive k
  right_inv := matchingValues_involutive k

/-- Pair the least unpaired point successively; there are five, three, then
one choices. No enumeration of all permutations or subgroups is used. -/
private theorem matching_exhaustive (t : Perm) (ht : t ^ 2 = 1)
    (hf : ∀ i : Fin 8, t i ≠ i) (h7 : t 7 = 0) :
    ∃ k : Fin 15, t = matching k := by
  have hinv (i : Fin 8) : t (t i) = i := by
    have h := congrArg (fun p : Perm => p i) ht
    simpa only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using h
  have h0 : t 0 = 7 := by simpa only [h7] using hinv 7
  have h1 : t 1 = 2 ∨ t 1 = 3 ∨ t 1 = 4 ∨ t 1 = 5 ∨ t 1 = 6 := by
    have := hf 1
    have := t.injective.ne (by decide : (1 : Fin 8) ≠ 0)
    have := t.injective.ne (by decide : (1 : Fin 8) ≠ 7)
    omega
  rcases h1 with h1 | h1 | h1 | h1 | h1
  · have h2 : t 2 = 1 := by simpa only [h1] using hinv 1
    have h3 : t 3 = 4 ∨ t 3 = 5 ∨ t 3 = 6 := by
      have := hf 3
      have := t.injective.ne (by decide : (3 : Fin 8) ≠ 0)
      have := t.injective.ne (by decide : (3 : Fin 8) ≠ 1)
      have := t.injective.ne (by decide : (3 : Fin 8) ≠ 2)
      have := t.injective.ne (by decide : (3 : Fin 8) ≠ 7)
      omega
    rcases h3 with h3 | h3 | h3
    · have h4 : t 4 = 3 := by simpa only [h3] using hinv 3
      have h5 : t 5 = 6 := by
        have := hf 5
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 3)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 4)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 7)
        omega
      have h6 : t 6 = 5 := by simpa only [h5] using hinv 5
      refine ⟨0, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
    · have h5 : t 5 = 3 := by simpa only [h3] using hinv 3
      have h4 : t 4 = 6 := by
        have := hf 4
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 3)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 5)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 7)
        omega
      have h6 : t 6 = 4 := by simpa only [h4] using hinv 4
      refine ⟨1, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
    · have h6 : t 6 = 3 := by simpa only [h3] using hinv 3
      have h4 : t 4 = 5 := by
        have := hf 4
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 3)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 6)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 7)
        omega
      have h5 : t 5 = 4 := by simpa only [h4] using hinv 4
      refine ⟨2, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
  · have h3 : t 3 = 1 := by simpa only [h1] using hinv 1
    have h2 : t 2 = 4 ∨ t 2 = 5 ∨ t 2 = 6 := by
      have := hf 2
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 0)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 1)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 3)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 7)
      omega
    rcases h2 with h2 | h2 | h2
    · have h4 : t 4 = 2 := by simpa only [h2] using hinv 2
      have h5 : t 5 = 6 := by
        have := hf 5
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 3)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 4)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 7)
        omega
      have h6 : t 6 = 5 := by simpa only [h5] using hinv 5
      refine ⟨3, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
    · have h5 : t 5 = 2 := by simpa only [h2] using hinv 2
      have h4 : t 4 = 6 := by
        have := hf 4
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 3)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 5)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 7)
        omega
      have h6 : t 6 = 4 := by simpa only [h4] using hinv 4
      refine ⟨4, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
    · have h6 : t 6 = 2 := by simpa only [h2] using hinv 2
      have h4 : t 4 = 5 := by
        have := hf 4
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 3)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 6)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 7)
        omega
      have h5 : t 5 = 4 := by simpa only [h4] using hinv 4
      refine ⟨5, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
  · have h4 : t 4 = 1 := by simpa only [h1] using hinv 1
    have h2 : t 2 = 3 ∨ t 2 = 5 ∨ t 2 = 6 := by
      have := hf 2
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 0)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 1)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 4)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 7)
      omega
    rcases h2 with h2 | h2 | h2
    · have h3 : t 3 = 2 := by simpa only [h2] using hinv 2
      have h5 : t 5 = 6 := by
        have := hf 5
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 3)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 4)
        have := t.injective.ne (by decide : (5 : Fin 8) ≠ 7)
        omega
      have h6 : t 6 = 5 := by simpa only [h5] using hinv 5
      refine ⟨6, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
    · have h5 : t 5 = 2 := by simpa only [h2] using hinv 2
      have h3 : t 3 = 6 := by
        have := hf 3
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 4)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 5)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 7)
        omega
      have h6 : t 6 = 3 := by simpa only [h3] using hinv 3
      refine ⟨7, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
    · have h6 : t 6 = 2 := by simpa only [h2] using hinv 2
      have h3 : t 3 = 5 := by
        have := hf 3
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 4)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 6)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 7)
        omega
      have h5 : t 5 = 3 := by simpa only [h3] using hinv 3
      refine ⟨8, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
  · have h5 : t 5 = 1 := by simpa only [h1] using hinv 1
    have h2 : t 2 = 3 ∨ t 2 = 4 ∨ t 2 = 6 := by
      have := hf 2
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 0)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 1)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 5)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 7)
      omega
    rcases h2 with h2 | h2 | h2
    · have h3 : t 3 = 2 := by simpa only [h2] using hinv 2
      have h4 : t 4 = 6 := by
        have := hf 4
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 3)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 5)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 7)
        omega
      have h6 : t 6 = 4 := by simpa only [h4] using hinv 4
      refine ⟨9, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
    · have h4 : t 4 = 2 := by simpa only [h2] using hinv 2
      have h3 : t 3 = 6 := by
        have := hf 3
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 4)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 5)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 7)
        omega
      have h6 : t 6 = 3 := by simpa only [h3] using hinv 3
      refine ⟨10, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
    · have h6 : t 6 = 2 := by simpa only [h2] using hinv 2
      have h3 : t 3 = 4 := by
        have := hf 3
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 5)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 6)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 7)
        omega
      have h4 : t 4 = 3 := by simpa only [h3] using hinv 3
      refine ⟨11, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
  · have h6 : t 6 = 1 := by simpa only [h1] using hinv 1
    have h2 : t 2 = 3 ∨ t 2 = 4 ∨ t 2 = 5 := by
      have := hf 2
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 0)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 1)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 6)
      have := t.injective.ne (by decide : (2 : Fin 8) ≠ 7)
      omega
    rcases h2 with h2 | h2 | h2
    · have h3 : t 3 = 2 := by simpa only [h2] using hinv 2
      have h4 : t 4 = 5 := by
        have := hf 4
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 3)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 6)
        have := t.injective.ne (by decide : (4 : Fin 8) ≠ 7)
        omega
      have h5 : t 5 = 4 := by simpa only [h4] using hinv 4
      refine ⟨12, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
    · have h4 : t 4 = 2 := by simpa only [h2] using hinv 2
      have h3 : t 3 = 5 := by
        have := hf 3
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 4)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 6)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 7)
        omega
      have h5 : t 5 = 3 := by simpa only [h3] using hinv 3
      refine ⟨13, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption
    · have h5 : t 5 = 2 := by simpa only [h2] using hinv 2
      have h3 : t 3 = 4 := by
        have := hf 3
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 0)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 1)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 2)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 5)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 6)
        have := t.injective.ne (by decide : (3 : Fin 8) ≠ 7)
        omega
      have h4 : t 4 = 3 := by simpa only [h3] using hinv 3
      refine ⟨14, ?_⟩
      apply Equiv.ext
      intro i
      fin_cases i <;> assumption

private def badIndex : Fin 10 → Fin 15 := ![0, 1, 2, 3, 6, 7, 8, 10, 13, 14]

private def badWord : Fin 10 → List Bool :=
  ![[true, false, false, false, false, true, false, false, true, false, true],
    [true, false, true, false, false, true, false, true],
    [false, true, false, false, true, false, false, true, false, true],
    [true, false, true, false, false, true, false, true],
    [false, true, false, false, true, false, false, true, false, true],
    [true, false, false, false, false, false, true, false, true, false, true],
    [false, false, false, true, false, true, false, false, true],
    [false, false, false, true, false, false, true, false, true],
    [false, false, true, false, true, false, false, true, false, true],
    [false, true, false, true, false, true]]

/-- Each rejected matching produces a nonidentity involution fixing infinity. -/
private theorem bad_certificate : ∀ k : Fin 10,
    let w := word cycle (matching (badIndex k)) (badWord k)
    w ^ 2 = 1 ∧ w ≠ 1 ∧ w 7 = 7 := by
  intro k
  fin_cases k <;> dsimp [badIndex, badWord, matching, matchingValues] <;> decide

private def seedIndex : Fin 3 → Fin 15 := ![4, 11, 12]

private def seedWord : Fin 3 → List Bool :=
  ![[false, true, false, false, false, false, true, false],
    [false, true, false, false, true, false], [true]]

/-- The other three nonaffine matchings recover the literal marked inversion. -/
private theorem seed_certificate : ∀ k : Fin 3,
    word cycle (matching (seedIndex k)) (seedWord k) = inversion := by decide

private theorem index_cases : ∀ k : Fin 15,
    k = 5 ∨ k = 9 ∨ (∃ j : Fin 3, k = seedIndex j) ∨
      (∃ j : Fin 10, k = badIndex j) := by decide

private theorem normalized_survivors (U : Subgroup Perm) (hc : cycle ∈ U)
    (hfree : ∀ t ∈ U, t ^ 2 = 1 → t ≠ 1 → ∀ i : Fin 8, t i ≠ i)
    (hseed : ¬linearSeed ≤ U) (t : Perm) (htU : t ∈ U)
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1) (h7 : t 7 = 0) :
    t = matching 5 ∨ t = matching 9 := by
  obtain ⟨k, rfl⟩ := matching_exhaustive t ht (hfree t htU ht ht1) h7
  rcases index_cases k with rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl
  · have hi : inversion ∈ U := by
      rw [← seed_certificate j]
      exact word_mem U hc htU _
    apply (hseed ?_).elim
    apply (Subgroup.closure_le U).mpr
    intro g hg
    rcases hg with rfl | rfl
    · exact hc
    · exact hi
  · obtain ⟨h2, hne, hfix⟩ := bad_certificate j
    exact (hfree _ (word_mem U hc htU _) h2 hne 7 hfix).elim

private def cyclicConjugate (k : Fin 7) (t : Perm) : Perm :=
  cycle ^ k.val * t * (cycle ^ k.val)⁻¹

private theorem cycle_transitive : ∀ i : Fin 8, i ≠ 7 →
    ∃ k : Fin 7, (cycle ^ k.val) 0 = i ∧ (cycle ^ k.val) 7 = 7 := by decide

/-- Normalize a nonidentity involution by the seven-cycle and then undo the
conjugation, retaining membership of its normalized representative. -/
private theorem involution_cases (U : Subgroup Perm) (hc : cycle ∈ U)
    (hfree : ∀ t ∈ U, t ^ 2 = 1 → t ≠ 1 → ∀ i : Fin 8, t i ≠ i)
    (hseed : ¬linearSeed ≤ U) (t : Perm) (htU : t ∈ U)
    (ht : t ^ 2 = 1) (ht1 : t ≠ 1) :
    ∃ k : Fin 7,
      (matching 5 ∈ U ∧ t = cyclicConjugate k (matching 5)) ∨
      (matching 9 ∈ U ∧ t = cyclicConjugate k (matching 9)) := by
  obtain ⟨k, hk0, hk7⟩ := cycle_transitive (t 7) (hfree t htU ht ht1 7)
  let q := cycle ^ k.val
  let u := MulAut.conj q⁻¹ t
  have hq : q ∈ U := U.pow_mem hc _
  have huU : u ∈ U := by
    simpa only [u, MulAut.conj_apply, inv_inv] using
      U.mul_mem (U.mul_mem (U.inv_mem hq) htU) hq
  have hu2 : u ^ 2 = 1 := by
    dsimp only [u]
    rw [← map_pow, ht, map_one]
  have hu1 : u ≠ 1 := by
    intro h
    apply ht1
    apply (MulAut.conj q⁻¹).injective
    simpa only [map_one] using h
  have hu7 : u 7 = 0 := by
    change (q⁻¹ * t * (q⁻¹)⁻¹) 7 = 0
    simp only [inv_inv, Equiv.Perm.mul_apply]
    rw [show q 7 = 7 from hk7, ← show q 0 = t 7 from hk0]
    exact q.symm_apply_apply 0
  have hrecover : t = cyclicConjugate k u := by
    simp [cyclicConjugate, u, MulAut.conj_apply, q, mul_assoc]
  rcases normalized_survivors U hc hfree hseed u huU hu2 hu1 hu7 with hu | hu
  · rw [hu] at huU hrecover
    exact ⟨k, Or.inl ⟨huU, hrecover⟩⟩
  · rw [hu] at huU hrecover
    exact ⟨k, Or.inr ⟨huU, hrecover⟩⟩

private theorem affine_families_commute : ∀ k l : Fin 7,
    Commute (cyclicConjugate k (matching 5)) (cyclicConjugate l (matching 5)) ∧
    Commute (cyclicConjugate k (matching 9)) (cyclicConjugate l (matching 9)) := by
  change ∀ k l : Fin 7,
    cyclicConjugate k (matching 5) * cyclicConjugate l (matching 5) =
      cyclicConjugate l (matching 5) * cyclicConjugate k (matching 5) ∧
    cyclicConjugate k (matching 9) * cyclicConjugate l (matching 9) =
      cyclicConjugate l (matching 9) * cyclicConjugate k (matching 9)
  decide

private theorem mixed_order : orderOf (cycle * matching 5 * matching 9) = 5 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  apply orderOf_eq_prime <;> dsimp [matching, matchingValues] <;> decide

/-- The two affine families together produce an element of order five. -/
private theorem not_both_affine (U : Subgroup Perm) (hc : cycle ∈ U)
    (hcard : Nat.card U ∣ 168) (ha : matching 5 ∈ U) (hb : matching 9 ∈ U) :
    False := by
  have h := (U.orderOf_dvd_natCard (U.mul_mem (U.mul_mem hc ha) hb)).trans hcard
  rw [mixed_order] at h
  exact (by decide : ¬5 ∣ 168) h

/-- A subgroup containing the marked seven-cycle, of order dividing 168, with
fixed-point-free nonidentity involutions either contains the marked linear
seed or has commuting square-one elements. This is the finite calculation
needed by `equiv_of_involution_calculation`; it assumes no recognition theorem. -/
public theorem involution_calculation (U : Subgroup Perm) (hc : cycle ∈ U)
    (hcard : Nat.card U ∣ 168)
    (hfree : ∀ t ∈ U, t ^ 2 = 1 → t ≠ 1 → ∀ i : Fin 8, t i ≠ i) :
    linearSeed ≤ U ∨ (∀ a b : U, a ^ 2 = 1 → b ^ 2 = 1 → Commute a b) := by
  by_cases hseed : linearSeed ≤ U
  · exact Or.inl hseed
  right
  intro a b ha hb
  change a * b = b * a
  apply Subtype.ext
  change (a : Perm) * (b : Perm) = (b : Perm) * (a : Perm)
  by_cases ha1 : (a : Perm) = 1
  · simp [ha1]
  by_cases hb1 : (b : Perm) = 1
  · simp [hb1]
  have ha2 : (a : Perm) ^ 2 = 1 := congrArg Subtype.val ha
  have hb2 : (b : Perm) ^ 2 = 1 := congrArg Subtype.val hb
  obtain ⟨k, ⟨h5a, hka⟩ | ⟨h9a, hka⟩⟩ :=
    involution_cases U hc hfree hseed a a.property ha2 ha1
  · obtain ⟨l, ⟨_, hlb⟩ | ⟨h9b, hlb⟩⟩ :=
      involution_cases U hc hfree hseed b b.property hb2 hb1
    · rw [hka, hlb]
      exact (affine_families_commute k l).1
    · exact (not_both_affine U hc hcard h5a h9b).elim
  · obtain ⟨l, ⟨h5b, hlb⟩ | ⟨_, hlb⟩⟩ :=
      involution_cases U hc hfree hseed b b.property hb2 hb1
    · exact (not_both_affine U hc hcard h5b h9a).elim
    · rw [hka, hlb]
      exact (affine_families_commute k l).2

end MulAction.SemilinearPointStabilizer.DegreeEight
