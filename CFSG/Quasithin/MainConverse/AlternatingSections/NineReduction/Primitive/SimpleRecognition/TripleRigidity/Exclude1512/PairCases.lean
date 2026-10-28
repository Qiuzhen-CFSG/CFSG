module

public import CFSG.Quasithin.MainConverse.AlternatingSections.NineReduction.Primitive.SimpleRecognition.TripleRigidity.Exclude1512.Generators
public import Mathlib.Tactic.FinCases

/-!
# The fifteen normalized involutions on nine letters

An involution fixing only 2 and sending 0 to 3 pairs the remaining letters
`{1,4,5,6,7,8}`. We enumerate the five possible partners of 1, then the three
pairings of the remaining four letters. Thirteen of these fifteen permutations
have an explicit word of order five together with `cycle`; the other two are
`involution false` and `involution true`. Every word is checked by kernel
reduction, and membership in the generated subgroup gives divisibility by five
through Lagrange's theorem.

This is the finite pairing calculation used to exclude order 1512 in the
alternating case of condition K, Aschbacher–Smith, `refs/quasithin.pdf`, printed
pp.4 and 482. The separate orders of the two surviving generated subgroups
are not needed here.
-/

namespace CFSG.Quasithin.MainConverse.NineReduction.Exclude1512

/-- Pairings in lexicographic order of the successive partners. -/
private def pairing : Fin 15 → Perm :=
  ![Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 5 6 * Equiv.swap 7 8,
    Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 5 7 * Equiv.swap 6 8,
    Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 5 8 * Equiv.swap 6 7,
    Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 4 6 * Equiv.swap 7 8,
    Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 4 7 * Equiv.swap 6 8,
    Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 4 8 * Equiv.swap 6 7,
    Equiv.swap 0 3 * Equiv.swap 1 6 * Equiv.swap 4 5 * Equiv.swap 7 8,
    Equiv.swap 0 3 * Equiv.swap 1 6 * Equiv.swap 4 7 * Equiv.swap 5 8,
    Equiv.swap 0 3 * Equiv.swap 1 6 * Equiv.swap 4 8 * Equiv.swap 5 7,
    Equiv.swap 0 3 * Equiv.swap 1 7 * Equiv.swap 4 5 * Equiv.swap 6 8,
    Equiv.swap 0 3 * Equiv.swap 1 7 * Equiv.swap 4 6 * Equiv.swap 5 8,
    Equiv.swap 0 3 * Equiv.swap 1 7 * Equiv.swap 4 8 * Equiv.swap 5 6,
    Equiv.swap 0 3 * Equiv.swap 1 8 * Equiv.swap 4 5 * Equiv.swap 6 7,
    Equiv.swap 0 3 * Equiv.swap 1 8 * Equiv.swap 4 6 * Equiv.swap 5 7,
    Equiv.swap 0 3 * Equiv.swap 1 8 * Equiv.swap 4 7 * Equiv.swap 5 6]

private theorem reverse_pair {t : Perm} (hinv : Function.Involutive t)
    {a b : Fin 9} (h : t a = b) : t b = a := by
  rw [← h, hinv]

private theorem exhaustive_4 (t : Perm) (hinv : Function.Involutive t)
    (hne : ∀ x : Fin 9, x ≠ 2 → t x ≠ x)
    (h03 : t 0 = 3) (h22 : t 2 = 2) (h14 : t 1 = 4) :
    ∃ i : Fin 15, t = pairing i := by
  have hrev := @reverse_pair t hinv
  have h30 := hrev h03
  have h41 := hrev h14
  have h5 : t 5 = 6 ∨ t 5 = 7 ∨ t 5 = 8 := by
    generalize hy : t 5 = y
    have hyr := hrev hy
    fin_cases y <;> simp_all
  rcases h5 with h56 | h57 | h58
  · have h65 := hrev h56
    have h78 : t 7 = 8 := by
      generalize hy : t 7 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h87 := hrev h78
    refine ⟨0, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h14, h56, h78, h30, h41, h65, h87]
  · have h75 := hrev h57
    have h68 : t 6 = 8 := by
      generalize hy : t 6 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h86 := hrev h68
    refine ⟨1, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h14, h57, h68, h30, h41, h75, h86]
  · have h85 := hrev h58
    have h67 : t 6 = 7 := by
      generalize hy : t 6 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h76 := hrev h67
    refine ⟨2, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h14, h58, h67, h30, h41, h85, h76]

private theorem exhaustive_5 (t : Perm) (hinv : Function.Involutive t)
    (hne : ∀ x : Fin 9, x ≠ 2 → t x ≠ x)
    (h03 : t 0 = 3) (h22 : t 2 = 2) (h15 : t 1 = 5) :
    ∃ i : Fin 15, t = pairing i := by
  have hrev := @reverse_pair t hinv
  have h30 := hrev h03
  have h51 := hrev h15
  have h4 : t 4 = 6 ∨ t 4 = 7 ∨ t 4 = 8 := by
    generalize hy : t 4 = y
    have hyr := hrev hy
    fin_cases y <;> simp_all
  rcases h4 with h46 | h47 | h48
  · have h64 := hrev h46
    have h78 : t 7 = 8 := by
      generalize hy : t 7 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h87 := hrev h78
    refine ⟨3, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h15, h46, h78, h30, h51, h64, h87]
  · have h74 := hrev h47
    have h68 : t 6 = 8 := by
      generalize hy : t 6 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h86 := hrev h68
    refine ⟨4, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h15, h47, h68, h30, h51, h74, h86]
  · have h84 := hrev h48
    have h67 : t 6 = 7 := by
      generalize hy : t 6 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h76 := hrev h67
    refine ⟨5, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h15, h48, h67, h30, h51, h84, h76]

private theorem exhaustive_6 (t : Perm) (hinv : Function.Involutive t)
    (hne : ∀ x : Fin 9, x ≠ 2 → t x ≠ x)
    (h03 : t 0 = 3) (h22 : t 2 = 2) (h16 : t 1 = 6) :
    ∃ i : Fin 15, t = pairing i := by
  have hrev := @reverse_pair t hinv
  have h30 := hrev h03
  have h61 := hrev h16
  have h4 : t 4 = 5 ∨ t 4 = 7 ∨ t 4 = 8 := by
    generalize hy : t 4 = y
    have hyr := hrev hy
    fin_cases y <;> simp_all
  rcases h4 with h45 | h47 | h48
  · have h54 := hrev h45
    have h78 : t 7 = 8 := by
      generalize hy : t 7 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h87 := hrev h78
    refine ⟨6, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h16, h45, h78, h30, h61, h54, h87]
  · have h74 := hrev h47
    have h58 : t 5 = 8 := by
      generalize hy : t 5 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h85 := hrev h58
    refine ⟨7, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h16, h47, h58, h30, h61, h74, h85]
  · have h84 := hrev h48
    have h57 : t 5 = 7 := by
      generalize hy : t 5 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h75 := hrev h57
    refine ⟨8, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h16, h48, h57, h30, h61, h84, h75]

private theorem exhaustive_7 (t : Perm) (hinv : Function.Involutive t)
    (hne : ∀ x : Fin 9, x ≠ 2 → t x ≠ x)
    (h03 : t 0 = 3) (h22 : t 2 = 2) (h17 : t 1 = 7) :
    ∃ i : Fin 15, t = pairing i := by
  have hrev := @reverse_pair t hinv
  have h30 := hrev h03
  have h71 := hrev h17
  have h4 : t 4 = 5 ∨ t 4 = 6 ∨ t 4 = 8 := by
    generalize hy : t 4 = y
    have hyr := hrev hy
    fin_cases y <;> simp_all
  rcases h4 with h45 | h46 | h48
  · have h54 := hrev h45
    have h68 : t 6 = 8 := by
      generalize hy : t 6 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h86 := hrev h68
    refine ⟨9, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h17, h45, h68, h30, h71, h54, h86]
  · have h64 := hrev h46
    have h58 : t 5 = 8 := by
      generalize hy : t 5 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h85 := hrev h58
    refine ⟨10, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h17, h46, h58, h30, h71, h64, h85]
  · have h84 := hrev h48
    have h56 : t 5 = 6 := by
      generalize hy : t 5 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h65 := hrev h56
    refine ⟨11, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h17, h48, h56, h30, h71, h84, h65]

private theorem exhaustive_8 (t : Perm) (hinv : Function.Involutive t)
    (hne : ∀ x : Fin 9, x ≠ 2 → t x ≠ x)
    (h03 : t 0 = 3) (h22 : t 2 = 2) (h18 : t 1 = 8) :
    ∃ i : Fin 15, t = pairing i := by
  have hrev := @reverse_pair t hinv
  have h30 := hrev h03
  have h81 := hrev h18
  have h4 : t 4 = 5 ∨ t 4 = 6 ∨ t 4 = 7 := by
    generalize hy : t 4 = y
    have hyr := hrev hy
    fin_cases y <;> simp_all
  rcases h4 with h45 | h46 | h47
  · have h54 := hrev h45
    have h67 : t 6 = 7 := by
      generalize hy : t 6 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h76 := hrev h67
    refine ⟨12, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h18, h45, h67, h30, h81, h54, h76]
  · have h64 := hrev h46
    have h57 : t 5 = 7 := by
      generalize hy : t 5 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h75 := hrev h57
    refine ⟨13, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h18, h46, h57, h30, h81, h64, h75]
  · have h74 := hrev h47
    have h56 : t 5 = 6 := by
      generalize hy : t 5 = y
      have hyr := hrev hy
      fin_cases y <;> simp_all
    have h65 := hrev h56
    refine ⟨14, ?_⟩
    ext x
    fin_cases x <;> simp [pairing, Equiv.Perm.mul_apply, Equiv.swap_apply_def,
      h22, h03, h18, h47, h56, h30, h81, h74, h65]

private theorem exhaustive (t : Perm) (ht : t ^ 2 = 1)
    (hfix : ∀ x : Fin 9, t x = x ↔ x = 2) (h03 : t 0 = 3) :
    ∃ i : Fin 15, t = pairing i := by
  have hinv : Function.Involutive t := by
    intro x
    simpa only [pow_two, Equiv.Perm.mul_apply, Equiv.Perm.one_apply] using
      congrArg (fun p : Perm => p x) ht
  have hrev := @reverse_pair t hinv
  have h30 := hrev h03
  have h22 := (hfix 2).mpr rfl
  have hne (x : Fin 9) (hx : x ≠ 2) : t x ≠ x := fun h => hx ((hfix x).mp h)
  clear hfix ht
  have h1 : t 1 = 4 ∨ t 1 = 5 ∨ t 1 = 6 ∨ t 1 = 7 ∨ t 1 = 8 := by
    generalize hy : t 1 = y
    have hyr := hrev hy
    fin_cases y <;> simp_all
  rcases h1 with h14 | h15 | h16 | h17 | h18
  · exact exhaustive_4 t hinv hne h03 h22 h14
  · exact exhaustive_5 t hinv hne h03 h22 h15
  · exact exhaustive_6 t hinv hne h03 h22 h16
  · exact exhaustive_7 t hinv hne h03 h22 h17
  · exact exhaustive_8 t hinv hne h03 h22 h18

/-- A list `[i₁, …, iₖ]` denotes the product of the factors `cycle ^ iⱼ * t`. -/
private def word (t : Perm) : List ℕ → Perm
  | [] => 1
  | n :: ns => (cycle ^ n * t) * word t ns

private theorem word_mem (t : Perm) (ns : List ℕ) :
    word t ns ∈ Subgroup.closure {cycle, t} := by
  have hc : cycle ∈ Subgroup.closure {cycle, t} :=
    Subgroup.subset_closure (by simp)
  have ht : t ∈ Subgroup.closure {cycle, t} :=
    Subgroup.subset_closure (by simp)
  induction ns with
  | nil => exact Subgroup.one_mem _
  | cons n ns ih =>
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.pow_mem _ hc n) ht) ih

-- The nested applications in the longest word require a deeper reduction stack.
set_option maxRecDepth 4000 in
private theorem certificates (i : Fin 15) :
    pairing i = involution false ∨ pairing i = involution true ∨
      ∃ ns : List ℕ, word (pairing i) ns ^ 5 = 1 ∧ word (pairing i) ns ≠ 1 := by
  fin_cases i
  · right; right
    refine ⟨[1, 1, 6, 3], ?_, ?_⟩ <;> decide
  · right; right
    refine ⟨[1, 5, 4], ?_, ?_⟩ <;> decide
  · right; right
    refine ⟨[3, 3, 3], ?_, ?_⟩ <;> decide
  · right; right
    refine ⟨[1, 1, 1], ?_, ?_⟩ <;> decide
  · right; right
    refine ⟨[1, 2, 3], ?_, ?_⟩ <;> decide
  · right; right
    refine ⟨[1, 3, 2], ?_, ?_⟩ <;> decide
  · right; right
    refine ⟨[1, 3, 5], ?_, ?_⟩ <;> decide
  · right; right
    refine ⟨[1, 1, 2, 5], ?_, ?_⟩ <;> decide
  · right; right
    refine ⟨[2, 2, 2], ?_, ?_⟩ <;> decide
  · right; right
    refine ⟨[1, 1, 1], ?_, ?_⟩ <;> decide
  · right; right
    refine ⟨[2, 2, 2], ?_, ?_⟩ <;> decide
  · right; right
    refine ⟨[1, 5, 3], ?_, ?_⟩ <;> decide
  · left
    decide
  · right; left
    decide
  · right; right
    refine ⟨[2, 2], ?_, ?_⟩ <;> decide

/-- Every normalized involution is one of the two seeds or generates with the
seven-cycle a subgroup whose order is divisible by five. -/
public theorem normalized_involution_cases (t : Perm) (ht : t ^ 2 = 1)
    (hfix : ∀ x : Fin 9, t x = x ↔ x = 2) (h03 : t 0 = 3) :
    t = involution false ∨ t = involution true ∨
      5 ∣ Nat.card (Subgroup.closure {cycle, t}) := by
  obtain ⟨i, rfl⟩ := exhaustive t ht hfix h03
  rcases certificates i with h | h | ⟨ns, hpow, hne⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · right; right
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    have hord : orderOf (word (pairing i) ns) = 5 := orderOf_eq_prime hpow hne
    rw [← hord]
    exact (Subgroup.closure {cycle, pairing i}).orderOf_dvd_natCard (word_mem _ _)

end CFSG.Quasithin.MainConverse.NineReduction.Exclude1512
