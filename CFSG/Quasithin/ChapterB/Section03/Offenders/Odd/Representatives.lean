module

public import CFSG.Quasithin.ChapterB.Section03.Offenders.Defs
public import CFSG.Quasithin.ChapterB.Section03.Offenders.FixedTests
import Mathlib.FieldTheory.Finiteness
import Mathlib.Tactic.FinCases

/-!
# Odd-degree disjoint-transposition representatives

For degrees five and seven, small multiplication tables enumerate the groups
`A_m` and identify them with their defining subgroup closures. Their orders
are `2^m`, and their elements commute and square to one. On the full binary
permutation module, the fixed-vector test is equality within each swapped
pair. Counting these binary vectors and applying rank-nullity gives fixed
codimension `m`. All finite certificates are checked by Lean's kernel.

The table construction follows the corresponding degree-six construction in
`Offenders.Six.Representatives`; this module has no degree-six dependency.

Source: Aschbacher–Smith, *The Classification of Quasithin Groups*,
1 March 2004 manuscript, Proposition B.3.2(1), printed pp. 83–84.
-/

public section

namespace CFSG.Quasithin.ChapterB.Offenders.Odd
open BinaryPermutation Representation.BinaryOffender

private def transpositionAt (n i : ℕ) : Equiv.Perm (Fin n) :=
  if hi : i < n / 2 then pairSwap n ⟨i, hi⟩ else 1

private def words (n : ℕ) : Fin 8 → Equiv.Perm (Fin n) :=
  let a := transpositionAt n 0
  let b := transpositionAt n 1
  let c := transpositionAt n 2
  ![1, a, b, a*b, c, a*c, b*c, a*b*c]

private def initialWords (n : ℕ) (m : Fin 4) : Fin (2 ^ m.val) → Equiv.Perm (Fin n) :=
  fun i => words n ⟨i.val, lt_of_lt_of_le i.isLt (by have := m.isLt; interval_cases m.val <;> decide)⟩

private def tableSubgroup {G : Type*} [Group G] {k : ℕ} (f : Fin k → G)
    (hone : ∃ i, f i = 1)
    (hmul : ∀ i j, ∃ l, f i * f j = f l)
    (hinv : ∀ i, ∃ j, (f i)⁻¹ = f j) : Subgroup G where
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

private def initialTable (n : ℕ) (hn : n = 5 ∨ n = 7) (m : Fin 4) :
    Subgroup (Equiv.Perm (Fin n)) := tableSubgroup (initialWords n m)
  (by fin_cases m <;> exact ⟨0, rfl⟩)
  (by rcases hn with rfl | rfl <;> revert m <;> decide)
  (by rcases hn with rfl | rfl <;> revert m <;> decide)

private theorem initialTable_eq (n : ℕ) (hn : n = 5 ∨ n = 7)
    (m : Fin 4) (hm : m.val ≤ n / 2) :
    initialTable n hn m = disjointTranspositions n m.val := by
  apply le_antisymm
  · rintro g ⟨i, rfl⟩
    have ht (j : ℕ) (hj : j < m.val) :
        transpositionAt n j ∈ disjointTranspositions n m.val := by
      have hjn : j < n / 2 := hj.trans_le hm
      simpa only [transpositionAt, dif_pos hjn] using pairSwap_mem ⟨j, hjn⟩ hj
    fin_cases m <;> fin_cases i <;>
      dsimp only [initialWords, words] <;>
      first | exact Subgroup.one_mem _ | exact ht 0 (by decide) |
        exact ht 1 (by decide) | exact ht 2 (by decide) |
        exact Subgroup.mul_mem _ (ht 0 (by decide)) (ht 1 (by decide)) |
        exact Subgroup.mul_mem _ (ht 0 (by decide)) (ht 2 (by decide)) |
        exact Subgroup.mul_mem _ (ht 1 (by decide)) (ht 2 (by decide)) |
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (ht 0 (by decide)) (ht 1 (by decide)))
          (ht 2 (by decide))
  · apply (Subgroup.closure_le _).2
    rintro g ⟨i, hi, rfl⟩
    rcases hn with rfl | rfl <;> fin_cases m <;> fin_cases i <;> dsimp at hi hm <;> try omega
    all_goals first | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨4, rfl⟩

/-- The order of `A_m`, including the trivial initial segment. -/
theorem card_disjointTranspositions {n m : ℕ} (hn : n = 5 ∨ n = 7)
    (hm : m ≤ n / 2) : Nat.card (disjointTranspositions n m) = 2 ^ m := by
  have hm4 : m < 4 := by rcases hn with rfl | rfl <;> omega
  rw [← initialTable_eq n hn ⟨m, hm4⟩ hm]
  have hi : Function.Injective (initialWords n ⟨m, hm4⟩) := by
    rcases hn with rfl | rfl <;> interval_cases m <;> first | omega | decide +revert
  exact (Nat.card_congr (Equiv.ofInjective _ hi)).symm.trans (by simp)

/-- The binary rank formula in B.3.2(1). -/
theorem rank_disjointTranspositions {n m : ℕ} (hn : n = 5 ∨ n = 7)
    (hm : m ≤ n / 2) : rank (disjointTranspositions n m) = m := by
  rw [rank, card_disjointTranspositions hn hm, Nat.log_pow (by decide : 1 < 2)]

/-- The disjoint-transposition groups are elementary abelian. -/
theorem elementary_disjointTranspositions {n m : ℕ} (hn : n = 5 ∨ n = 7)
    (hm : m ≤ n / 2) : IsElementaryAbelian 2 (disjointTranspositions n m) := by
  have hm4 : m < 4 := by rcases hn with rfl | rfl <;> omega
  rw [← initialTable_eq n hn ⟨m, hm4⟩ hm]
  have hc : ∀ i j, initialWords n ⟨m, hm4⟩ i * initialWords n ⟨m, hm4⟩ j =
      initialWords n ⟨m, hm4⟩ j * initialWords n ⟨m, hm4⟩ i := by
    rcases hn with rfl | rfl <;> interval_cases m <;> decide +revert
  have hs : ∀ i, initialWords n ⟨m, hm4⟩ i ^ 2 = 1 := by
    rcases hn with rfl | rfl <;> interval_cases m <;> decide +revert
  refine { toIsMulCommutative := ⟨⟨?_⟩⟩, exponent_dvd_p := ?_ }
  · rintro ⟨a, i, rfl⟩ ⟨b, j, rfl⟩
    exact Subtype.ext (hc i j)
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    rintro ⟨a, i, rfl⟩
    exact Subtype.ext (hs i)

/-- For positive `m`, the group `A_m` is nontrivial elementary abelian. -/
theorem isElementaryTwo_disjointTranspositions {n m : ℕ} (hn : n = 5 ∨ n = 7)
    (hm0 : 1 ≤ m) (hm : m ≤ n / 2) :
    IsElementaryTwo (disjointTranspositions n m) := by
  refine ⟨?_, elementary_disjointTranspositions hn hm⟩
  intro h
  have hr := rank_disjointTranspositions hn hm
  rw [h, Representation.BinaryOffender.rank_bot] at hr
  omega

private def pairTest (n m : ℕ) (v : Full (Fin n)) : Prop :=
  ∀ i : Fin (n / 2), i.val < m →
    v ⟨2 * i.val, by omega⟩ = v ⟨2 * i.val + 1, by omega⟩

private instance (n m : ℕ) (v : Full (Fin n)) : Decidable (pairTest n m v) :=
  inferInstanceAs (Decidable (∀ i : Fin (n / 2), i.val < m → _))

set_option maxRecDepth 4096 in
/-- Pairwise coordinate equalities leave `n - m` free binary coordinates. -/
theorem finrank_full_fixedSpace_disjointTranspositions {n m : ℕ}
    (hn : n = 5 ∨ n = 7) (hm : m ≤ n / 2) :
    Module.finrank (ZMod 2)
      (fixedSpace (representation (Fin n)) (disjointTranspositions n m)) = n - m := by
  let e : {v : Full (Fin n) // pairTest n m v} ≃
      fixedSpace (representation (Fin n)) (disjointTranspositions n m) :=
    Equiv.subtypeEquivRight (fun v => (full_fixed_disjointTranspositions_iff n m v).symm)
  have hcount : Fintype.card {v : Full (Fin n) // pairTest n m v} = 2 ^ (n - m) := by
    rcases hn with rfl | rfl <;> interval_cases m <;> decide
  have hc := Module.natCard_eq_pow_finrank (K := ZMod 2)
    (V := fixedSpace (representation (Fin n)) (disjointTranspositions n m))
  have he := Nat.card_congr e
  rw [Nat.card_eq_fintype_card, hcount, hc] at he
  norm_num at he
  exact he.symm

/-- The full permutation module has fixed codimension `m` under `A_m`. -/
theorem fixedCodim_full_disjointTranspositions {n m : ℕ}
    (hn : n = 5 ∨ n = 7) (hm : m ≤ n / 2) :
    fixedCodim (representation (Fin n)) (disjointTranspositions n m) = m := by
  have h := fixedCodim_add_finrank (representation (Fin n)) (disjointTranspositions n m)
  rw [finrank_full_fixedSpace_disjointTranspositions hn hm, finrank_full, Fintype.card_fin] at h
  omega

end CFSG.Quasithin.ChapterB.Offenders.Odd
