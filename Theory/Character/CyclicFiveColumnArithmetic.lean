module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic
/-!
# Five signs from ordinary column orthogonality

An integer column of squared norm five containing the principal value one
has only signs and zeros if its degree-weighted sum vanishes and the
principal degree is one. An entry of absolute value two would exhaust the
remaining norm, forcing the impossible degree equation `1 ± 2n = 0`.
There are therefore exactly five nonzero entries, enumerated principal first.

Source: Fong (1967), printed p.75, citing Brauer (1942).
The enumeration follows `CyclicSevenColumnArithmetic`.
-/

public section
open scoped BigOperators
namespace CyclicFiveColumnArithmetic

private theorem signs {J : Type*} [Fintype J]
    (b n : J → ℤ) (p : J) (hp : b p = 1) (hnp : n p = 1)
    (hs : ∑ i, b i ^ 2 = 5) (hd : ∑ i, n i * b i = 0) (i : J) :
    b i = 0 ∨ b i = 1 ∨ b i = -1 := by
  classical
  by_cases hip : i = p
  · simp [hip, hp]
  have hi : b i ^ 2 ≤ 4 := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({i,p} : Finset J) ⊆ Finset.univ from Finset.subset_univ _)
      (fun j _ _ => sq_nonneg (b j))
    simp only [Finset.sum_pair hip, hp, one_pow, hs] at hh
    omega
  have hlo : -2 ≤ b i := by nlinarith
  have hhi : b i ≤ 2 := by nlinarith
  by_contra h
  have hi2 : b i = 2 ∨ b i = -2 := by omega
  have hz (j : J) (hji : j ≠ i) (hjp : j ≠ p) : b j = 0 := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg
      (show (insert j {i,p} : Finset J) ⊆ Finset.univ from Finset.subset_univ _)
      (fun k _ _ => sq_nonneg (b k))
    rw [Finset.sum_insert (by simp [hji, hjp]), Finset.sum_pair hip, hs, hp] at hh
    rcases hi2 with hi2 | hi2 <;> rw [hi2] at hh <;> nlinarith [sq_nonneg (b j)]
  have hw : ∑ j, n j * b j = n i * b i + 1 := by
    rw [← Finset.sum_subset (Finset.subset_univ {i,p})]
    · simp [Finset.sum_pair hip, hp, hnp]
    · intro j _ hj
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
      rw [hz j hj.1 hj.2, mul_zero]
  rw [hw] at hd
  rcases hi2 with hi2 | hi2 <;> rw [hi2] at hd <;> omega

/-- The five nonzero entries are signs and can be enumerated principal first. -/
theorem exists_five_sign_rows {J : Type*} [Fintype J]
    (b n : J → ℤ) (p : J) (hp : b p = 1) (hnp : n p = 1)
    (hs : ∑ i, b i ^ 2 = 5) (hd : ∑ i, n i * b i = 0) :
    ∃ e : Fin 5 ↪ J, e 0 = p ∧
      (∀ j, b (e j) = 1 ∨ b (e j) = -1) ∧
      (∀ i, i ∉ Set.range e → b i = 0) := by
  classical
  have hb := signs b n p hp hnp hs hd
  let S := {i : J // b i ≠ 0}
  have hcard : Fintype.card S = 5 := by
    have he : (∑ i, b i ^ 2) = ∑ i : J, if b i ≠ 0 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases hb i with h | h | h <;> simp [h]
    rw [he] at hs
    have hh : (Fintype.card S : ℤ) = 5 := by
      simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.card_univ, S, Fintype.card_subtype] using hs
    exact_mod_cast hh
  let e₀ : Fin 5 ≃ S := (Fintype.equivFinOfCardEq hcard).symm
  let p' : S := ⟨p, by simp [hp]⟩
  let e₁ : Fin 5 ≃ S := (Equiv.swap 0 (e₀.symm p')).trans e₀
  let e : Fin 5 ↪ J := e₁.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨e, ?_, ?_, ?_⟩
  · change (e₀ (Equiv.swap 0 (e₀.symm p') 0)).val = p
    simp [p']
  · intro j
    exact (hb (e j)).resolve_left (e₁ j).property
  · intro i hi
    by_contra hbi
    apply hi
    exact ⟨e₁.symm ⟨i,hbi⟩, congrArg Subtype.val (e₁.apply_symm_apply _)⟩
end CyclicFiveColumnArithmetic
