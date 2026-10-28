module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Int.Order.Basic
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Tactic

/-!
# Integer arithmetic for the order-thirteen character columns

Four exceptional rows have the form `c + ε ηᵢ`, where the local periods
have sum minus one and squared norms summing to ten. All other rows have
integer values `bᵢ`. Column orthogonality gives
`Σ bᵢ² + 4c² - 2εc = 3`. The principal row bounds this sum from below,
leaving only `c = 0` or `c = ε`. In the latter case only the principal
row remains, contradicting degree orthogonality and the positive common
exceptional degree. Thus the shift is zero, and precisely three remaining
values are signs. The enumeration puts the principal row first.

These are purely integer consequences; the character-theoretic inputs are
discharged by the ordinary cyclic-thirteen row construction.
Source: the exceptional-character argument underlying
Alperin--Brauer--Gorenstein, III.8, printed pp.116--117.
-/

public section
open scoped BigOperators
namespace CyclicThirteenColumnArithmetic

private theorem shift_alternatives {c ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (h : 4 * c ^ 2 - 2 * ε * c ≤ 2) : c = 0 ∨ c = ε := by
  rcases hε with rfl | rfl
  · have hlo : 0 ≤ c := by nlinarith
    have hhi : c ≤ 1 := by nlinarith
    omega
  · have hlo : -1 ≤ c := by nlinarith
    have hhi : c ≤ 0 := by nlinarith
    omega

private theorem weighted_sum_of_square_sum_one
    {J : Type*} [Fintype J] [DecidableEq J]
    (b n : J → ℤ) (p : J) (hp : b p = 1)
    (h : ∑ i, b i ^ 2 = 1) : ∑ i, n i * b i = n p := by
  have hz (i : J) (hi : i ≠ p) : b i = 0 := by
    have hh := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({i,p} : Finset J) ⊆ Finset.univ from Finset.subset_univ _)
      (fun j _ _ => sq_nonneg (b j))
    simp only [Finset.sum_pair hi, hp, one_pow, h] at hh
    nlinarith [sq_nonneg (b i)]
  rw [Finset.sum_eq_single p]
  · rw [hp, mul_one]
  · intro i _ hi
    rw [hz i hi, mul_zero]
  · simp

/-- Column norms and degree orthogonality eliminate the common integer shift
of the four exceptional values. -/
theorem shift_eq_zero {J : Type*} [Fintype J]
    (b n : J → ℤ) (p : J) (hp : b p = 1) (hnp : n p = 1)
    (c ε D : ℤ) (hε : ε = 1 ∨ ε = -1) (hD : 0 < D)
    (hcolumn : (∑ i, b i ^ 2) + 4 * c ^ 2 - 2 * ε * c = 3)
    (hdegree : (∑ i, n i * b i) + (4 * c - ε) * D = 0) :
    c = 0 ∧ ∑ i, b i ^ 2 = 3 := by
  classical
  have hbound : 1 ≤ ∑ i, b i ^ 2 := by
    have h := Finset.single_le_sum (fun i _ => sq_nonneg (b i))
      (Finset.mem_univ p)
    simpa only [hp, one_pow] using h
  have hc : c = 0 := by
    rcases shift_alternatives (c := c) hε (by linarith) with hc | hc
    · exact hc
    · have hs : ∑ i, b i ^ 2 = 1 := by
        rcases hε with rfl | rfl <;> subst c <;> nlinarith [hcolumn]
      have hw := weighted_sum_of_square_sum_one b n p hp hs
      rw [hw, hnp, hc] at hdegree
      rcases hε with rfl | rfl <;> nlinarith
  exact ⟨hc, by simpa [hc] using hcolumn⟩

/-- An integer column of squared norm three has exactly three nonzero entries,
each a sign. A specified entry of value one can be placed first. -/
theorem exists_three_sign_rows {J : Type*} [Fintype J]
    (b : J → ℤ) (p : J) (hp : b p = 1) (hs : ∑ i, b i ^ 2 = 3) :
    ∃ e : Fin 3 ↪ J, e 0 = p ∧
      (∀ j, b (e j) = 1 ∨ b (e j) = -1) ∧
      (∀ i, i ∉ Set.range e → b i = 0) := by
  classical
  have hb (i : J) : b i = 0 ∨ b i = 1 ∨ b i = -1 := by
    have hh := Finset.single_le_sum (fun j _ => sq_nonneg (b j))
      (Finset.mem_univ i)
    rw [hs] at hh
    have hlo : -1 ≤ b i := by nlinarith
    have hhi : b i ≤ 1 := by nlinarith
    omega
  let S := {i : J // b i ≠ 0}
  have hcard : Fintype.card S = 3 := by
    have he : (∑ i, b i ^ 2) = ∑ i : J, if b i ≠ 0 then (1 : ℤ) else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      rcases hb i with h | h | h <;> simp [h]
    rw [he] at hs
    have hh : (Fintype.card S : ℤ) = 3 := by
      simpa only [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
        Finset.card_univ, S, Fintype.card_subtype] using hs
    exact_mod_cast hh
  let e₀ : Fin 3 ≃ S := (Fintype.equivFinOfCardEq hcard).symm
  let p' : S := ⟨p, by simp [hp]⟩
  let e₁ : Fin 3 ≃ S := (Equiv.swap 0 (e₀.symm p')).trans e₀
  let e : Fin 3 ↪ J := e₁.toEmbedding.trans (Function.Embedding.subtype _)
  refine ⟨e, ?_, ?_, ?_⟩
  · change (e₀ (Equiv.swap 0 (e₀.symm p') 0)).val = p
    simp [p']
  · intro j
    exact (hb (e j)).resolve_left (e₁ j).property
  · intro i hi
    by_contra hbi
    apply hi
    exact ⟨e₁.symm ⟨i,hbi⟩, congrArg Subtype.val (e₁.apply_symm_apply _)⟩

end CyclicThirteenColumnArithmetic
