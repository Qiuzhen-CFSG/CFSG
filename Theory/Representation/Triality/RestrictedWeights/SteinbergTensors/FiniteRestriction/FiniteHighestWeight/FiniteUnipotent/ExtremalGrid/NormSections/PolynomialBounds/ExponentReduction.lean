module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.PolynomialSums
public import Mathlib.Tactic.Linarith

/-!
# Reducing polynomial exponents on products of finite fields

A positive exponent m is replaced by 1+(m-1) mod (N-1), while exponent zero
stays zero. This preserves evaluation on an N-element field, including at
zero. Every reduced exponent is at most N-1. Its equality with N-1 is
exactly positive divisibility of the original exponent by N-1.

The lemmas are used after literal triality substitution. Reduction, unlike an
unproved ordinary degree estimate, really gives the mixed-grid support bound.
Source context: Steinberg, `Chapter2St2.tex`, 13.3(a); finite-field power laws.
-/

@[expose] public noncomputable section
open scoped Classical BigOperators
open MvPolynomial
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.PolynomialBounds

def reducePower (N m : ℕ) : ℕ := if m = 0 then 0 else (m-1) % (N-1) + 1

lemma reducePower_le (N m : ℕ) (hN : 1 < N) : reducePower N m ≤ N-1 := by
  by_cases hm : m=0
  · simp [reducePower, hm]
  · simp only [reducePower, if_neg hm]
    have := Nat.mod_lt (m-1) (by omega : 0 < N-1)
    omega

set_option backward.isDefEq.respectTransparency false in
lemma reducePower_eq_top_iff (N m : ℕ) (hN : 1 < N) :
    reducePower N m = N-1 ↔ ∃ r : ℕ, 0 < r ∧ m = (N-1)*r := by
  by_cases hm : m=0
  · simp only [hm, reducePower, ite_true]
    constructor
    · omega
    · rintro ⟨r, hr, h⟩
      have := Nat.mul_pos (by omega : 0 < N-1) hr
      omega
  · have hm1 : m-1+1=m := by omega
    have hN1 : 0 < N-1 := by omega
    simp only [reducePower, if_neg hm]
    constructor
    · intro h
      refine ⟨(m-1)/(N-1)+1, Nat.succ_pos _, ?_⟩
      have := Nat.mod_add_div (m-1) (N-1)
      nlinarith
    · rintro ⟨r, hr, h⟩
      have hr1 : r-1+1=r := by omega
      have hN2 : N-2+1=N-1 := by omega
      have hm' : m-1 = (N-1)*(r-1)+(N-2) := by nlinarith
      rw [hm', Nat.add_mod]
      simp only [Nat.mul_mod_right, zero_add, Nat.mod_mod]
      rw [Nat.mod_eq_of_lt (by omega : N-2 < N-1)]
      omega

lemma pow_reducePower {F : Type*} [Field F] [Fintype F] (x : F) (m : ℕ) :
    x ^ reducePower (Fintype.card F) m = x^m := by
  by_cases hm : m=0
  · simp [reducePower, hm]
  have hr : 0 < reducePower (Fintype.card F) m := by simp [reducePower, hm]
  by_cases hx : x=0
  · simp [hx, zero_pow (by omega : m ≠ 0), zero_pow hr.ne']
  have hp := FiniteField.pow_card_sub_one_eq_one x hx
  have he : x ^ ((m-1) % (Fintype.card F-1)) = x ^ (m-1) := by
    conv_rhs => rw [← Nat.mod_add_div (m-1) (Fintype.card F-1)]
    rw [pow_add, pow_mul, hp, one_pow, mul_one]
  simp only [reducePower, if_neg hm, pow_add, pow_one, he]
  rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ m)]

variable {σ : Type*} [Fintype σ]
variable (F : σ → Type*) [∀ i, Field (F i)] [∀ i, Fintype (F i)]

def reduceExponent (e : σ →₀ ℕ) : σ →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i => reducePower (Fintype.card (F i)) (e i))

lemma reduceExponent_eq_top_iff (e : σ →₀ ℕ) :
    reduceExponent F e = PolynomialSums.topExponent F ↔
      ∀ i, ∃ r : ℕ, 0 < r ∧ e i = (Fintype.card (F i)-1)*r := by
  rw [Finsupp.ext_iff]
  exact forall_congr' (fun i => reducePower_eq_top_iff _ _ Fintype.one_lt_card)

lemma reduceExponent_top :
    reduceExponent F (PolynomialSums.topExponent F) = PolynomialSums.topExponent F := by
  apply (reduceExponent_eq_top_iff F _).mpr
  intro i
  exact ⟨1, by omega, by simp⟩

variable {k : Type*} [Field k]

lemma eval_monomial_reduceExponent (ι : ∀ i, F i →+* k) (e : σ →₀ ℕ)
    (c : k) (x : ∀ i, F i) :
    eval (fun i => ι i (x i)) (monomial (reduceExponent F e) c) =
      eval (fun i => ι i (x i)) (monomial e c) := by
  simp only [eval_monomial]
  congr 1
  simp only [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  apply Finset.prod_congr rfl
  intro i hi
  change (ι i (x i)) ^ reducePower (Fintype.card (F i)) (e i) = (ι i (x i)) ^ e i
  simp only [← map_pow, pow_reducePower]

lemma reduceExponent_ne_top (e : σ →₀ ℕ)
    (hne : reduceExponent F e ≠ PolynomialSums.topExponent F) :
    ∃ i, reduceExponent F e i < Fintype.card (F i)-1 := by
  by_contra! h
  apply hne
  ext i
  exact le_antisymm (reducePower_le _ _ Fintype.one_lt_card) (h i)

lemma reduced_sum_support {α : Type*} (s : Finset α) (d : α → σ →₀ ℕ) (c : α → k) :
    ∀ e ∈ (∑ a ∈ s, monomial (reduceExponent F (d a)) (c a)).support,
      e ≠ PolynomialSums.topExponent F → ∃ i, e i < Fintype.card (F i)-1 := by
  intro e he hne
  obtain ⟨a, ha, hae⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  have hae' : e = reduceExponent F (d a) := by
    by_cases hc : c a = 0
    · simp [hc] at hae
    · simpa only [support_monomial, if_neg hc, Finset.mem_singleton] using hae
  subst e
  exact reduceExponent_ne_top F (d a) hne

end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.PolynomialBounds
