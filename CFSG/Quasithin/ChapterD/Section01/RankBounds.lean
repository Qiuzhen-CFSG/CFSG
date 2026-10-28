module

public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith

/-!
# Rank inequalities in the multiple-chief-factor branch

This is the numerical part of Aschbacher–Smith, Proposition D.1.3,
printed pp. 174–175, equations (j)–(o). Write a = m(A/B), b = m(B/C_B(U)),
x = m(U/C_U(A)), and y = m(U/C_U(B)). Replacement gives x ≤ a+b;
the conjugate filtration gives qb ≤ y ≤ x; the c noncentral chief factors
give ca ≤ x. These inequalities imply q ≤ 2 when a > 0 and c ≥ 2.
At q = 2 every inequality is sharp. The group-theoretic construction of
these ranks and inequalities is deliberately separate from this calculation.
-/

namespace CFSG.Quasithin.ChapterD

/-- Equations (k)–(m): eliminate the rank of B/C_B(U). -/
public theorem qrc_rank_elimination {q a b x : ℝ}
    (hq : 0 ≤ q) (hx : x ≤ a + b) (hb : q * b ≤ x) :
    (q - 1) * x ≤ q * a := by
  nlinarith [mul_nonneg hq (sub_nonneg.mpr hx)]

/-- Equations (m)–(o): c ≥ 2 noncentral factors force q ≤ 2. -/
public theorem qrc_rank_bound {q a b x c : ℝ}
    (hq : 1 < q) (ha : 0 < a) (hc : 2 ≤ c)
    (hx : x ≤ a + b) (hb : q * b ≤ x) (hchief : c * a ≤ x) :
    q ≤ 2 := by
  have he := qrc_rank_elimination (by linarith : 0 ≤ q) hx hb
  have htwo : 2 * a ≤ x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (le_of_lt ha)]
  have hqa : (q - 2) * a ≤ 0 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ q - 1) (sub_nonneg.mpr htwo)]
  nlinarith

/-- At q = 2 the full rank chain in (j)–(o) is a chain of equalities. -/
public theorem qrc_rank_equality {a b x y c : ℝ}
    (ha : 0 < a) (hc : 2 ≤ c) (hx : x ≤ a + b)
    (hby : 2 * b ≤ y) (hyx : y ≤ x) (hchief : c * a ≤ x) :
    c = 2 ∧ a = b ∧ x = 2 * a ∧ y = x := by
  have htwo : 2 * a ≤ x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (le_of_lt ha)]
  have hab : a = b := by linarith
  have hxa : x = 2 * a := by linarith
  have hc' : c ≤ 2 := by nlinarith
  exact ⟨le_antisymm hc' hc, hab, hxa, by linarith⟩

/-- If all factor ranks are at least a and their sum is at most c·a,
each factor rank equals a. This is the equality step following (o). -/
public theorem qrc_factor_ranks_eq {ι : Type*} (s : Finset ι)
    (r : ι → ℝ) (a : ℝ) (hlower : ∀ i ∈ s, a ≤ r i)
    (hupper : ∑ i ∈ s, r i ≤ (s.card : ℝ) * a) :
    ∀ i ∈ s, r i = a := by
  have hsum : ∑ i ∈ s, r i = ∑ _i ∈ s, a := by
    apply le_antisymm
    · simpa using hupper
    · exact Finset.sum_le_sum hlower
  intro i hi
  exact ((Finset.sum_eq_sum_iff_of_le hlower).mp hsum.symm i hi).symm

end CFSG.Quasithin.ChapterD
