module

public import Mathlib.LinearAlgebra.Charpoly.Basic
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# Primitive recurrences for binary automorphisms of order fifteen

An automorphism of a binary vector space with sixteen elements, of exact
order fifteen, satisfies either a⁴ = a + 1 or a⁴ = a³ + 1. The conclusion
is stated pointwise for the supplied linear equivalence, so later arguments
can apply it directly to invariant multilinear maps without choosing a basis.

The cardinality formula gives dimension four. Cayley–Hamilton then provides
the actual monic quartic characteristic polynomial as an annihilator.
Of the sixteen possible binary quartics, two give the stated recurrences.
For every other quartic q, the proof records a polynomial identity
r*q + s*(X^15+1) = X^k+1, with k equal to three or five. Evaluating that
identity at the automorphism would make its order divide k, a contradiction.
The explicit identities are checked by polynomial ring normalization in
characteristic two.

This is a direct finite-field linear-algebra consequence of the cardinality
formula and Cayley–Hamilton. It supplies the recurrence used to exclude
invariant trilinear forms under an order-fifteen action; no classification
of finite linear groups or hypothesis on such forms is used here.
-/

open Polynomial

namespace LinearEquiv

private noncomputable def binaryQuartic (c0 c1 c2 c3 : ZMod 2) : Polynomial (ZMod 2) :=
  X ^ 4 + C c3 * X ^ 3 + C c2 * X ^ 2 + C c1 * X + C c0

private theorem binary_value (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

private theorem binary_quartic_cases (c0 c1 c2 c3 : ZMod 2) :
    binaryQuartic c0 c1 c2 c3 = X ^ 4 + X + 1 ∨
    binaryQuartic c0 c1 c2 c3 = X ^ 4 + X ^ 3 + 1 ∨
    ∃ (k : ℕ), (k = 3 ∨ k = 5) ∧
      ∃ r s : Polynomial (ZMod 2),
        r * binaryQuartic c0 c1 c2 c3 + s * (X ^ 15 + 1) = X ^ k + 1 := by
  have htwo : (2 : Polynomial (ZMod 2)) = 0 := CharP.cast_eq_zero _ 2
  have hfour : (4 : Polynomial (ZMod 2)) = 0 := by
    calc
      (4 : Polynomial (ZMod 2)) = 2 + 2 := by norm_num
      _ = 0 := by rw [htwo]; simp
  rcases binary_value c0 with rfl | rfl <;>
    rcases binary_value c1 with rfl | rfl <;>
    rcases binary_value c2 with rfl | rfl <;>
    rcases binary_value c3 with rfl | rfl
  all_goals simp only [binaryQuartic, C_0, C_1, zero_mul, one_mul, add_zero]
  · refine Or.inr (Or.inr ⟨5, Or.inr rfl,
      X ^ 11 + X, 1, ?_⟩)
    ring_nf
    simp [htwo]
  · refine Or.inr (Or.inr ⟨3, Or.inl rfl,
      X ^ 14 + X ^ 13 + X ^ 12, X ^ 3 + 1, ?_⟩)
    ring_nf
    simp [htwo]
  · refine Or.inr (Or.inr ⟨3, Or.inl rfl,
      X ^ 11 + X ^ 9 + X ^ 7 + X ^ 5 + X ^ 3 + X, 1, ?_⟩)
    ring_nf
    simp [htwo]
  · refine Or.inr (Or.inr ⟨3, Or.inl rfl,
      X ^ 13 + X ^ 12 + X ^ 11 + X ^ 9 + X ^ 8 + X ^ 6 + X ^ 5 + X ^ 3 + X ^ 2 + 1, X ^ 2 + 1, ?_⟩)
    ring_nf
    simp [htwo, hfour]
  · refine Or.inr (Or.inr ⟨3, Or.inl rfl,
      X ^ 11 + X ^ 8 + X ^ 5 + X ^ 2, 1, ?_⟩)
    ring_nf
    simp [htwo]
  · refine Or.inr (Or.inr ⟨5, Or.inr rfl,
      X ^ 13 + X ^ 12 + X ^ 10 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 + X, X ^ 2 + 1, ?_⟩)
    ring_nf
    simp [htwo]
  · refine Or.inr (Or.inr ⟨5, Or.inr rfl,
      X ^ 14 + X ^ 12 + X ^ 10 + X ^ 9 + X ^ 8 + X ^ 5 + X ^ 3 + X ^ 2, X ^ 3 + 1, ?_⟩)
    ring_nf
    simp [htwo]
  · refine Or.inr (Or.inr ⟨5, Or.inr rfl,
      X ^ 13 + X ^ 10 + X ^ 9 + X ^ 6 + X ^ 5 + X ^ 2 + 1, X ^ 2 + X + 1, ?_⟩)
    ring_nf
    simp [htwo]
  · refine Or.inr (Or.inr ⟨5, Or.inr rfl,
      X ^ 14 + X ^ 13 + X ^ 11 + X ^ 10 + X ^ 9 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 3 + X ^ 2, X ^ 3 + X ^ 2 + 1, ?_⟩)
    ring_nf
    simp [htwo]
  · exact Or.inr (Or.inl trivial)
  · refine Or.inr (Or.inr ⟨3, Or.inl rfl,
      X ^ 13 + X ^ 12 + X ^ 11 + X ^ 10 + X ^ 7 + X ^ 6 + X ^ 5 + X ^ 4 + X + 1, X ^ 2 + X, ?_⟩)
    ring_nf
    simp [htwo]
  · refine Or.inr (Or.inr ⟨3, Or.inl rfl,
      X ^ 13 + X ^ 9 + X ^ 8 + X ^ 6 + X ^ 2 + X, X ^ 2 + X + 1, ?_⟩)
    ring_nf
    simp [htwo]
  · exact Or.inl trivial
  · refine Or.inr (Or.inr ⟨3, Or.inl rfl,
      X ^ 11 + X ^ 10 + X ^ 9 + X ^ 5 + X ^ 4 + X ^ 3, 1, ?_⟩)
    ring_nf
    simp [htwo]
  · refine Or.inr (Or.inr ⟨3, Or.inl rfl,
      X ^ 13 + X ^ 12 + X ^ 8 + X ^ 6 + X ^ 5 + X, X ^ 2 + X + 1, ?_⟩)
    ring_nf
    simp [htwo]
  · refine Or.inr (Or.inr ⟨5, Or.inr rfl,
      X + 1, 0, ?_⟩)
    ring_nf
    simp [htwo]

private theorem quartic_expansion
    (q : Polynomial (ZMod 2)) (hm : q.Monic) (hd : q.natDegree = 4) :
    q = binaryQuartic (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) := by
  have hcoeff : q.coeff 4 = 1 := by simpa only [hd] using hm.coeff_natDegree
  conv_lhs => rw [q.as_sum_range_C_mul_X_pow, hd]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    pow_zero, pow_one, mul_one, hcoeff, C_1, one_mul]
  dsimp [binaryQuartic]
  ring

private theorem toEnd_pow
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (a : V ≃ₗ[ZMod 2] V) (n : ℕ) :
    (a ^ n).toLinearMap = a.toLinearMap ^ n := by
  ext x
  exact (congrFun (LinearEquiv.coe_pow a n) x).trans
    (Module.End.pow_apply a.toLinearMap n x).symm

/-- An order-fifteen automorphism of a sixteen-element binary vector space
satisfies one of the two primitive quartic recurrences. -/
public theorem order_fifteen_recurrence
    {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (hV : Nat.card V = 16) (a : V ≃ₗ[ZMod 2] V) (ha : orderOf a = 15) :
    (∀ x : V, a (a (a (a x))) = a x + x) ∨
      (∀ x : V, a (a (a (a x))) = a (a (a x)) + x) := by
  classical
  let : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hdim : Module.finrank (ZMod 2) V = 4 := by
    apply Nat.pow_right_injective (by decide : 2 ≤ 2)
    have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := V)
    rw [hV, Nat.card_zmod] at h
    simpa only [Nat.reducePow] using h.symm
  let f : Module.End (ZMod 2) V := a.toLinearMap
  let q : Polynomial (ZMod 2) := f.charpoly
  have hq : q = binaryQuartic (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3) :=
    quartic_expansion q f.charpoly_monic (f.charpoly_natDegree.trans hdim)
  have hann : aeval f q = 0 := f.aeval_self_charpoly
  have hadd (x : V) : x + x = 0 := by
    simpa only [two_smul, zero_smul] using
      congrArg (fun r : ZMod 2 => r • x) (show (2 : ZMod 2) = 0 by decide)
  have hpow : f ^ 15 = 1 := by
    rw [← toEnd_pow a 15, ← ha, pow_orderOf_eq_one]
    rfl
  have horder : aeval f (X ^ 15 + 1 : Polynomial (ZMod 2)) = 0 := by
    simp only [map_add, map_pow, aeval_X, map_one, hpow]
    ext x
    exact hadd x
  rcases binary_quartic_cases (q.coeff 0) (q.coeff 1) (q.coeff 2) (q.coeff 3)
      with hone | hthree | ⟨k, hk, r, s, hbezout⟩
  · left
    have hroot : f ^ 4 + f + 1 = 0 := by
      rw [hq, hone] at hann
      simpa only [map_add, map_pow, aeval_X, map_one] using hann
    intro x
    have hx := congrArg (fun e : Module.End (ZMod 2) V => e x) hroot
    change a (a (a (a x))) + a x + x = 0 at hx
    have hxa : a (a (a (a x))) + (a x + x) = 0 := by
      simpa only [add_assoc] using hx
    apply add_right_cancel (b := a x + x)
    exact hxa.trans (hadd (a x + x)).symm
  · right
    have hroot : f ^ 4 + f ^ 3 + 1 = 0 := by
      rw [hq, hthree] at hann
      simpa only [map_add, map_pow, aeval_X, map_one] using hann
    intro x
    have hx := congrArg (fun e : Module.End (ZMod 2) V => e x) hroot
    change a (a (a (a x))) + a (a (a x)) + x = 0 at hx
    have hxa : a (a (a (a x))) + (a (a (a x)) + x) = 0 := by
      simpa only [add_assoc] using hx
    apply add_right_cancel (b := a (a (a x)) + x)
    exact hxa.trans (hadd (a (a (a x)) + x)).symm
  · have hroot : f ^ k + 1 = 0 := by
      rw [← hq] at hbezout
      have he := congrArg (aeval f) hbezout
      simpa only [map_add, map_mul, map_pow, aeval_X, map_one, hann,
        horder, mul_zero, zero_add] using he.symm
    have hfk : f ^ k = 1 := by
      ext x
      have hx := congrArg (fun e : Module.End (ZMod 2) V => e x) hroot
      change (f ^ k) x + x = 0 at hx
      exact add_right_cancel (hx.trans (hadd x).symm)
    have hak : a ^ k = 1 := by
      apply LinearEquiv.toLinearMap_injective
      rw [toEnd_pow]
      exact hfk
    have hdiv := orderOf_dvd_of_pow_eq_one hak
    rw [ha] at hdiv
    rcases hk with rfl | rfl <;> norm_num at hdiv

end LinearEquiv
