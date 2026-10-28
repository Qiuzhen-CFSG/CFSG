module

public import Theory.Representation.FrobeniusFixedDescent.Periodic
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Fixed bases for Frobenius-semilinear maps

An injective Frobenius-semilinear map over an algebraic closure of a prime
field admits a basis of fixed vectors. Periodicity reduces the spanning
assertion to orbit sums. A linear form vanishing on the fixed vectors gives
a polynomial of degree less than `p^n` vanishing at all `p^n` distinct roots
of `X^(p^n)-X`; its coefficient of `X` is therefore zero.

This elementary form of Lang's theorem for general linear groups needs no
assumed cocycle solution and no division by the period. It supplies the
prime-field realization described in Gorenstein, *Finite Groups*, §16.6,
p.482.
-/

public section

open Module Polynomial
namespace Representation.FrobeniusFixedDescent
variable {p : ℕ} [Fact p.Prime] {K V : Type*} [Field K]
  [CharP K p] [IsAlgClosed K] [AddCommGroup V] [Module K V]
  (T : V →+ V) (hsemi : ∀ (a : K) (v : V), T (a • v) = a ^ p • T v)

omit [Fact p.Prime] [CharP K p] [IsAlgClosed K] in
include hsemi in
/-- Iterating a Frobenius-semilinear map raises scalars to successive prime powers. -/
theorem iterate_smul (i : ℕ) (a : K) (v : V) :
    T^[i] (a • v) = a ^ (p ^ i) • T^[i] v := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih, hsemi, Function.iterate_succ_apply',
      ← pow_mul, pow_succ]

/-- A full orbit sum of a periodic vector is fixed. -/
theorem sum_iterates_fixed {n : ℕ} {w : V} (hw : T^[n] w = w) :
    T (∑ i ∈ Finset.range n, T^[i] w) = ∑ i ∈ Finset.range n, T^[i] w := by
  rw [map_sum]
  simp only [← Function.iterate_succ_apply']
  apply add_right_cancel (b := w)
  calc
    (∑ i ∈ Finset.range n, T^[i + 1] w) + w =
        ∑ i ∈ Finset.range (n + 1), T^[i] w := by
      rw [Finset.sum_range_succ']
      rfl
    _ = (∑ i ∈ Finset.range n, T^[i] w) + w := by
      rw [Finset.sum_range_succ, hw]

include hsemi in
/-- Periodic Frobenius-semilinear maps have spanning fixed vectors. -/
theorem span_fixed_eq_top_of_periodic
    (hperiodic : ∀ v : V, ∃ n > 0, T^[n] v = v) :
    Submodule.span K {v : V | T v = v} = ⊤ := by
  classical
  let W := Submodule.span K {v : V | T v = v}
  by_contra hn
  obtain ⟨φ, hφ, hW⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top
    (show W < ⊤ from lt_top_iff_ne_top.mpr hn) inferInstance
  apply hφ
  ext v
  obtain ⟨n, hn, hv⟩ := hperiodic v
  let Q : K[X] := ∑ i ∈ Finset.range n, monomial (p ^ i) (φ (T^[i] v))
  let P : K[X] := X ^ (p ^ n) - X
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_pow_sub_X_ne_zero K
    (Nat.ne_of_gt hn) (Fact.out : p.Prime).one_lt
  have hPc : P.roots.toFinset.card = p ^ n := by
    rw [Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots
      (galois_poly_separable p (p ^ n) (dvd_pow_self p (Nat.ne_of_gt hn)))),
      IsAlgClosed.card_roots_eq_natDegree]
    exact FiniteField.X_pow_card_pow_sub_X_natDegree_eq K
      (Nat.ne_of_gt hn) (Fact.out : p.Prime).one_lt
  have heval (a : K) (ha : a ∈ P.roots.toFinset) : Q.eval a = 0 := by
    have ha' : a ^ (p ^ n) = a := by
      have := (Polynomial.mem_roots hP0).mp (Multiset.mem_toFinset.mp ha)
      simpa only [P, Polynomial.IsRoot, eval_sub, eval_pow, eval_X, sub_eq_zero] using this
    have hw : T^[n] (a • v) = a • v := by
      rw [iterate_smul T hsemi, ha', hv]
    have hm : (∑ i ∈ Finset.range n, T^[i] (a • v)) ∈ W :=
      Submodule.subset_span (sum_iterates_fixed T hw)
    have hz : φ (∑ i ∈ Finset.range n, T^[i] (a • v)) = 0 := by
      have := Submodule.mem_map_of_mem hm (f := φ)
      rwa [hW, Submodule.mem_bot] at this
    simpa only [Q, eval_finsetSum, eval_monomial, map_sum,
      iterate_smul T hsemi, map_smul, smul_eq_mul, mul_comm] using hz
  have hdeg : Q.natDegree < p ^ n := by
    apply lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ ?_)
      (Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (show n - 1 < n by omega))
    intro i hi
    exact (Polynomial.natDegree_monomial_le _).trans
      (Nat.pow_le_pow_right (Nat.Prime.pos Fact.out) (by
        have := Finset.mem_range.mp hi
        omega))
  have hQ : Q = 0 := Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero Q
    (f := fun a : P.roots.toFinset => (a : K)) Subtype.val_injective
    (fun a => heval a a.property) (by simpa only [Fintype.card_coe, hPc] using hdeg)
  have hc := congrArg (fun q : K[X] => q.coeff 1) hQ
  have hp (i : ℕ) : p ^ i = 1 ↔ i = 0 := by
    constructor
    · intro h
      by_contra hi
      have := Nat.one_lt_pow hi (Fact.out : p.Prime).one_lt
      omega
    · rintro rfl
      rfl
  simpa only [Q, finsetSum_coeff, coeff_monomial, hp, Finset.sum_ite_eq',
    Finset.mem_range, hn, if_true, Function.iterate_zero_apply, coeff_zero,
    LinearMap.zero_apply] using hc

include hsemi in
/-- An injective Frobenius-semilinear map has a fixed basis, indexed like any
specified finite basis. The basis is constructed, not assumed. -/
theorem exists_fixed_basis [Algebra (ZMod p) K] [Algebra.IsAlgebraic (ZMod p) K]
    {ι : Type*} [Fintype ι] (b : Basis ι K V) (hT : Function.Injective T) :
    ∃ b' : Basis ι K V, ∀ i, T (b' i) = b' i := by
  classical
  let s : Set V := {v | T v = v}
  have hs : ⊤ ≤ Submodule.span K s := le_of_eq
    (span_fixed_eq_top_of_periodic T hsemi (periodic b T hT hsemi)).symm
  let b' := Basis.ofSpan hs
  have hb' : ∀ i, T (b' i) = b' i := by
    intro i
    exact Basis.extendLe_subset (linearIndependent_empty K V) (Set.empty_subset s) hs
      (Set.mem_range_self i)
  refine ⟨b'.reindex (b'.indexEquiv b), fun i => ?_⟩
  simpa only [Basis.reindex_apply] using hb' ((b'.indexEquiv b).symm i)

end Representation.FrobeniusFixedDescent
