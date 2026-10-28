module

public import Theory.Representation.SL2.HighestWeightSpan
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Uniqueness of Highest-Weight Orbit Spans

For a finite field `K` mapping to a field `F`, the actual highest-weight
orbit spans of degrees `n, m < |K|` are equivalent only if `n = m`.
The two-embedding variant also compares diagonal weights and detects whether
the degree is zero; this supplies the Frobenius-twist input to descent.
The public fixed-line characterization identifies the upper-transvection
invariants with the scalar multiples of the actual pure-power generator.
No characteristic restriction, dimension formula, or character-classification
hypothesis is needed.

Upper-unipotent fixed vectors in a homogeneous space lie on its pure-power
line: highest-weight extraction applied to the span of a fixed vector proves
this directly. An intertwining equivalence therefore sends the pure generator
to a nonzero scalar multiple of the other one, so the diagonal weights agree.
The cyclic unit group separates positive degrees in the specified range.
Weight zero is distinguished because its generator is fixed by every matrix,
whereas a lower transvection moves every positive-degree pure power, as seen
by evaluation at `(0, 1)`.

This proves pairwise inequivalence of the concrete simple candidates for the
restricted-weight parameters in Fong--Wong, Nagoya Math. J. 36 (1969), p. 149,
formula (1.15). Exhaustivity and Frobenius descent are separate results.
-/

open MvPolynomial
open Matrix.SpecialLinearGroup
open scoped MatrixGroups

namespace Representation.SL2

variable {K F : Type*} [Field K] [Field F]

private theorem map_transvection (e : K →+* F) (i j : Fin 2) (hij : i ≠ j) (a : K) :
    Matrix.SpecialLinearGroup.map e (transvection hij a) = transvection hij (e a) := by
  ext l m
  simp [map_apply_coe, transvection_coe, Matrix.single_apply, Matrix.one_apply]
  split_ifs <;> simp

private theorem fixed_upper_eq_smul (e : K →+* F) (n : ℕ)
    (x : Fin (n+1) → K) (hx : Function.Injective x)
    (f : MvPolynomial (Fin 2) F) (hf : f.IsHomogeneous n)
    (hfix : ∀ t : K, polynomialAction F (Matrix.SpecialLinearGroup.map e
      (transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t)) f = f) :
    ∃ c : F, f = c • X 0 ^ n := by
  by_cases hf0 : f = 0
  · exact ⟨0, by simp [hf0]⟩
  have hgen : X 0 ^ n ∈ Submodule.span F {f} := by
    apply X_pow_mem_of_transvection_samples _ f hf hf0 (fun a => e (x a)) (e.injective.comp hx)
    intro a
    rw [← map_transvection e 0 1 zero_ne_one, hfix]
    exact Submodule.mem_span_singleton_self f
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hgen
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, zero_smul] at hc
    exact (pow_ne_zero n (X_ne_zero (0 : Fin 2))) hc.symm
  refine ⟨c⁻¹, ?_⟩
  rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]

private noncomputable def highestVector (e : K →+* F) (n : ℕ) :
    (highestWeightSpan e n).toSubmodule := ⟨X 0 ^ n, X_pow_mem_highestWeightSpan e n⟩

private theorem highestVector_ne_zero (e : K →+* F) (n : ℕ) : highestVector e n ≠ 0 := by
  intro h
  have hh := congrArg Subtype.val h
  exact (pow_ne_zero n (X_ne_zero (0 : Fin 2))) hh

private theorem upper_highestVector (e : K →+* F) (n : ℕ) (t : K) :
    (highestWeightSpan e n).toRepresentation
      (transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t) (highestVector e n) =
        highestVector e n := by
  apply Subtype.ext
  change polynomialAction F (Matrix.SpecialLinearGroup.map e
    (transvection zero_ne_one t)) (X 0 ^ n) = _
  simp [polynomialAction, transvection_coe, Matrix.one_apply, Matrix.single_apply,
    Fin.sum_univ_two, highestVector]

private theorem equiv_highestVector_scalar [Finite K] (e e' : K →+* F) (n m : ℕ)
    (hm : m < Nat.card K)
    (φ : ((highestWeightSpan e n).toRepresentation).Equiv
      (highestWeightSpan e' m).toRepresentation) :
    ∃ c : F, c ≠ 0 ∧ (φ (highestVector e n) : MvPolynomial (Fin 2) F) = c • X 0 ^ m := by
  classical
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨x⟩ := Function.Embedding.nonempty_of_card_le (α := Fin (m+1)) (β := K)
    (by simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using Nat.succ_le_of_lt hm)
  obtain ⟨c, hc⟩ := fixed_upper_eq_smul e' m x x.injective (φ (highestVector e n))
    (highestWeightSpan_le_homogeneous e' m (φ (highestVector e n)).property) (by
      intro t
      have h := Representation.IntertwiningMap.isIntertwining
        (highestWeightSpan e n).toRepresentation (highestWeightSpan e' m).toRepresentation φ.toIntertwiningMap
        (transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t) (highestVector e n)
      rw [upper_highestVector] at h
      exact congrArg Subtype.val h.symm)
  refine ⟨c, ?_, hc⟩
  intro hc0
  rw [hc0, zero_smul] at hc
  have hφ : φ (highestVector e n) = 0 := Subtype.ext hc
  exact highestVector_ne_zero e n (φ.toLinearEquiv.map_eq_zero_iff.mp hφ)

private theorem diagonal_X_pow (e : K →+* F) (n : ℕ) (a : K) (ha : a ≠ 0) :
    polynomialAction F (Matrix.SpecialLinearGroup.map e (diag2 a ha)) (X 0 ^ n) =
      (e a) ^ n • X 0 ^ n := by
  rw [map_pow]
  simp [polynomialAction, diag2_coe', Fin.sum_univ_two, smul_pow, ← map_pow, C_mul']

private theorem diagonal_highestVector (e : K →+* F) (n : ℕ) (a : K) (ha : a ≠ 0) :
    (highestWeightSpan e n).toRepresentation (diag2 a ha) (highestVector e n) =
      (e a) ^ n • highestVector e n := by
  apply Subtype.ext
  exact diagonal_X_pow e n a ha

private theorem equiv_diagonal_weights [Finite K] (e e' : K →+* F) (n m : ℕ)
    (hm : m < Nat.card K)
    (φ : ((highestWeightSpan e n).toRepresentation).Equiv
      (highestWeightSpan e' m).toRepresentation) (a : K) (ha : a ≠ 0) :
    (e a) ^ n = (e' a) ^ m := by
  obtain ⟨c, hc0, hc⟩ := equiv_highestVector_scalar e e' n m hm φ
  have h := Representation.IntertwiningMap.isIntertwining
    (highestWeightSpan e n).toRepresentation (highestWeightSpan e' m).toRepresentation
    φ.toIntertwiningMap (diag2 a ha) (highestVector e n)
  rw [diagonal_highestVector, map_smul] at h
  have hh := congrArg Subtype.val h
  change (e a) ^ n • (φ (highestVector e n) : MvPolynomial (Fin 2) F) =
    polynomialAction F (Matrix.SpecialLinearGroup.map e' (diag2 a ha))
      (φ (highestVector e n)) at hh
  rw [hc, map_smul, diagonal_X_pow, smul_smul, smul_smul] at hh
  have hs := smul_left_injective F (pow_ne_zero m (X_ne_zero (0 : Fin 2))) hh
  apply mul_right_cancel₀ hc0
  simpa only [mul_comm c] using hs

private theorem zero_of_equiv_zero [Finite K] (e e' : K →+* F) (m : ℕ)
    (hm : m < Nat.card K)
    (φ : ((highestWeightSpan e 0).toRepresentation).Equiv
      (highestWeightSpan e' m).toRepresentation) : m = 0 := by
  obtain ⟨c, hc0, hc⟩ := equiv_highestVector_scalar e e' 0 m hm φ
  let g : SL(2, K) := transvection (i := (1 : Fin 2)) (j := 0) one_ne_zero 1
  have hg : (highestWeightSpan e 0).toRepresentation g (highestVector e 0) = highestVector e 0 := by
    apply Subtype.ext
    exact map_one (polynomialAction F (Matrix.SpecialLinearGroup.map e g))
  have h := Representation.IntertwiningMap.isIntertwining
    (highestWeightSpan e 0).toRepresentation (highestWeightSpan e' m).toRepresentation
    φ.toIntertwiningMap g (highestVector e 0)
  rw [hg] at h
  have hh := congrArg Subtype.val h
  change (φ (highestVector e 0) : MvPolynomial (Fin 2) F) =
    polynomialAction F (Matrix.SpecialLinearGroup.map e' g) (φ (highestVector e 0)) at hh
  rw [hc, map_smul] at hh
  have hpure := smul_right_injective (MvPolynomial (Fin 2) F) hc0 hh
  have hev := congrArg (MvPolynomial.eval ![0, 1]) hpure
  by_contra hm0
  simp [polynomialAction, g, transvection_coe, Matrix.one_apply, Matrix.single_apply,
    Fin.sum_univ_two, hm0] at hev

public theorem highestWeightSpan_equiv_imp_eq [Finite K] (e : K →+* F) (n m : ℕ)
    (hn : n < Nat.card K) (hm : m < Nat.card K)
    (φ : ((highestWeightSpan e n).toRepresentation).Equiv
      (highestWeightSpan e m).toRepresentation) : n = m := by
  by_cases hn0 : n = 0
  · subst n
    exact (zero_of_equiv_zero e e m hm φ).symm
  by_cases hm0 : m = 0
  · subst m
    exact zero_of_equiv_zero e e n hn φ.symm
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := Kˣ)
  have ho : orderOf a = Nat.card K - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers ha, Nat.card_units]
  have heq : a ^ n = a ^ m := Units.ext (e.injective (by
    simpa only [Units.val_pow_eq_pow_val, map_pow] using equiv_diagonal_weights e e n m hm φ a a.ne_zero))
  have heq' : a ^ (n-1) = a ^ (m-1) := by
    apply mul_right_cancel (b := a)
    simpa only [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n),
      Nat.sub_add_cancel (by omega : 1 ≤ m)] using heq
  have hnm := pow_injOn_Iio_orderOf (x := a)
    (show n-1 < orderOf a by rw [ho]; omega) (show m-1 < orderOf a by rw [ho]; omega) heq'
  omega


public theorem highestWeightSpan_equiv_embedding_weights [Finite K]
    (e e' : K →+* F) (n m : ℕ) (hn : n < Nat.card K) (hm : m < Nat.card K)
    (φ : (highestWeightSpan e n).toRepresentation.Equiv
      (highestWeightSpan e' m).toRepresentation) :
    (∀ a : K, a ≠ 0 → (e a) ^ n = (e' a) ^ m) ∧ (n = 0 ↔ m = 0) := by
  refine ⟨equiv_diagonal_weights e e' n m hm φ, ?_⟩
  constructor
  · intro hn0
    subst n
    exact zero_of_equiv_zero e e' m hm φ
  · intro hm0
    subst m
    exact zero_of_equiv_zero e' e n hn φ.symm

public theorem highestWeightSpan_upper_fixed_iff [Finite K] (e : K →+* F) (n : ℕ)
    (hn : n < Nat.card K) (v : (highestWeightSpan e n).toSubmodule) :
    (∀ t : K, (highestWeightSpan e n).toRepresentation
      (transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one t) v = v) ↔
    ∃ c : F, v = c • (⟨X 0 ^ n, X_pow_mem_highestWeightSpan e n⟩ :
      (highestWeightSpan e n).toSubmodule) := by
  classical
  constructor
  · intro hfix
    let : Fintype K := Fintype.ofFinite K
    obtain ⟨x⟩ := Function.Embedding.nonempty_of_card_le (α := Fin (n+1)) (β := K)
      (by simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using Nat.succ_le_of_lt hn)
    obtain ⟨c, hc⟩ := fixed_upper_eq_smul e n x x.injective v
      (highestWeightSpan_le_homogeneous e n v.property) (fun t => congrArg Subtype.val (hfix t))
    exact ⟨c, Subtype.ext hc⟩
  · rintro ⟨c, rfl⟩ t
    rw [map_smul]
    congr 1
    exact upper_highestVector e n t

end Representation.SL2
