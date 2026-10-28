module

public import Theory.Representation.SL2.BinaryHermitianRecognition.Setup
public import Theory.Representation.SL2.HighestWeightSpan
public import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Polynomial realization of the repeated Frobenius pair

The matrix unit `Eₐᵦ` is sent to `Xₐ^(2^j) * Xᵦ^(2^(j+s))`. Substitution
intertwines this map with the concrete matrix action `A^(2^j) M (A^(2^(j+s)))ᵀ`.
For positive `s`, the four monomials have distinct exponent vectors, so the map
is injective.

Matrices with first column `(t, 1)` give orbit vectors whose four coefficient
vectors are precisely these monomials. Vandermonde interpolation recovers them
when the weight is less than the field cardinality. Conversely, the image is
invariant and contains the highest-weight vector, proving equality with its
orbit span. The bound follows from `j < s` and `|K| = 2^(2*s)`, including
`s = 1, j = 0`.

This is the two-factor comparison used in the repeated-pair case of
GLS volume 3, §§2.8.6, 2.8.8, 2.8.10(b), and Aschbacher--Smith, combined
manuscript (1 March 2004), G.9.3(7), printed pp.354,356–357. Scalar descent
to the Hermitian module is a separate comparison.
-/

open MvPolynomial
open scoped MatrixGroups
open Representation.OrthogonalFourMinus
namespace Representation.SL2.BinaryHermitian
noncomputable section
variable {K L : Type*} [Field K] [Field L]

private def pairMonomial (a b : ℕ) (i : Fin 2 × Fin 2) : MvPolynomial (Fin 2) L :=
  X i.1 ^ a * X i.2 ^ b

private def pairPolynomial (a b : ℕ) : Mat L →ₗ[L] MvPolynomial (Fin 2) L where
  toFun M := ∑ i : Fin 2 × Fin 2, M i.1 i.2 • pairMonomial a b i
  map_add' M N := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c M := by simp [mul_smul, Finset.smul_sum]

private theorem pairMonomial_independent {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    LinearIndependent L (pairMonomial (L := L) a b) := by
  let d : Fin 2 × Fin 2 → Fin 2 →₀ ℕ := fun i =>
    Finsupp.single i.1 a + Finsupp.single i.2 b
  have hd : Function.Injective d := by
    rintro ⟨i, j⟩ ⟨k, l⟩ h
    have h0 := congrArg (fun v : Fin 2 →₀ ℕ => v 0) h
    clear h
    fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
      simp [d] at h0 ⊢ <;> omega
  have h := (basisMonomials (Fin 2) L).linearIndependent.comp d hd
  have heq : pairMonomial (L := L) a b = (basisMonomials (Fin 2) L) ∘ d := by
    funext i
    simp [pairMonomial, d, coe_basisMonomials, X_pow_eq_monomial, monomial_mul]
  rw [heq]
  exact h

private theorem pairPolynomial_injective {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Function.Injective (pairPolynomial (L := L) a b) := by
  intro M N h
  have h' : ∑ i : Fin 2 × Fin 2, M i.1 i.2 • pairMonomial a b i =
      ∑ i : Fin 2 × Fin 2, N i.1 i.2 • pairMonomial a b i := h
  ext i j
  exact (pairMonomial_independent ha hab).eq_coords_of_eq h' (i, j)

private theorem pairPolynomial_intertwines [CharP L 2] [PerfectRing L 2]
    (e : K →+* L) (s j : ℕ) (g : SL(2, K)) (M : Mat L) :
    pairPolynomial (2 ^ j) (2 ^ (j + s)) (pair e s j g M) =
      polynomialAction L (Matrix.SpecialLinearGroup.map e g)
        (pairPolynomial (2 ^ j) (2 ^ (j + s)) M) := by
  rw [pair_apply]
  simp [pairPolynomial, pairMonomial, polynomialAction, Fintype.sum_prod_type,
    Fin.sum_univ_two, Matrix.mul_apply, add_pow_char_pow, mul_pow, Algebra.smul_def]
  ring

private theorem sparse_coeff_mem {V I : Type*} [AddCommGroup V] [Module L V]
    [Fintype I] {n : ℕ} (W : Submodule L V) (c : I → V) (d : I → Fin n)
    (hd : Function.Injective d) (x : Fin n → L) (hx : Function.Injective x)
    (heval : ∀ t, ∑ i, x t ^ (d i).val • c i ∈ W) (i : I) : c i ∈ W := by
  classical
  let c' : Fin n → V := fun r => ∑ i, if r = d i then c i else 0
  have hs (t : Fin n) : ∑ r, x t ^ r.val • c' r = ∑ i, x t ^ (d i).val • c i := by
    simp only [c', Finset.smul_sum]
    rw [Finset.sum_comm]
    congr 1
    funext i
    simp [smul_ite]
  have h := W.coeff_mem_of_sum_pow_smul_mem c' x hx
    (fun t => (hs t).symm ▸ heval t) (d i)
  simpa [c', hd.eq_iff] using h

private def pairDegree (a b : ℕ) (i : Fin 2 × Fin 2) : Fin (a + b + 1) :=
  ⟨(if i.1 = 0 then a else 0) + (if i.2 = 0 then b else 0), by
    split_ifs <;> omega⟩

private theorem pairDegree_injective {a b : ℕ} (ha : 0 < a) (hab : a < b) :
    Function.Injective (pairDegree a b) := by
  rintro ⟨i, j⟩ ⟨k, l⟩ h
  have h0 := congrArg Fin.val h
  clear h
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [pairDegree] at h0 ⊢ <;> omega

private def pairSample (t : K) : SL(2, K) :=
  ⟨!![t, -1; 1, 0], by simp [Matrix.det_fin_two]⟩

private theorem pairSample_expansion [CharP L 2] (e : K →+* L) (j k : ℕ) (t : K) :
    polynomialAction L (Matrix.SpecialLinearGroup.map e (pairSample t))
        (X 0 ^ (2 ^ j + 2 ^ k)) =
      ∑ i : Fin 2 × Fin 2, e t ^ (pairDegree (2 ^ j) (2 ^ k) i).val •
        pairMonomial (2 ^ j) (2 ^ k) i := by
  simp only [map_pow]
  have hp : polynomialAction L (Matrix.SpecialLinearGroup.map e (pairSample t)) (X 0) =
      C (e t) * X 0 + X 1 := by
    simp only [polynomialAction, aeval_X, Fin.sum_univ_two]
    change C (e t) * X 0 + C (e 1) * X 1 = _
    simp
  rw [hp, pow_add, add_pow_char_pow, add_pow_char_pow]
  simp [pairDegree, pairMonomial, Fintype.sum_prod_type,
    Fin.sum_univ_two, mul_pow, Algebra.smul_def, pow_add]
  ring

private theorem pairMonomial_mem [CharP L 2] [Finite K] (e : K →+* L)
    (j k : ℕ) (hjk : j < k) (hn : 2 ^ j + 2 ^ k < Nat.card K) (i : Fin 2 × Fin 2) :
    pairMonomial (L := L) (2 ^ j) (2 ^ k) i ∈ highestWeightSpan e (2 ^ j + 2 ^ k) := by
  classical
  let := Fintype.ofFinite K
  obtain ⟨x⟩ := Function.Embedding.nonempty_of_card_le
    (α := Fin (2 ^ j + 2 ^ k + 1)) (β := K)
    (by simpa only [Fintype.card_fin, Nat.card_eq_fintype_card] using Nat.succ_le_of_lt hn)
  apply sparse_coeff_mem (highestWeightSpan e (2 ^ j + 2 ^ k)).toSubmodule
    (pairMonomial (2 ^ j) (2 ^ k)) (pairDegree (2 ^ j) (2 ^ k))
    (pairDegree_injective (by positivity) (Nat.pow_lt_pow_right (by decide) hjk))
    (fun t => e (x t)) (e.injective.comp x.injective) _ i
  intro t
  rw [← pairSample_expansion]
  exact Submodule.subset_span ⟨pairSample (x t), rfl⟩

private def pairPolynomialIntertwiner [CharP L 2] [PerfectRing L 2]
    (e : K →+* L) (s j : ℕ) :
    IntertwiningMap (pair e s j)
      ((polynomialRepresentation L).comp (Matrix.SpecialLinearGroup.map e)) where
  toLinearMap := pairPolynomial (2 ^ j) (2 ^ (j + s))
  isIntertwining' g := by
    apply LinearMap.ext
    intro M
    exact pairPolynomial_intertwines e s j g M

private theorem pairPolynomial_range [CharP L 2] [PerfectRing L 2] [Finite K]
    (e : K →+* L) (s j : ℕ) (hs : 0 < s)
    (hn : 2 ^ j + 2 ^ (j + s) < Nat.card K) :
    (pairPolynomialIntertwiner e s j).range = highestWeightSpan e (2 ^ j + 2 ^ (j + s)) := by
  apply le_antisymm
  · rintro P ⟨M, rfl⟩
    change (∑ i : Fin 2 × Fin 2, M i.1 i.2 • pairMonomial (2 ^ j) (2 ^ (j + s)) i) ∈
      (highestWeightSpan e (2 ^ j + 2 ^ (j + s))).toSubmodule
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
      (pairMonomial_mem e j (j + s) (by omega) hn i)
  · apply (highestWeightSpan_le_iff _ _ _).mpr
    refine ⟨!![1, 0; 0, 0], ?_⟩
    change pairPolynomial (2 ^ j) (2 ^ (j + s)) !![1, 0; 0, 0] = _
    simp [pairPolynomial, pairMonomial, Fintype.sum_prod_type, Fin.sum_univ_two, pow_add]

private theorem pairWeight_lt (s j : ℕ) (hj : j < s) :
    2 ^ j + 2 ^ (j + s) < 2 ^ (2 * s) := by
  have hab : 2 ^ j < 2 ^ (j + s) := Nat.pow_lt_pow_right (by decide) (by omega)
  calc
    2 ^ j + 2 ^ (j + s) < 2 ^ (j + s) * 2 := by omega
    _ = 2 ^ (j + s + 1) := (pow_succ _ _).symm
    _ ≤ 2 ^ (2 * s) := Nat.pow_le_pow_right (by decide) (by omega)

/-- The concrete two-factor Frobenius matrix representation is the highest-weight
orbit span, via the map sending `Eₐᵦ` to `Xₐ^(2^j) * Xᵦ^(2^(j+s))`. -/
public theorem pair_equiv_highestWeightSpan [Finite K] [CharP L 2] [PerfectRing L 2]
    (e : K →+* L) (s j : ℕ) [NeZero s] (hK : Nat.card K = 2 ^ (2 * s)) (hj : j < s) :
    Nonempty ((pair e s j).Equiv
      (highestWeightSpan e (2 ^ j * (1 + 2 ^ s))).toRepresentation) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hn : 2 ^ j + 2 ^ (j + s) < Nat.card K := by
    rw [hK]
    exact pairWeight_lt s j hj
  have hw : 2 ^ j * (1 + 2 ^ s) = 2 ^ j + 2 ^ (j + s) := by
    rw [pow_add]
    ring
  rw [hw]
  let H := highestWeightSpan e (2 ^ j + 2 ^ (j + s))
  have hr := pairPolynomial_range e s j hs hn
  let f : Mat L →ₗ[L] H.toSubmodule :=
    (pairPolynomial (2 ^ j) (2 ^ (j + s))).codRestrict H.toSubmodule (by
      intro M
      change pairPolynomial (2 ^ j) (2 ^ (j + s)) M ∈ highestWeightSpan e (2 ^ j + 2 ^ (j + s))
      rw [← hr]
      exact ⟨M, rfl⟩)
  have hf : Function.Bijective f := by
    constructor
    · intro M N h
      exact pairPolynomial_injective (a := 2 ^ j) (b := 2 ^ (j + s)) (by positivity)
        (Nat.pow_lt_pow_right (by decide) (by omega : j < j + s)) (congrArg Subtype.val h)
    · intro v
      have hv : v.val ∈ (pairPolynomialIntertwiner e s j).range := by
        rw [hr]
        exact v.property
      obtain ⟨M, hM⟩ := hv
      exact ⟨M, Subtype.ext hM⟩
  refine ⟨Representation.Equiv.mk (LinearEquiv.ofBijective f hf) ?_⟩
  intro g
  apply LinearMap.ext
  intro M
  apply Subtype.ext
  exact pairPolynomial_intertwines e s j g M

end
end Representation.SL2.BinaryHermitian
