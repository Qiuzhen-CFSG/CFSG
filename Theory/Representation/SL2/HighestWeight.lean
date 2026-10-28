module

public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.Polynomial.BigOperators
public import Theory.Representation.SL2.BinaryForms
public import Theory.LinearAlgebra.PolynomialCoefficients

/-!
# Extracting Highest-Weight Binary Forms

A subspace containing the images of a degree-`k` homogeneous form under upper
transvections at `k + 1` distinct field parameters contains every coefficient
of its orbit polynomial. For a nonzero form, the highest parameter coefficient
is a nonzero scalar multiple of `X 0 ^ k`: homogeneity makes the monomial with
maximal `X 1` exponent unique. Thus the subspace contains that pure power.

The first coefficient for either transvection direction is `X i * pderiv j f`.
The two extraction results need no characteristic restriction; they use only
the specified distinct samples and subspace membership. They supply the
highest-weight and derivative steps in the restricted-degree irreducibility
of the actual binary-form representations used in Fong--Wong (1.15).
-/

open MvPolynomial

namespace Representation.SL2

variable {F : Type*} [Field F]

private noncomputable def orbitPolynomial (i j : Fin 2) :
    MvPolynomial (Fin 2) F →ₐ[F] Polynomial (MvPolynomial (Fin 2) F) :=
  MvPolynomial.aeval fun l =>
    Polynomial.C (X l) + if l = j then Polynomial.C (X i) * Polynomial.X else 0

private theorem orbitPolynomial_X (i j l : Fin 2) :
    orbitPolynomial (F := F) i j (X l) =
      Polynomial.C (X l) + if l = j then Polynomial.C (X i) * Polynomial.X else 0 := by
  simp [orbitPolynomial]

private theorem orbitPolynomial_coeff_zero (i j : Fin 2) (f : MvPolynomial (Fin 2) F) :
    (orbitPolynomial i j f).coeff 0 = f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [orbitPolynomial, Polynomial.algebraMap_apply]
  | add f g hf hg => simp [hf, hg]
  | mul_X f l hf =>
    rw [map_mul, orbitPolynomial_X, Polynomial.mul_coeff_zero, hf]
    split_ifs <;> simp

private theorem orbitPolynomial_coeff_one (i j : Fin 2) (f : MvPolynomial (Fin 2) F) :
    (orbitPolynomial i j f).coeff 1 = X i * pderiv j f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [orbitPolynomial, Polynomial.algebraMap_apply]
  | add f g hf hg => simp [hf, hg, mul_add]
  | mul_X f l hf =>
    rw [map_mul, orbitPolynomial_X]
    simp only [mul_add, Polynomial.coeff_add,
      Polynomial.coeff_mul_C]
    split_ifs with h
    · subst l
      rw [← mul_assoc, Polynomial.coeff_mul_X, Polynomial.coeff_mul_C]
      rw [hf, orbitPolynomial_coeff_zero]
      simp only [pderiv_mul, pderiv_X_self, mul_one]
      ring
    · simp only [hf, mul_zero, Polynomial.coeff_zero, add_zero, pderiv_mul,
        pderiv_X_of_ne h, mul_zero, add_zero]
      ring

private theorem orbitPolynomial_natDegree_X_le (i j l : Fin 2) :
    (orbitPolynomial (F := F) i j (X l)).natDegree ≤ 1 := by
  rw [orbitPolynomial_X]
  apply le_trans (Polynomial.natDegree_add_le _ _)
  split_ifs <;> simp

private theorem orbitPolynomial_natDegree_le (i j : Fin 2)
    (f : MvPolynomial (Fin 2) F) {k : ℕ} (hf : f.IsHomogeneous k) :
    (orbitPolynomial i j f).natDegree ≤ k := by
  classical
  rw [f.as_sum, map_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro d hd
  rw [MvPolynomial.monomial_eq, map_mul, map_finsuppProd]
  rw [show orbitPolynomial (F := F) i j (C (coeff d f)) =
    Polynomial.C (C (coeff d f)) by simp [orbitPolynomial, Polynomial.algebraMap_apply]]
  change (Polynomial.C (C (coeff d f)) *
    d.prod (fun l n => orbitPolynomial i j (X l ^ n))).natDegree ≤ k
  apply le_trans (Polynomial.natDegree_C_mul_le _ _)
  change (∏ l ∈ d.support, orbitPolynomial i j (X l ^ d l)).natDegree ≤ k
  apply le_trans (Polynomial.natDegree_prod_le _ _)
  calc
    ∑ l ∈ d.support, (orbitPolynomial i j (X l ^ d l)).natDegree ≤
        ∑ l ∈ d.support, d l := by
      apply Finset.sum_le_sum
      intro l _
      rw [map_pow]
      exact Polynomial.natDegree_pow_le.trans (by
        simpa using Nat.mul_le_mul_left (d l) (orbitPolynomial_natDegree_X_le i j l))
    _ = k := hf.degree_eq_sum_deg_support hd |>.symm

private theorem orbitPolynomial_eval (i j : Fin 2) (hij : i ≠ j)
    (t : F) (f : MvPolynomial (Fin 2) F) :
    (orbitPolynomial i j f).eval (C t) =
      polynomialAction F (Matrix.SpecialLinearGroup.transvection hij t) f := by
  induction f using MvPolynomial.induction_on with
  | C a => simp [orbitPolynomial, polynomialAction, Polynomial.algebraMap_apply]
  | add f g hf hg => simp [hf, hg]
  | mul_X f l hf =>
    rw [map_mul, Polynomial.eval_mul, hf, map_mul, orbitPolynomial_X]
    congr 1
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [polynomialAction, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.single_apply, Fin.sum_univ_two] <;> ring

private theorem orbitPolynomial_coeff_mem {k : ℕ} (W : Submodule F (MvPolynomial (Fin 2) F))
    (i j : Fin 2) (hij : i ≠ j) (f : MvPolynomial (Fin 2) F) (hf : f.IsHomogeneous k)
    (x : Fin (k + 1) → F) (hx : Function.Injective x)
    (hmem : ∀ a, polynomialAction F (Matrix.SpecialLinearGroup.transvection hij (x a)) f ∈ W)
    (r : Fin (k + 1)) : (orbitPolynomial i j f).coeff r ∈ W := by
  apply W.coeff_mem_of_sum_pow_smul_mem (fun r : Fin (k + 1) =>
    (orbitPolynomial i j f).coeff r) x hx _ r
  intro a
  have heval := hmem a
  rw [← orbitPolynomial_eval,
    Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le (orbitPolynomial_natDegree_le i j f hf)),
    ← Fin.sum_univ_eq_sum_range] at heval
  simpa only [← map_pow, mul_comm, MvPolynomial.C_mul'] using heval

private theorem orbitPolynomial_monomial (i j : Fin 2) (hij : i ≠ j)
    (d : Fin 2 →₀ ℕ) (a : F) :
    orbitPolynomial i j (monomial d a) =
      Polynomial.C (C a * X i ^ d i) *
        (Polynomial.C (X j) + Polynomial.C (X i) * Polynomial.X) ^ d j := by
  classical
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp only [Fin.prod_univ_two, map_mul, map_pow, orbitPolynomial_X]
  rw [show orbitPolynomial (F := F) i j (C a) = Polynomial.C (C a) by
    simp [orbitPolynomial, Polynomial.algebraMap_apply]]
  fin_cases i <;> fin_cases j <;> simp_all <;> ring

private theorem orbitPolynomial_monomial_natDegree_le (i j : Fin 2) (hij : i ≠ j)
    (d : Fin 2 →₀ ℕ) (a : F) :
    (orbitPolynomial i j (monomial d a)).natDegree ≤ d j := by
  rw [orbitPolynomial_monomial i j hij]
  apply le_trans (Polynomial.natDegree_C_mul_le _ _)
  apply Polynomial.natDegree_pow_le.trans
  have h : (Polynomial.C (X j) + Polynomial.C (X i) * Polynomial.X :
      Polynomial (MvPolynomial (Fin 2) F)).natDegree ≤ 1 := by
    apply le_trans (Polynomial.natDegree_add_le _ _)
    simp
  exact (Nat.mul_le_mul_left (d j) h).trans_eq (mul_one _)

private theorem orbitPolynomial_monomial_coeff_top (i j : Fin 2) (hij : i ≠ j)
    (d : Fin 2 →₀ ℕ) (a : F) :
    (orbitPolynomial i j (monomial d a)).coeff (d j) = C a * X i ^ (d i + d j) := by
  rw [orbitPolynomial_monomial i j hij, Polynomial.coeff_C_mul]
  have h : (Polynomial.C (X j) + Polynomial.C (X i) * Polynomial.X :
      Polynomial (MvPolynomial (Fin 2) F)).natDegree ≤ 1 := by
    apply le_trans (Polynomial.natDegree_add_le _ _)
    simp
  have hc := Polynomial.coeff_pow_of_natDegree_le (m := d j) h
  simp only [mul_one, Polynomial.coeff_add, Polynomial.coeff_C, one_ne_zero, ↓reduceIte,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_one, mul_one, zero_add] at hc
  rw [hc, pow_add, mul_assoc]

private theorem orbitPolynomial_coeff_max {k : ℕ} (f : MvPolynomial (Fin 2) F)
    (hf : f.IsHomogeneous k) (d : Fin 2 →₀ ℕ) (hd : d ∈ f.support)
    (hmax : ∀ e ∈ f.support, e 1 ≤ d 1) :
    (orbitPolynomial 0 1 f).coeff (d 1) = C (coeff d f) * X 0 ^ k := by
  classical
  conv_lhs => rw [f.as_sum, map_sum, Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single d]
  · rw [orbitPolynomial_monomial_coeff_top 0 1 zero_ne_one]
    have hdeg : d 0 + d 1 = k := by
      have h := hf.degree_eq_sum_deg_support hd
      change k = d.degree at h
      simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using h.symm
    rw [hdeg]
  · intro e he hne
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    apply (orbitPolynomial_monomial_natDegree_le 0 1 zero_ne_one e _).trans_lt
    refine lt_of_le_of_ne (hmax e he) ?_
    intro heq
    apply hne
    have hde := hf.degree_eq_sum_deg_support he
    have hdd := hf.degree_eq_sum_deg_support hd
    change k = e.degree at hde
    change k = d.degree at hdd
    simp only [Finsupp.degree_eq_sum, Fin.sum_univ_two] at hde hdd
    ext l
    fin_cases l
    · change e 0 = d 0
      omega
    · exact heq
  · exact fun hn => (hn hd).elim

public theorem X_pow_mem_of_transvection_samples {k : ℕ}
    (W : Submodule F (MvPolynomial (Fin 2) F))
    (f : MvPolynomial (Fin 2) F) (hf : f.IsHomogeneous k) (hf0 : f ≠ 0)
    (x : Fin (k + 1) → F) (hx : Function.Injective x)
    (hmem : ∀ a, polynomialAction F
      (Matrix.SpecialLinearGroup.transvection (i := (0 : Fin 2)) (j := 1) zero_ne_one (x a)) f ∈ W) :
    X 0 ^ k ∈ W := by
  classical
  obtain ⟨d, hd, hmax⟩ := f.support.exists_max_image (fun d => d 1)
    (MvPolynomial.support_nonempty.mpr hf0)
  have hdeg : d 0 + d 1 = k := by
    have h := hf.degree_eq_sum_deg_support hd
    change k = d.degree at h
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using h.symm
  have hcoeff := orbitPolynomial_coeff_mem W 0 1 zero_ne_one f hf x hx hmem
    ⟨d 1, by omega⟩
  rw [orbitPolynomial_coeff_max f hf d hd hmax] at hcoeff
  have hc : coeff d f ≠ 0 := MvPolynomial.mem_support_iff.mp hd
  have h := W.smul_mem (coeff d f)⁻¹ hcoeff
  simpa only [C_mul', smul_smul, inv_mul_cancel₀ hc, one_smul] using h

public theorem X_mul_pderiv_mem_of_transvection_samples {k : ℕ}
    (W : Submodule F (MvPolynomial (Fin 2) F))
    (i j : Fin 2) (hij : i ≠ j) (f : MvPolynomial (Fin 2) F) (hf : f.IsHomogeneous k)
    (x : Fin (k + 1) → F) (hx : Function.Injective x)
    (hmem : ∀ a, polynomialAction F (Matrix.SpecialLinearGroup.transvection hij (x a)) f ∈ W) :
    X i * pderiv j f ∈ W := by
  by_cases hk : k = 0
  · rw [← orbitPolynomial_coeff_one]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by
      have h := orbitPolynomial_natDegree_le i j f hf
      omega)]
    exact W.zero_mem
  · have h := orbitPolynomial_coeff_mem W i j hij f hf x hx hmem ⟨1, by omega⟩
    simpa only [orbitPolynomial_coeff_one] using h

end Representation.SL2

