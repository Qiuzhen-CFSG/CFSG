module

public import Theory.Representation.SL2.HighestWeight
public import Theory.Representation.SubrepresentationLattice
public import Mathlib.Algebra.CharP.Basic

/-!
# Restricted Binary Forms Are Irreducible

Let `K` map to a field `F` of positive characteristic `p`. The action of
`SL2(K)` on degree-`k` binary forms over `F` is irreducible when `k < p`.
Neither field need be finite, and the result includes `k = 0` and `p = 2`.

The prime-field parameters `0, ..., k` are distinct in `F`. In any nonzero
invariant subspace, the sampled upper-transvection orbit of a nonzero form
therefore yields the pure power `X 0 ^ k`, by the highest-weight extraction
lemma. Sampled lower transvections yield the operator `X 1 * pderiv 0`.
Repeated application generates all degree-`k` monomials: the scalar factors
are nonzero because their positive exponents are less than `p`.

This proves the restricted-weight irreducibility prerequisite for the binary
forms in Fong--Wong, Nagoya Math. J. 36 (1969), p. 149, formula (1.15).
The scalar-extension formulation provides absolute irreducibility without
assuming the later tensor-product classification or Frobenius descent.
-/

open MvPolynomial

namespace Representation.SL2

variable {F : Type*} [Field F]

private theorem monomial_mem_of_pure_power {p k : ℕ} [CharP F p] (hkp : k < p)
    (W : Submodule F (MvPolynomial (Fin 2) F)) (hbase : X 0 ^ k ∈ W)
    (hderiv : ∀ f ∈ W, f.IsHomogeneous k → X 1 * pderiv 0 f ∈ W)
    (r : ℕ) (hr : r ≤ k) : X 0 ^ (k - r) * X 1 ^ r ∈ W := by
  induction r with
  | zero => simpa using hbase
  | succ r ih =>
    have hrk : r ≤ k := by omega
    have hhom : (X 0 ^ (k-r) * X 1 ^ r : MvPolynomial (Fin 2) F).IsHomogeneous k := by
      convert ((isHomogeneous_X F (0 : Fin 2)).pow (k-r)).mul
        ((isHomogeneous_X F (1 : Fin 2)).pow r) using 1
      omega
    have h := hderiv _ (ih hrk) hhom
    have hd : X 1 * pderiv 0 (X 0 ^ (k-r) * X 1 ^ r : MvPolynomial (Fin 2) F) =
        ((k-r : ℕ) : F) • (X 0 ^ (k-(r+1)) * X 1 ^ (r+1)) := by
      simp only [pderiv_mul, pderiv_pow, pderiv_X_self,
        pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide), mul_zero, add_zero, mul_one]
      rw [show k-r-1 = k-(r+1) by omega]
      simp only [pow_succ, Algebra.smul_def, map_natCast]
      ring
    rw [hd] at h
    have hc : ((k-r : ℕ) : F) ≠ 0 := by
      intro hc
      have hz := CharP.natCast_injOn_Iio F p (show k-r < p by omega)
        (show 0 < p by omega) (by simpa only [Nat.cast_zero] using hc)
      omega
    have hi := W.smul_mem (((k-r : ℕ) : F)⁻¹) h
    simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi

private theorem homogeneous_le_of_pure_power {p k : ℕ} [CharP F p] (hkp : k < p)
    (W : Submodule F (MvPolynomial (Fin 2) F)) (hbase : X 0 ^ k ∈ W)
    (hderiv : ∀ f ∈ W, f.IsHomogeneous k → X 1 * pderiv 0 f ∈ W) :
    homogeneousSubmodule (Fin 2) F k ≤ W := by
  classical
  intro f hf
  rw [f.as_sum]
  apply W.sum_mem
  intro d hd
  have hdeg : d 0 + d 1 = k := by
    have h := hf.degree_eq_sum_deg_support hd
    change k = d.degree at h
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using h.symm
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two, C_mul']
  apply W.smul_mem
  have h := monomial_mem_of_pure_power hkp W hbase hderiv (d 1) (by omega)
  rwa [show k - d 1 = d 0 by omega] at h

public theorem binaryForms_isIrreducible {K : Type*} [Field K] (e : K →+* F)
    {p k : ℕ} [CharP F p] (hkp : k < p) :
    IsIrreducible ((binaryFormsRepresentation F k).comp (Matrix.SpecialLinearGroup.map e)) := by
  classical
  let H := homogeneousSubmodule (Fin 2) F k
  let ρ := (binaryFormsRepresentation F k).comp (Matrix.SpecialLinearGroup.map e)
  have : Nontrivial (homogeneousSubmodule (Fin 2) F k) :=
    Module.nontrivial_of_finrank_eq_succ (R := F)
      (M := homogeneousSubmodule (Fin 2) F k) (binaryForms_finrank F k)
  apply IsSimpleOrder.of_forall_eq_top
  intro U hU
  have hUne : U.toSubmodule ≠ ⊥ := fun h => hU (Subrepresentation.toSubmodule_injective h)
  obtain ⟨f, hfU, hf0⟩ := U.toSubmodule.ne_bot_iff.mp hUne
  let W := U.toSubmodule.map H.subtype
  let x : Fin (k + 1) → F := fun a => (a.val : F)
  have hx : Function.Injective x := by
    intro a b hab
    apply Fin.ext
    exact CharP.natCast_injOn_Iio F p (by change a.val < p; omega)
      (by change b.val < p; omega) hab
  have hinv (i j : Fin 2) (hij : i ≠ j) (g : MvPolynomial (Fin 2) F) (hg : g ∈ W)
      (a : Fin (k + 1)) :
      polynomialAction F (Matrix.SpecialLinearGroup.transvection hij (x a)) g ∈ W := by
    obtain ⟨v, hv, rfl⟩ := hg
    have he : Matrix.SpecialLinearGroup.map e
        (Matrix.SpecialLinearGroup.transvection hij (a.val : K)) =
        Matrix.SpecialLinearGroup.transvection hij (x a) := by
      ext l m
      simp [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe,
        Matrix.single_apply, x, Matrix.one_apply]
      split_ifs <;> simp
    refine ⟨ρ (Matrix.SpecialLinearGroup.transvection hij (a.val : K)) v,
      U.apply_mem_toSubmodule _ hv, ?_⟩
    change polynomialAction F (Matrix.SpecialLinearGroup.map e
      (Matrix.SpecialLinearGroup.transvection hij (a.val : K))) v = _
    rw [he]
    rfl
  have hbase : (X 0 ^ k : MvPolynomial (Fin 2) F) ∈ W := by
    apply X_pow_mem_of_transvection_samples W f f.property
      (fun h => hf0 (Subtype.ext h)) x hx
    exact hinv 0 1 zero_ne_one f ⟨f, hfU, rfl⟩
  have hle : H ≤ W := homogeneous_le_of_pure_power hkp W hbase (fun g hg hhom =>
    X_mul_pderiv_mem_of_transvection_samples W 1 0 one_ne_zero g hhom x hx
      (hinv 1 0 one_ne_zero g hg))
  apply top_unique
  intro v _
  obtain ⟨w, hw, heq⟩ := hle v.property
  have hweq : w = v := Subtype.ext heq
  exact hweq ▸ hw

end Representation.SL2


