module

public import Theory.Representation.SL2.HighestWeightSpan
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Tactic.LinearCombination

/-!
# Central Sign on Highest-Weight Modules

The central matrix `-I` acts on the degree-`n` highest-weight orbit span by
`(-1)^n`. If the coefficient field has characteristic different from two,
it belongs to the representation kernel precisely when `n` is even.

Substitution by `-I` negates both variables. Each degree-`n` monomial acquires
the same scalar, so the action formula holds on the homogeneous space and
hence on its actual highest-weight subrepresentation. The nonzero pure-power
generator detects whether the scalar is one. This is the parity input for
the faithful refinement of Fong--Wong (1E), p. 149; no classification theorem
is assumed here.
-/

open MvPolynomial
open scoped MatrixGroups

namespace Representation.SL2

variable {K F : Type*} [Field K] [Field F]

private theorem polynomialAction_neg_one_X (e : K →+* F) (i : Fin 2) :
    polynomialAction F (Matrix.SpecialLinearGroup.map e (-1)) (X i) = -X i := by
  simp [polynomialAction, Matrix.SpecialLinearGroup.map_apply_coe, Matrix.one_apply,
    Matrix.neg_apply]

private theorem polynomialAction_neg_one (e : K →+* F) (n : ℕ)
    (f : MvPolynomial (Fin 2) F) (hf : f.IsHomogeneous n) :
    polynomialAction F (Matrix.SpecialLinearGroup.map e (-1)) f = (-1 : F)^n • f := by
  classical
  conv_lhs => rw [f.as_sum, map_sum]
  conv_rhs => rw [f.as_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdeg : d 0 + d 1 = n := by
    have h := hf.degree_eq_sum_deg_support hd
    change n = d.degree at h
    simpa only [Finsupp.degree_eq_sum, Fin.sum_univ_two] using h.symm
  rw [monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]
  simp only [map_mul, map_pow, polynomialAction_neg_one_X]
  rw [show polynomialAction F (Matrix.SpecialLinearGroup.map e (-1)) (C (coeff d f)) =
    C (coeff d f) by simp [polynomialAction]]
  simp only [Algebra.smul_def, MvPolynomial.algebraMap_eq, map_pow, map_neg, map_one]
  rw [neg_pow, neg_pow, ← hdeg, pow_add]
  ring

public theorem highestWeightSpan_neg_one_apply (e : K →+* F) (n : ℕ)
    (v : (highestWeightSpan e n).toSubmodule) :
    (highestWeightSpan e n).toRepresentation (-1) v = (-1 : F)^n • v := by
  apply Subtype.ext
  exact polynomialAction_neg_one e n v (highestWeightSpan_le_homogeneous e n v.property)

public theorem highestWeightSpan_neg_one_mem_ker_iff (e : K →+* F) (n : ℕ) (hF : (2 : F) ≠ 0) :
    (-1 : SL(2, K)) ∈ (highestWeightSpan e n).toRepresentation.ker ↔ Even n := by
  have hv0 : (X 0 ^ n : MvPolynomial (Fin 2) F) ≠ 0 := pow_ne_zero _ (X_ne_zero _)
  let v : (highestWeightSpan e n).toSubmodule := ⟨X 0 ^ n, X_pow_mem_highestWeightSpan e n⟩
  constructor
  · intro h
    have he : (highestWeightSpan e n).toRepresentation (-1) = 1 := h
    have hx := congrArg (fun f : Module.End F (highestWeightSpan e n).toSubmodule => f v) he
    rw [highestWeightSpan_neg_one_apply] at hx
    have heq : (-1 : F)^n = 1 := by
      apply smul_left_injective F (show v ≠ 0 from fun h => hv0 (congrArg Subtype.val h))
      simpa using hx
    exact (neg_one_pow_eq_one_iff_even (by intro h; apply hF; linear_combination -h)).mp heq
  · intro hn
    change (highestWeightSpan e n).toRepresentation (-1) = 1
    apply LinearMap.ext
    intro v
    rw [highestWeightSpan_neg_one_apply, hn.neg_one_pow, one_smul]
    rfl

end Representation.SL2

