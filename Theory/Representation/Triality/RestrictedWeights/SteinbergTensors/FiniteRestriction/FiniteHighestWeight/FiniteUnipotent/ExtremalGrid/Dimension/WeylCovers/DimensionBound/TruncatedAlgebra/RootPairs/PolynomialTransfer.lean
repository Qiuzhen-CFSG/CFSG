module
public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.FiniteHighestWeight.FiniteUnipotent.ExtremalGrid.Dimension.WeylCovers.DimensionBound.TruncatedAlgebra.CoefficientLaws

/-!
# Higher coefficients of a root-pair exchange

One polynomial coefficient extracts transport through the product of two
root curves. A second extracts the full two-parameter straightening law.
The diagonal coefficients then recover the sum-root coefficients inductively
inside any subalgebra containing the two input root strings, provided the
exchange constant is nonzero. All point relations are explicit hypotheses;
no Chevalley parametrization or geometric existence theorem is assumed here.

Source: GLS3 1.12.1(b), and Steinberg, *Representations of algebraic groups*
(1963), §2. The proof uses polynomial coefficients, without factorials.
-/

open Theory.AlgebraicGroup
open Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
namespace Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
public noncomputable section
universe u v
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- A scaled product of two curves gives convolution of their higher coefficients. -/
theorem curveCoefficient_product_intertwine (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y z : Morphism (KPlus k) K)
    (L : Module.End k V) (c : k)
    (h : ∀ t, L * (rho.action (x.onPoints (kPlusPoint t))).val =
      (rho.action (y.onPoints (kPlusPoint t))).val *
        (rho.action (z.onPoints (kPlusPoint (c * t)))).val * L) (j : ℕ) :
    L * curveCoefficient rho hr x j =
      ∑ m ∈ Finset.range (j + 1), c ^ m •
        (curveCoefficient rho hr y (j - m) * curveCoefficient rho hr z m * L) := by
  classical
  ext v
  apply (Module.finBasis k V).repr.injective
  ext b
  let B := Module.finBasis k V
  let l := B.coord b
  have hp : curvePolynomial rho hr x (l.comp L) v =
      ∑ d, (curvePolynomial rho hr z (B.coord d) (L v)).comp
        (Polynomial.C c * Polynomial.X) * curvePolynomial rho hr y l (B d) := by
    apply Polynomial.funext
    intro t
    simp only [curvePolynomial_eval, LinearMap.comp_apply, Polynomial.eval_finsetSum,
      Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_C, Polynomial.eval_X]
    have he := congrArg l (LinearMap.congr_fun (h t) v)
    change l (L ((rho.action (x.onPoints (kPlusPoint t))).val v)) = _
    simp only [Module.End.mul_apply] at he
    rw [he]
    change l ((rho.action (y.onPoints (kPlusPoint t))).val
      ((rho.action (z.onPoints (kPlusPoint (c * t)))).val (L v))) = _
    conv_lhs => rw [← B.sum_repr ((rho.action (z.onPoints (kPlusPoint (c * t)))).val (L v))]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply]
  change (l.comp L) (curveCoefficient rho hr x j v) = _
  rw [dual_curveCoefficient, hp]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Polynomial.comp_C_mul_X_coeff]
  rw [Finset.sum_comm]
  change _ = l ((∑ m ∈ Finset.range (j + 1), c ^ m •
    (curveCoefficient rho hr y (j - m) * curveCoefficient rho hr z m * L)) v)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    Module.End.mul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m hm
  change _ = c ^ m * l (curveCoefficient rho hr y (j - m)
    (∑ d, (curvePolynomial rho hr z (B.coord d) (L v)).coeff m • B d))
  simp only [map_sum, map_smul, smul_eq_mul, dual_curveCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Two coefficient extractions from the actual two-parameter exchange. -/
theorem curveCoefficient_exchange (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y z : Morphism (KPlus k) K)
    (c : k) (h : ∀ s t, x.onPoints (kPlusPoint s) * y.onPoints (kPlusPoint t) =
      y.onPoints (kPlusPoint t) * z.onPoints (kPlusPoint (c * s * t)) *
        x.onPoints (kPlusPoint s)) (i j : ℕ) :
    curveCoefficient rho hr x i * curveCoefficient rho hr y j =
      ∑ m ∈ Finset.range (min i j + 1), c ^ m •
        (curveCoefficient rho hr y (j - m) * curveCoefficient rho hr z m *
          curveCoefficient rho hr x (i - m)) := by
  classical
  have ht (s : k) := curveCoefficient_product_intertwine rho hr y y z
    (rho.action (x.onPoints (kPlusPoint s))).val (c * s) (fun t => by
      simpa only [map_mul, Units.val_mul] using
        congrArg (fun g => (rho.action g).val) (h s t)) j
  ext v
  apply (Module.finBasis k V).repr.injective
  ext b
  let l := (Module.finBasis k V).coord b
  have hp : curvePolynomial rho hr x l (curveCoefficient rho hr y j v) =
      ∑ m ∈ Finset.range (j + 1), c ^ m •
        (curvePolynomial rho hr x
          (l.comp (curveCoefficient rho hr y (j - m) * curveCoefficient rho hr z m)) v *
            Polynomial.X ^ m) := by
    apply Polynomial.funext
    intro s
    simp only [curvePolynomial_eval, Polynomial.eval_finsetSum, Polynomial.eval_smul,
      Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X, LinearMap.comp_apply]
    have he := congrArg l (LinearMap.congr_fun (ht s) v)
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
      Module.End.mul_apply, smul_eq_mul, mul_pow] at he ⊢
    rw [he]
    apply Finset.sum_congr rfl
    intro m hm
    ring
  change l (curveCoefficient rho hr x i (curveCoefficient rho hr y j v)) = _
  rw [dual_curveCoefficient, hp]
  simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    Polynomial.coeff_mul_X_pow', smul_eq_mul]
  have hs : Finset.range (min i j + 1) ⊆ Finset.range (j + 1) :=
    Finset.range_mono (by omega)
  rw [← Finset.sum_subset hs (by
    intro m hm hn
    have hi : ¬ m ≤ i := by
      simp only [Finset.mem_range] at hm hn
      omega
    simp only [if_neg hi, mul_zero])]
  change _ = l ((∑ m ∈ Finset.range (min i j + 1), c ^ m •
    (curveCoefficient rho hr y (j - m) * curveCoefficient rho hr z m *
      curveCoefficient rho hr x (i - m))) v)
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro m hm
  have hi : m ≤ i := by simp only [Finset.mem_range] at hm; omega
  rw [if_pos hi, ← dual_curveCoefficient]
  rfl

/-- A nonzero root-string constant generates every truncated coefficient of the sum root. -/
theorem curveCoefficient_mem_of_exchange (rho : RationalRepresentation K V)
    (hr : IsRationalRepresentation rho) (x y z : Morphism (KPlus k) K)
    (c : k) (hc : c ≠ 0)
    (h : ∀ s t, x.onPoints (kPlusPoint s) * y.onPoints (kPlusPoint t) =
      y.onPoints (kPlusPoint t) * z.onPoints (kPlusPoint (c * s * t)) *
        x.onPoints (kPlusPoint s)) (A : Subalgebra k (Module.End k V)) (q : ℕ)
    (hx : ∀ j < q, curveCoefficient rho hr x j ∈ A)
    (hy : ∀ j < q, curveCoefficient rho hr y j ∈ A) :
    ∀ j < q, curveCoefficient rho hr z j ∈ A := by
  intro j
  induction j using Nat.strong_induction_on with
  | h j ih =>
    intro hj
    have he := curveCoefficient_exchange rho hr x y z c h j j
    simp only [min_self, Finset.sum_range_succ, Nat.sub_self, curveCoefficient_zero,
      one_mul, mul_one] at he
    have hs : (∑ m ∈ Finset.range j, c ^ m •
        (curveCoefficient rho hr y (j - m) * curveCoefficient rho hr z m *
          curveCoefficient rho hr x (j - m))) ∈ A := by
      apply A.sum_mem
      intro m hm
      have hmj : m < j := Finset.mem_range.mp hm
      exact A.smul_mem (A.mul_mem (A.mul_mem (hy _ (by omega))
        (ih m hmj (by omega))) (hx _ (by omega))) _
    have hm : c ^ j • curveCoefficient rho hr z j ∈ A := by
      have he' : c ^ j • curveCoefficient rho hr z j =
          curveCoefficient rho hr x j * curveCoefficient rho hr y j -
            ∑ m ∈ Finset.range j, c ^ m •
              (curveCoefficient rho hr y (j - m) * curveCoefficient rho hr z m *
                curveCoefficient rho hr x (j - m)) := by
        rw [he, add_sub_cancel_left]
      rw [he']
      exact A.sub_mem (A.mul_mem (hx j hj) (hy j hj)) hs
    have hinv := A.smul_mem hm (c ^ j)⁻¹
    simpa only [smul_smul, inv_mul_cancel₀ (pow_ne_zero j hc), one_smul] using hinv
end
end Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.ExtremalGrid.CyclicDimension
