module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction.TensorGrading.WeightDegrees
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.TensorStep.PolynomialExpansion
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.Multiplicity.TorusCovariance

/-!
# Full weight shifts of every rational root coefficient

Compare polynomial coefficients in the actual coroot covariance equation.
The coefficient of degree `n` shifts every coroot coordinate by `n` times
the root's Cartan pairing. In particular its integral degree shifts by
`n` times the native root degree. This concerns all coefficients and all
roots, and uses the given genuine rational root expansion throughout.

Source: Steinberg (1963), Sections 5 and 12; GLS3 Sections 1.12 and 1.14.
-/

public section
noncomputable section
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction

open Theory.AlgebraicGroup StandardRootSystem EndNode
open AlgebraicTensor
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

private def scalarPolynomial {V : Type*} [AddCommGroup V] [Module F V]
    (p : ℕ →₀ Module.End F V) (l : Module.Dual F V) (v : V) : Polynomial F :=
  p.sum fun n A => Polynomial.monomial n (l (A v))

omit [IsAlgClosed F] in
private theorem scalarPolynomial_eval {V : Type*} [AddCommGroup V] [Module F V]
    (p : ℕ →₀ Module.End F V) (l : Module.Dual F V) (v : V) (t : F) :
    (scalarPolynomial p l v).eval t = l ((p.sum fun n A => t ^ n • A) v) := by
  simp only [scalarPolynomial, Finsupp.sum, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul,
    smul_eq_mul, mul_comm]

omit [IsAlgClosed F] in
private theorem scalarPolynomial_coeff {V : Type*} [AddCommGroup V] [Module F V]
    (p : ℕ →₀ Module.End F V) (l : Module.Dual F V) (v : V) (n : ℕ) :
    (scalarPolynomial p l v).coeff n = l (p n v) := by
  classical
  simp only [scalarPolynomial, Finsupp.sum, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial]
  by_cases hn : n ∈ p.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro i _ hi
      simp [hi]
    · exact fun h => (h hn).elim
  · rw [Finset.sum_eq_zero (fun i hi => if_neg (by
      intro h
      exact hn (h ▸ hi)))]
    simp [Finsupp.notMem_support_iff.mp hn]

/-- Extract any coefficient of a scaled intertwining equation. -/
theorem coeff_intertwine (B : AlgebraicFactor F) (p : RootExpansion B.action)
    (r s : F4Chevalley.Root) (A D : Module.End F B.Space) (c : F)
    (h : ∀ (t : F) (v : B.Space),
      A ((B.action.action (algebraicRootElement r t) : Module.End F B.Space) v) =
        (B.action.action (algebraicRootElement s (c * t)) : Module.End F B.Space) (D v))
    (n : ℕ) : A * p.coeff r n = c ^ n • (p.coeff s n * D) := by
  ext v
  apply (Module.finBasis F B.Space).repr.injective
  ext i
  let l := (Module.finBasis F B.Space).coord i
  have hp : scalarPolynomial (p.coeff r) (l.comp A) v =
      (scalarPolynomial (p.coeff s) l (D v)).comp (Polynomial.C c * Polynomial.X) := by
    apply Polynomial.funext
    intro t
    simp only [scalarPolynomial_eval, p.eval_eq, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, LinearMap.comp_apply, h]
  have hc := congrArg (fun q : Polynomial F => q.coeff n) hp
  rw [scalarPolynomial_coeff, Polynomial.comp_C_mul_X_coeff,
    scalarPolynomial_coeff] at hc
  change l (A (p.coeff r n v)) = l (c ^ n • p.coeff s n (D v))
  simpa only [LinearMap.comp_apply, map_smul, smul_eq_mul, mul_comm] using hc

/-- Every root coefficient has its exact full four-coroot weight shift. -/
theorem coeff_mem_corootWeightSpace (B : AlgebraicFactor F) (p : RootExpansion B.action)
    (r : F4Chevalley.Root) (n : ℕ) (μ : EndNode.Weight) {v : B.Space}
    (hv : v ∈ corootWeightSpace B μ) :
    p.coeff r n v ∈ corootWeightSpace B (μ + n • rootWeight r) := by
  apply (mem_corootWeightSpace B _ _).mpr
  intro j t
  let A : Module.End F B.Space :=
    B.action.action (algebraicCorootElement (typeF4SimpleRootIndex j) t)
  have he := coeff_intertwine B p r r A A ((t : F) ^ rootWeight r j) (by
    intro a w
    have hh := congrArg (fun g => (B.action.action g : Module.End F B.Space) w)
      (Multiplicity.coroot_root_commute (typeF4RootPairing_baseEquiv j) r t a)
    simpa only [map_mul, Units.val_mul, Module.End.mul_apply, A, rootWeight,
      typeF4RootPairing_baseEquiv_val] using hh) n
  have he' := congrArg (fun L : Module.End F B.Space => L v) he
  have ht := (mem_corootWeightSpace B μ v).mp hv j t
  change A (p.coeff r n v) = ((t : F) ^ rootWeight r j) ^ n • p.coeff r n (A v) at he'
  change A v = _ at ht
  rw [ht, map_smul, smul_smul] at he'
  convert he' using 1
  change ((t : F) ^ (μ j + (n : ℤ) * rootWeight r j)) • _ = _
  rw [zpow_add₀ t.ne_zero, mul_comm (n : ℤ), zpow_mul, zpow_natCast, mul_comm]

/-- The coefficient shift changes the integer degree by its degree times
its polynomial exponent. -/
theorem coefficient_weightDegree (μ : EndNode.Weight) (r : F4Chevalley.Root) (n : ℕ) :
    weightDegree (μ + n • rootWeight r) =
      weightDegree μ + (n : ℤ) * weightDegree (rootWeight r) := by
  rw [weightDegree_add, weightDegree_nsmul]

end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.FiniteRootAction
