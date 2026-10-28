module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.Operations
public import Theory.AlgebraicGroup.Representations.Matrix
public import Theory.AlgebraicGroup.Unipotent.OneParameterCore
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Algebra.Polynomial.Expand
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Root coefficients and Frobenius tensor products

A rational orbit along an additive one-parameter group has unique polynomial
coordinates. Their first coefficients define a linear operator, characterized
by all covectors, which preserves each invariant subspace. When a regular
endomorphism squares the parameter, the first coefficient on a tensor with
its pullback is the first-factor operator tensored with the identity.

This is a polynomial argument in arbitrary characteristic, without division by
factorials. The scalar-coordinate construction generalizes the checked F4
construction in `EndNode.Multiplicity.RootOperators` to arbitrary rational
representations and arbitrary additive one-parameter morphisms.

This supplies a coefficient step toward the ordinary-Frobenius case of
Steinberg's tensor theorem, GLS3, Theorem 2.8.5 / [St2, Theorem 13.1].
-/

open Theory.AlgebraicGroup
open scoped TensorProduct
namespace Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
public noncomputable section
universe u v w
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {K : Variety k} [AlgebraicGroup K]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private theorem exists_curvePolynomial
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K)
    (l : Module.Dual k V) (v : V) :
    ∃ p : Polynomial k, ∀ t : k,
      p.eval t = l ((ρ.action (x.onPoints (kPlusPoint t))).val v) := by
  obtain ⟨b, f, hf⟩ := hρ
  let c : Variety.PolynomialFunction (KPlus k) :=
    Variety.PolynomialFunction.pullback x.toVariety
      (rationalRepresentationLinearMatrixCoefficient ρ b f l v)
  obtain ⟨p, hp⟩ := c.representedBy
  refine ⟨MvPolynomial.uniqueAlgEquiv k PUnit p, fun t => ?_⟩
  calc
    (MvPolynomial.uniqueAlgEquiv k PUnit p).eval t =
        MvPolynomial.eval₂ (RingHom.id k) (fun _ => t) p := by
      simpa using MvPolynomial.eval₂_const_uniqueAlgEquiv
        (R := k) (S := k) (f := p) (φ := RingHom.id k) (a := t)
    _ = c (kPlusPoint t) := (hp (kPlusPoint t)).symm
    _ = _ := rationalRepresentationLinearMatrixCoefficient_apply ρ b f hf l v _

/-- The scalar polynomial of a rational orbit along an additive one-parameter group. -/
def curvePolynomial
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K)
    (l : Module.Dual k V) (v : V) : Polynomial k :=
  (exists_curvePolynomial ρ hρ x l v).choose

theorem curvePolynomial_eval
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K)
    (l : Module.Dual k V) (v : V) (t : k) :
    (curvePolynomial ρ hρ x l v).eval t =
      l ((ρ.action (x.onPoints (kPlusPoint t))).val v) :=
  (exists_curvePolynomial ρ hρ x l v).choose_spec t

theorem curvePolynomial_add
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K)
    (l : Module.Dual k V) (v w : V) :
    curvePolynomial ρ hρ x l (v + w) =
      curvePolynomial ρ hρ x l v + curvePolynomial ρ hρ x l w := by
  apply Polynomial.funext
  intro t
  simp only [Polynomial.eval_add, curvePolynomial_eval, map_add]

theorem curvePolynomial_smul
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K)
    (l : Module.Dual k V) (c : k) (v : V) :
    curvePolynomial ρ hρ x l (c • v) = c • curvePolynomial ρ hρ x l v := by
  apply Polynomial.funext
  intro t
  simp only [Polynomial.eval_smul, curvePolynomial_eval, map_smul]

/-- The first polynomial coefficient of the actual action; no factorial is inverted. -/
@[expose] def curveOperator
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K) : Module.End k V :=
  let b := Module.finBasis k V
  { toFun := fun v => ∑ i, (curvePolynomial ρ hρ x (b.coord i) v).coeff 1 • b i
    map_add' := by
      intro v w
      simp only [curvePolynomial_add, Polynomial.coeff_add, add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro c v
      simp only [curvePolynomial_smul, Polynomial.coeff_smul, smul_eq_mul,
        mul_smul, Finset.smul_sum, RingHom.id_apply] }

/-- Covectors characterize the first coefficient independently of the chosen basis. -/
theorem dual_curveOperator
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K)
    (l : Module.Dual k V) (v : V) :
    l (curveOperator ρ hρ x v) = (curvePolynomial ρ hρ x l v).coeff 1 := by
  let b := Module.finBasis k V
  have hp : curvePolynomial ρ hρ x l v =
      ∑ i, l (b i) • curvePolynomial ρ hρ x (b.coord i) v := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, curvePolynomial_eval]
    conv_lhs => rw [← b.sum_repr ((ρ.action (x.onPoints (kPlusPoint t))).val v)]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply, mul_comm]
  rw [hp]
  change l (∑ i, (curvePolynomial ρ hρ x (b.coord i) v).coeff 1 • b i) = _
  simp only [map_sum, map_smul, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    smul_eq_mul, mul_comm]

/-- A subspace invariant under the point action is stable under its first root coefficient. -/
theorem curveOperator_mem
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K)
    (U : Submodule k V) (hU : IsInvariantSubmodule ρ U) (v : V) (hv : v ∈ U) :
    curveOperator ρ hρ x v ∈ U := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
  intro l hl
  rw [dual_curveOperator]
  have hp : curvePolynomial ρ hρ x l v = 0 := by
    apply Polynomial.funext
    intro t
    rw [curvePolynomial_eval, Polynomial.eval_zero]
    exact (Submodule.mem_dualAnnihilator _).mp hl _ (hU _ _ hv)
  simp [hp]

/-- The constant coefficient is the original vector coordinate. -/
theorem curvePolynomial_coeff_zero
    (ρ : RationalRepresentation K V) (hρ : IsRationalRepresentation ρ)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K)
    (l : Module.Dual k V) (v : V) :
    (curvePolynomial ρ hρ x l v).coeff 0 = l v := by
  have hz : kPlusPoint (0 : k) = 1 := by
    apply (additiveGroupPointEquiv k).injective
    rfl
  rw [Polynomial.coeff_zero_eq_eval_zero, curvePolynomial_eval, hz, map_one, map_one]
  rfl

variable {W : Type w} [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- The specified tensor of the first action with a regular pullback of the second. -/
@[expose] def tensorPullback (φ : Theory.AlgebraicGroup.Morphism K K)
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W) :
    RationalRepresentation K (V ⊗[k] W) :=
  algebraicAction (Representation.tprod
    ((Units.coeHom _).comp ρ.action)
    ((Units.coeHom _).comp (pullback φ σ).action))

theorem tensorPullback_rational (φ : Theory.AlgebraicGroup.Morphism K K)
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    (hρ : IsRationalRepresentation ρ) (hσ : IsRationalRepresentation σ) :
    IsRationalRepresentation (tensorPullback φ ρ σ) := by
  apply tprod_rational
  · apply rational_of_action_eq _ ρ _ hρ
    intro g
    rw [algebraicAction_apply]
    rfl
  · apply rational_of_action_eq _ (pullback φ σ) _ (pullback_rational φ σ hσ)
    intro g
    rw [algebraicAction_apply]
    rfl

omit [IsAlgClosed k] [FiniteDimensional k V] [FiniteDimensional k W] in
theorem tensorPullback_apply_tmul (φ : Theory.AlgebraicGroup.Morphism K K)
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    (g : Variety.Point K) (v : V) (w : W) :
    ((tensorPullback φ ρ σ).action g).val (v ⊗ₜ[k] w) =
      (ρ.action g).val v ⊗ₜ[k] (σ.action (φ.onPoints g)).val w := rfl

/-- Squaring a root parameter kills its degree-one coefficient in the second
factor. The first coefficient of the tensor action acts on the left alone. -/
theorem curveOperator_tensorPullback
    (φ : Theory.AlgebraicGroup.Morphism K K)
    (ρ : RationalRepresentation K V) (σ : RationalRepresentation K W)
    (hρ : IsRationalRepresentation ρ) (hσ : IsRationalRepresentation σ)
    (x : Theory.AlgebraicGroup.Morphism (KPlus k) K)
    (hx : ∀ t, φ.onPoints (x.onPoints (kPlusPoint t)) =
      x.onPoints (kPlusPoint (t ^ 2))) :
    curveOperator (tensorPullback φ ρ σ) (tensorPullback_rational φ ρ σ hρ hσ) x =
      (curveOperator ρ hρ x).rTensor W := by
  apply TensorProduct.ext'
  intro v w
  let b := Module.finBasis k V
  let c := Module.finBasis k W
  apply (b.tensorProduct c).repr.injective
  ext ij
  obtain ⟨i, j⟩ := ij
  let l := (b.tensorProduct c).coord (i, j)
  have hp : curvePolynomial (tensorPullback φ ρ σ)
      (tensorPullback_rational φ ρ σ hρ hσ) x l (v ⊗ₜ[k] w) =
      curvePolynomial ρ hρ x (b.coord i) v *
        (curvePolynomial σ hσ x (c.coord j) w).comp (Polynomial.X ^ 2) := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_pow,
      Polynomial.eval_X, curvePolynomial_eval, tensorPullback_apply_tmul, hx]
    change (b.tensorProduct c).repr
      ((ρ.action (x.onPoints (kPlusPoint t))).val v ⊗ₜ[k]
        (σ.action (x.onPoints (kPlusPoint (t ^ 2)))).val w) (i, j) = _
    rw [Module.Basis.tensorProduct_repr_tmul_apply]
    simp only [Module.Basis.coord_apply, smul_eq_mul, mul_comm]
  change l (curveOperator (tensorPullback φ ρ σ)
    (tensorPullback_rational φ ρ σ hρ hσ) x (v ⊗ₜ[k] w)) =
      l ((curveOperator ρ hρ x v) ⊗ₜ[k] w)
  rw [dual_curveOperator, hp, Polynomial.mul_coeff_one,
    ← Polynomial.expand_eq_comp_X_pow, Polynomial.coeff_expand (by decide : 0 < 2),
    Polynomial.coeff_expand (by decide : 0 < 2)]
  norm_num only [show ¬ 2 ∣ 1 by decide, show 2 ∣ 0 by decide, if_false, if_true,
    Nat.zero_div, mul_zero, zero_add]
  rw [curvePolynomial_coeff_zero, ← dual_curveOperator]
  change _ = (b.tensorProduct c).repr ((curveOperator ρ hρ x v) ⊗ₜ[k] w) (i, j)
  rw [Module.Basis.tensorProduct_repr_tmul_apply]
  simp only [Module.Basis.coord_apply, smul_eq_mul, mul_comm]

end
end Triality.RestrictedWeights.SteinbergTensors.AlgebraicTensor.RestrictedStep
