module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.HighestWeight
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.BasicMinimum.EndNode.ShortA2
public import Theory.AlgebraicGroup.Representations.Matrix
public import Mathlib.Algebra.Polynomial.Eval.Degree


/-!
# First coefficients of the actual rational F4 root action

Rationality makes every scalar root-orbit coordinate a polynomial. Its unique
coefficient in degree one defines a linear endomorphism of the factor itself.
The dual-coordinate formula characterizes this operator independently of the
basis used to construct it. Root-group fixation and scaled intertwining
identities pass to these operators by polynomial coefficient comparison.

These constructions work in positive characteristic: no factorial is inverted
and no characteristic-zero differentiation theorem is used.

Source: GLS3, Sections 1.12 and 1.14, applied to the concrete root morphisms.
-/

public section

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

private theorem exists_rootPolynomial (B : AlgebraicFactor F) (r : F4Chevalley.Root)
    (l : Module.Dual F B.Space) (v : B.Space) :
    ∃ p : Polynomial F, ∀ t : F, p.eval t =
      l ((B.action.action (algebraicRootElement r t) : Module.End F B.Space) v) := by
  obtain ⟨b, f, hf⟩ := B.irreducible.1
  let c : Variety.PolynomialFunction (KPlus F) :=
    Variety.PolynomialFunction.pullback (F4Chevalley.rootMorphism r).toVariety
      (rationalRepresentationLinearMatrixCoefficient B.action b f l v)
  obtain ⟨p, hp⟩ := c.representedBy
  refine ⟨MvPolynomial.uniqueAlgEquiv F PUnit p, fun t => ?_⟩
  calc
    (MvPolynomial.uniqueAlgEquiv F PUnit p).eval t =
        MvPolynomial.eval₂ (RingHom.id F) (fun _ => t) p := by
      simpa using MvPolynomial.eval₂_const_uniqueAlgEquiv
        (R := F) (S := F) (f := p) (φ := RingHom.id F) (a := t)
    _ = c (kPlusPoint t) := (hp (kPlusPoint t)).symm
    _ = l ((B.action.action (algebraicRootElement r t) : Module.End F B.Space) v) :=
      rationalRepresentationLinearMatrixCoefficient_apply B.action b f hf l v _

/-- The unique scalar polynomial along an actual root orbit. -/
def rootPolynomial (B : AlgebraicFactor F) (r : F4Chevalley.Root)
    (l : Module.Dual F B.Space) (v : B.Space) : Polynomial F :=
  (exists_rootPolynomial B r l v).choose

theorem rootPolynomial_eval (B : AlgebraicFactor F) (r : F4Chevalley.Root)
    (l : Module.Dual F B.Space) (v : B.Space) (t : F) :
    (rootPolynomial B r l v).eval t =
      l ((B.action.action (algebraicRootElement r t) : Module.End F B.Space) v) :=
  (exists_rootPolynomial B r l v).choose_spec t

theorem rootPolynomial_add (B : AlgebraicFactor F) (r : F4Chevalley.Root)
    (l : Module.Dual F B.Space) (v w : B.Space) :
    rootPolynomial B r l (v + w) = rootPolynomial B r l v + rootPolynomial B r l w := by
  apply Polynomial.funext
  intro t
  simp only [Polynomial.eval_add, rootPolynomial_eval, map_add]

theorem rootPolynomial_smul (B : AlgebraicFactor F) (r : F4Chevalley.Root)
    (l : Module.Dual F B.Space) (c : F) (v : B.Space) :
    rootPolynomial B r l (c • v) = c • rootPolynomial B r l v := by
  apply Polynomial.funext
  intro t
  simp only [Polynomial.eval_smul, rootPolynomial_eval, map_smul]

/-- The first coefficient of the rational action of a root group. -/
@[expose] def rootOperator (B : AlgebraicFactor F) (r : F4Chevalley.Root) : Module.End F B.Space :=
  let b := Module.finBasis F B.Space
  { toFun := fun v => ∑ i, (rootPolynomial B r (b.coord i) v).coeff 1 • b i
    map_add' := by
      intro v w
      simp only [rootPolynomial_add, Polynomial.coeff_add, add_smul, Finset.sum_add_distrib]
    map_smul' := by
      intro c v
      simp only [rootPolynomial_smul, Polynomial.coeff_smul, smul_eq_mul,
        mul_smul, Finset.smul_sum, RingHom.id_apply] }

theorem dual_rootOperator (B : AlgebraicFactor F) (r : F4Chevalley.Root)
    (l : Module.Dual F B.Space) (v : B.Space) :
    l (rootOperator B r v) = (rootPolynomial B r l v).coeff 1 := by
  let b := Module.finBasis F B.Space
  have hp : rootPolynomial B r l v =
      ∑ i, (l (b i)) • rootPolynomial B r (b.coord i) v := by
    apply Polynomial.funext
    intro t
    simp only [Polynomial.eval_finsetSum, Polynomial.eval_smul, rootPolynomial_eval]
    conv_lhs => rw [← b.sum_repr
      ((B.action.action (algebraicRootElement r t) : Module.End F B.Space) v)]
    simp only [map_sum, map_smul, smul_eq_mul, Module.Basis.coord_apply, mul_comm]
  rw [hp]
  change l (∑ i, (rootPolynomial B r (b.coord i) v).coeff 1 • b i) = _
  simp only [map_sum, map_smul, Polynomial.finsetSum_coeff, Polynomial.coeff_smul,
    smul_eq_mul, mul_comm]

theorem rootOperator_eq_zero_of_fixed (B : AlgebraicFactor F) (r : F4Chevalley.Root)
    (v : B.Space)
    (h : ∀ t : F,
      (B.action.action (algebraicRootElement r t) : Module.End F B.Space) v = v) :
    rootOperator B r v = 0 := by
  apply (Module.finBasis F B.Space).repr.injective
  ext i
  change (Module.finBasis F B.Space).coord i (rootOperator B r v) = _
  rw [dual_rootOperator]
  have hp : rootPolynomial B r ((Module.finBasis F B.Space).coord i) v =
      Polynomial.C ((Module.finBasis F B.Space).coord i v) := by
    apply Polynomial.funext
    intro t
    simp only [rootPolynomial_eval, h, Polynomial.eval_C]
  simp [hp]

/-- Extract the degree-one coefficient of a scaled intertwining relation. -/
theorem rootOperator_intertwine (B : AlgebraicFactor F) (r s : F4Chevalley.Root)
    (A D : Module.End F B.Space) (c : F)
    (h : ∀ (t : F) (v : B.Space),
      A ((B.action.action (algebraicRootElement r t) : Module.End F B.Space) v) =
        (B.action.action (algebraicRootElement s (c * t)) : Module.End F B.Space) (D v)) :
    A * rootOperator B r = c • (rootOperator B s * D) := by
  ext v
  apply (Module.finBasis F B.Space).repr.injective
  ext i
  let l := (Module.finBasis F B.Space).coord i
  have hp : rootPolynomial B r (l.comp A) v =
      (rootPolynomial B s l (D v)).comp (Polynomial.C c * Polynomial.X) := by
    apply Polynomial.funext
    intro t
    simp only [rootPolynomial_eval, Polynomial.eval_comp, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, LinearMap.comp_apply, h]
  have hc := congrArg (fun p : Polynomial F => p.coeff 1) hp
  rw [← dual_rootOperator, Polynomial.comp_C_mul_X_coeff, pow_one,
    ← dual_rootOperator] at hc
  change l (A (rootOperator B r v)) = l (c • rootOperator B s (D v))
  simpa only [LinearMap.comp_apply, map_smul, smul_eq_mul, mul_comm] using hc

end
end ReeF4.BinaryDegree.ExceptionalTensor.EndNode.Multiplicity
