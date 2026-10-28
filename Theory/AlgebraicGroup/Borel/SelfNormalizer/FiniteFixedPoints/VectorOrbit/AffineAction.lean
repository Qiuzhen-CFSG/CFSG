module

public import Theory.AlgebraicGroup.Representations.Matrix
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism
public import Theory.AlgebraicGroup.Variety.AffineSpace

/-!
# The regular affine action of a rational representation

In a finite basis, the action coordinates are sums of regular matrix
coefficients times vector coordinates. This constructs the actual morphism
on the product and transports it to the geometric affine space.

This is the affine-action input for Borel, *Linear Algebraic Groups*,
Theorem 11.16(iii), `refs/KGroup/Bor1/Chapter4.tex`.
-/

universe u v
namespace Theory.AlgebraicGroup.BorelSelfNormalizer
open Variety.Geometric
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]
variable {V : Type v} [AddCommGroup V] [Module k V] [Module.Finite k V]
variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Identify the geometric affine coordinates in a basis with vectors. -/
@[expose]
public noncomputable def vectorAffinePointEquiv (b : Module.Basis ι k V) :
    Point (ofAffine (affineSpaceVariety k ι)) ≃ V where
  toFun x := b.equivFun.symm (affinePointEquiv (affineSpaceVariety k ι) x).val
  invFun v := (affinePointEquiv (affineSpaceVariety k ι)).symm
    (affineSpacePoint (b.equivFun v))
  left_inv x := by
    apply (affinePointEquiv (affineSpaceVariety k ι)).injective
    rw [Equiv.apply_symm_apply]
    apply Variety.Point.ext
    exact b.equivFun.apply_symm_apply _
  right_inv v := by
    simp only [Equiv.apply_symm_apply]
    exact b.equivFun.symm_apply_apply v

private theorem exists_affine_action_morphism
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis ι k V) :
    ∃ F : Variety.Morphism (Variety.prod G (affineSpaceVariety k ι))
        (affineSpaceVariety k ι),
      ∀ z, F.toFun z = affineSpacePoint (b.equivFun
        ((ρ.action (Variety.prodPointEquiv G (affineSpaceVariety k ι) z).1).1
          (b.equivFun.symm (Variety.prodPointEquiv G (affineSpaceVariety k ι) z).2.val))) := by
  obtain ⟨e, f, hf⟩ := hρ
  let A := affineSpaceVariety k ι
  let c (i j : ι) := rationalRepresentationLinearMatrixCoefficient ρ e f (b.coord i) (b j)
  have hc (i j : ι) (g : Variety.Point G) :
      c i j g = (b.repr ((ρ.action g).1 (b j))) i :=
    rationalRepresentationLinearMatrixCoefficient_apply ρ e f hf (b.coord i) (b j) g
  let q (i : ι) : (Variety.prod G A).PolynomialFunction :=
    ∑ j, polynomialFunctionLeft G A (c i j) *
      polynomialFunctionRight G A (Variety.PolynomialFunction.ofPolynomial A (MvPolynomial.X j))
  have hq (i : ι) (z : Variety.Point (Variety.prod G A)) :
      q i z = (b.equivFun ((ρ.action (Variety.prodPointEquiv G A z).1).1
        (b.equivFun.symm (Variety.prodPointEquiv G A z).2.val))) i := by
    change polynomialFunctionEvalAddHom (Variety.prod G A) z (∑ j, _) = _
    rw [map_sum]
    change (∑ j, c i j (Variety.prodPointEquiv G A z).1 *
      evalPolynomial (Variety.prodPointEquiv G A z).2.val (MvPolynomial.X j)) = _
    simp_rw [evalPolynomial_X, hc]
    rw [Module.Basis.equivFun_apply,
      ← LinearMap.repr_apply_eq_sum_toMatrix b
        (ρ.action (Variety.prodPointEquiv G A z).1).1
        (b.equivFun.symm (Variety.prodPointEquiv G A z).2.val) i]
    apply Finset.sum_congr rfl
    intro j _
    rw [LinearMap.toMatrix_apply]
    have hj := congrFun (b.equivFun.apply_symm_apply
      (Variety.prodPointEquiv G A z).2.val) j
    change (b.repr (b.equivFun.symm (Variety.prodPointEquiv G A z).2.val)) j =
      (Variety.prodPointEquiv G A z).2.val j at hj
    rw [hj, mul_comm]
  refine ⟨{
    toFun := fun z => affineSpacePoint (b.equivFun
      ((ρ.action (Variety.prodPointEquiv G A z).1).1
        (b.equivFun.symm (Variety.prodPointEquiv G A z).2.val)))
    regular := ?_ }, fun _ => rfl⟩
  intro i
  obtain ⟨p, hp⟩ := (q i).representedBy
  exact ⟨p, fun z => (hq i z).symm.trans (hp z)⟩

/-- A rational representation acts regularly on its affine vector space. -/
public noncomputable def vectorAffineAction
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis ι k V) : MorphicAction G (ofAffine (affineSpaceVariety k ι)) where
  smul g x := (vectorAffinePointEquiv b).symm ((ρ.action g).1 (vectorAffinePointEquiv b x))
  one_smul x := by
    change (vectorAffinePointEquiv b).symm ((ρ.action 1).1 (vectorAffinePointEquiv b x)) = x
    rw [map_one]
    exact (vectorAffinePointEquiv b).symm_apply_apply x
  mul_smul g h x := by
    change (vectorAffinePointEquiv b).symm ((ρ.action (g * h)).1
      (vectorAffinePointEquiv b x)) = (vectorAffinePointEquiv b).symm
      ((ρ.action g).1 (vectorAffinePointEquiv b ((vectorAffinePointEquiv b).symm
        ((ρ.action h).1 (vectorAffinePointEquiv b x)))))
    rw [Equiv.apply_symm_apply, map_mul]
    rfl
  actionMorphism := ofAffineProductMorphism (exists_affine_action_morphism ρ hρ b).choose
  actionMorphism_apply g x := by
    apply (affinePointEquiv (affineSpaceVariety k ι)).injective
    rw [affinePointEquiv_ofAffineProductMorphism_prodPoint,
      (exists_affine_action_morphism ρ hρ b).choose_spec]
    simp only [Equiv.apply_symm_apply]
    exact (Equiv.apply_symm_apply (affinePointEquiv (affineSpaceVariety k ι)) _).symm

/-- The constructed regular action is exactly the given linear action. -/
public theorem vectorAffineAction_apply
    (ρ : RationalRepresentation G V) (hρ : IsRationalRepresentation ρ)
    (b : Module.Basis ι k V) (g : Variety.Point G)
    (x : Point (ofAffine (affineSpaceVariety k ι))) :
    vectorAffinePointEquiv b ((vectorAffineAction ρ hρ b).toMulAction.smul g x) =
      (ρ.action g).1 (vectorAffinePointEquiv b x) :=
  (vectorAffinePointEquiv b).apply_symm_apply _

end Theory.AlgebraicGroup.BorelSelfNormalizer
