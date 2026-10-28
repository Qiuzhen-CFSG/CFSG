module

public import Theory.AlgebraicGroup.Unipotent.Contraction.Defs
public import Theory.AlgebraicGroup.Unipotent.Contraction.Matrix
public import Theory.AlgebraicGroup.RightTranslation.MatrixCoefficients

/-!
Cocharacter-contracted elements are unipotent, in arbitrary characteristic.

For each polynomial function, its right translates span a finite-dimensional
stable space. Point evaluations span that space's dual, so the translation
matrices have regular coefficients. The contracting curve forces their
characteristic polynomial to equal that of the identity, as proved in
`Contraction.Matrix`. Nilpotence on each such space gives exactly the local
nilpotence of right translation defining `IsUnipotentElement`.

This supplies the contraction-to-unipotence step in the positive-root argument
of Borel, §14.5, and GLS3, Theorem 1.11.2, using the intrinsic definition from
GLS3, §§1.2–1.3. No connectedness or reductivity hypothesis is required.
-/

universe u

namespace Theory.AlgebraicGroup
variable {k : Type u} [Field k] [IsAlgClosed k]
variable {G : Variety k} [AlgebraicGroup G]

/-- If inverse conjugation by a cocharacter extends regularly to the affine
line with value one at zero, the contracted element is unipotent. -/
public theorem IsCocharacterContracted.isUnipotentElement
    {lambda : AlgebraicGroup.Morphism (KMult k) G}
    {g : Variety.Point G} (hg : IsCocharacterContracted lambda g) :
    IsUnipotentElement G g := by
  classical
  intro q
  let W := rightTranslateOrbitSpan G q
  let τ : Variety.Point G →* Module.End k W :=
    { toFun := fun x => (rightTranslationPullback G x).restrict
        (rightTranslateOrbitSpan_stable G q x)
      map_one' := by
        ext r x
        change r.val (x * 1) = r.val x
        rw [mul_one]
      map_mul' := by
        intro x y
        ext r z
        change r.val (z * (x * y)) = r.val ((z * x) * y)
        rw [mul_assoc] }
  let n := Module.finrank k W
  let b : Module.Basis (Fin n) k W := Module.finBasis k W
  let ρ : Variety.Point G →* Matrix (Fin n) (Fin n) k :=
    (LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp τ
  let c : Matrix (Fin n) (Fin n) (Variety.PolynomialFunction G) :=
    fun i j => (polynomialFunctionSubspaceDualCoefficients G W (b.coord i)).sum
      fun x a => a • Variety.PolynomialFunction.pullback
        (AlgebraicGroup.leftMulMorphism G x) (b j).val
  have hc (g' : Variety.Point G) (i j : Fin n) : c i j g' = ρ g' i j := by
    let d := polynomialFunctionSubspaceDualCoefficients G W (b.coord i)
    have hd := congrArg (fun L : Module.Dual k W => L (τ g' (b j)))
      (polynomialFunctionSubspaceDualCoefficients_spec G W (b.coord i))
    change ((d.sum fun x a => a • polynomialFunctionSubspaceEvaluation G W x)
      (τ g' (b j))) = b.repr (τ g' (b j)) i at hd
    change c i j g' = (LinearMap.toMatrixAlgEquiv b) (τ g') i j
    rw [LinearMap.toMatrixAlgEquiv_apply]
    rw [← hd]
    change polynomialFunctionEvalAddHom G g'
        (d.sum fun x a => a • Variety.PolynomialFunction.pullback
          (AlgebraicGroup.leftMulMorphism G x) (b j).val) =
      (LinearMap.applyₗ (R := k) (M := W) (M₂ := k) (τ g' (b j)))
        (d.sum fun x a => a • polynomialFunctionSubspaceEvaluation G W x)
    rw [map_finsuppSum, map_finsuppSum]
    apply Finsupp.sum_congr
    intro x hx
    simp only [Variety.PolynomialFunction.pullback,
      AlgebraicGroup.leftMulMorphism_apply, polynomialFunctionSubspaceEvaluation]
    rw [polynomialFunctionEvalAddHom_apply]
    simp only [polynomialFunction_smul_apply]
    rw [map_smul, LinearMap.applyₗ_apply_apply]
    simp only [smul_eq_mul]
    rfl
  have hnil : (τ g - 1) ^ n = 0 := by
    apply (LinearMap.toMatrixAlgEquiv b).injective
    rw [map_pow, map_sub (LinearMap.toMatrixAlgEquiv b), map_one, map_zero]
    exact hg.matrix_sub_one_pow_eq_zero ρ c hc
  have hq : q ∈ W := Submodule.subset_span
    ⟨1, AlgebraicGroup.rightMul_pullback_one G q⟩
  let qW : W := ⟨q, hq⟩
  have hsemi : Function.Semiconj (fun r : W => r.val)
      ⇑(τ g - 1 : Module.End k W) ⇑(rightTranslationPullback G g - 1) := by
    intro r
    rfl
  refine ⟨n, ?_⟩
  have hzero : (⇑(τ g - 1 : Module.End k W))^[n] qW = 0 := by
    rw [← Module.End.pow_apply, hnil]
    rfl
  have h := hsemi.iterate_right n qW
  rw [hzero] at h
  exact h.symm

end Theory.AlgebraicGroup
