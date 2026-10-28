module

public import Mathlib.RepresentationTheory.Basic
public import Theory.AlgebraicGroup.RightTranslation.Vanishing

universe u

/-!
The finite-dimensional right-translation representation attached to a closed
subgroup's vanishing-ideal generators.
-/

namespace Theory.AlgebraicGroup

section

variable {k : Type u} [Field k]

/-- Right translation restricted to the finite-dimensional span of the chosen
vanishing-ideal generators. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingSpanLinearMap
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (x : Variety.Point G) :
    H.rightTranslateVanishingSpan →ₗ[k] H.rightTranslateVanishingSpan :=
  (AlgebraicGroup.rightMulMorphism G x).pullbackAlgHom.toLinearMap.restrict
    (fun q hq => by
      change (AlgebraicGroup.rightMulMorphism G x).pullbackAlgHom q ∈
        H.rightTranslateVanishingSpan
      exact H.rightTranslateVanishingSpan_stable x q hq)

/-- The finite-dimensional right-translation representation attached to a
closed subgroup. -/
public noncomputable def ClosedSubgroup.rightTranslateVanishingSpanRepresentation
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Representation k (Variety.Point G) H.rightTranslateVanishingSpan where
  toFun := H.rightTranslateVanishingSpanLinearMap
  map_one' := by
    ext q g
    change q.1 (g * 1) = q.1 g
    rw [mul_one]
  map_mul' := by
    intro x y
    ext q g
    change q.1 (g * (x * y)) = q.1 ((g * x) * y)
    rw [mul_assoc]

/-- The same representation as a homomorphism to the general linear group. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingSpanGeneralLinear
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Variety.Point G →*
      LinearMap.GeneralLinearGroup k H.rightTranslateVanishingSpan where
  toFun := fun g =>
    { val := H.rightTranslateVanishingSpanLinearMap g
      inv := H.rightTranslateVanishingSpanLinearMap g⁻¹
      val_inv := by
        change H.rightTranslateVanishingSpanRepresentation g *
          H.rightTranslateVanishingSpanRepresentation g⁻¹ = 1
        rw [← map_mul, mul_inv_cancel, map_one]
      inv_val := by
        change H.rightTranslateVanishingSpanRepresentation g⁻¹ *
          H.rightTranslateVanishingSpanRepresentation g = 1
        rw [← map_mul, inv_mul_cancel, map_one] }
  map_one' := by
    apply Units.ext
    ext q g
    change q.1 (g * 1) = q.1 g
    rw [mul_one]
  map_mul' := by
    intro x y
    apply Units.ext
    ext q g
    change q.1 (g * (x * y)) = q.1 ((g * x) * y)
    rw [mul_assoc]

end

/-! Point evaluations span the dual of a finite-dimensional subspace of polynomial functions. -/

section

variable {k : Type u} [Field k]

/-- Evaluation at a point, restricted to a polynomial-function subspace. -/
@[expose]
public def polynomialFunctionSubspaceEvaluation (G : Variety k)
    (W : Submodule k G.PolynomialFunction) (x : Variety.Point G) :
    Module.Dual k W where
  toFun := fun f => f.1 x
  map_add' := fun _ _ => rfl
  map_smul' := by
    intro r f
    exact polynomialFunction_smul_apply G r f.1 x

/-- Point evaluations span the dual of any finite-dimensional subspace of
polynomial functions. -/
public lemma polynomialFunctionSubspaceDual_mem_span_evaluation
    (G : Variety k) (W : Submodule k G.PolynomialFunction)
    [FiniteDimensional k W] (K : Module.Dual k W) :
    K ∈ Submodule.span k
      (Set.range (polynomialFunctionSubspaceEvaluation G W)) := by
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro f hf
  have hfzero : f = 0 := by
    apply Subtype.ext
    apply Variety.PolynomialFunction.ext
    intro x
    have hx : f ∈ LinearMap.ker
        (polynomialFunctionSubspaceEvaluation G W x) :=
      (Submodule.mem_iInf _).1 hf x
    simpa [polynomialFunctionSubspaceEvaluation,
      Variety.PolynomialFunction.toFun] using LinearMap.mem_ker.mp hx
  rw [hfzero]
  exact LinearMap.map_zero K

/-- Finite coefficients expressing a dual functional as a linear combination
of point evaluations. -/
@[expose]
public noncomputable def polynomialFunctionSubspaceDualCoefficients
    (G : Variety k) (W : Submodule k G.PolynomialFunction)
    [FiniteDimensional k W] (K : Module.Dual k W) :
    Variety.Point G →₀ k :=
  Classical.choose (Finsupp.mem_span_range_iff_exists_finsupp.mp
    (polynomialFunctionSubspaceDual_mem_span_evaluation G W K))

/-- The chosen coefficients represent the original dual functional. -/
public lemma polynomialFunctionSubspaceDualCoefficients_spec
    (G : Variety k) (W : Submodule k G.PolynomialFunction)
    [FiniteDimensional k W] (K : Module.Dual k W) :
    (polynomialFunctionSubspaceDualCoefficients G W K).sum
        (fun x a => a • polynomialFunctionSubspaceEvaluation G W x) = K :=
  Classical.choose_spec (Finsupp.mem_span_range_iff_exists_finsupp.mp
    (polynomialFunctionSubspaceDual_mem_span_evaluation G W K))

end

/-! Regular matrix coefficients of the closed-subgroup right-translation representation. -/

section

variable {k : Type u} [Field k]

/-- A fixed basis of the finite-dimensional generator orbit span. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingSpanBasis
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G) :
    Module.Basis (Fin (Module.finrank k H.rightTranslateVanishingSpan)) k
      H.rightTranslateVanishingSpan :=
  Module.finBasis k H.rightTranslateVanishingSpan

/-- A regular function giving a basis matrix coefficient of the restricted
right-translation representation. -/
@[expose]
public noncomputable def ClosedSubgroup.rightTranslateVanishingMatrixCoefficient
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (e : Module.Basis (Fin (Module.finrank k H.rightTranslateVanishingSpan)) k
      H.rightTranslateVanishingSpan)
    (i j : Fin (Module.finrank k H.rightTranslateVanishingSpan)) :
    G.PolynomialFunction :=
  (polynomialFunctionSubspaceDualCoefficients G
    H.rightTranslateVanishingSpan (e.coord i)).sum fun x a =>
      a • Variety.PolynomialFunction.pullback
        (AlgebraicGroup.leftMulMorphism G x) (e j).val

/-- Evaluation of a matrix-coefficient function is the corresponding basis
coordinate of restricted right translation. -/
public lemma ClosedSubgroup.rightTranslateVanishingMatrixCoefficient_apply
    {G : Variety k} [AlgebraicGroup G] (H : ClosedSubgroup G)
    (e : Module.Basis (Fin (Module.finrank k H.rightTranslateVanishingSpan)) k
      H.rightTranslateVanishingSpan)
    (i j : Fin (Module.finrank k H.rightTranslateVanishingSpan))
    (g : Variety.Point G) :
    H.rightTranslateVanishingMatrixCoefficient e i j g =
      e.repr (H.rightTranslateVanishingSpanLinearMap g (e j)) i := by
  let c := polynomialFunctionSubspaceDualCoefficients G
    H.rightTranslateVanishingSpan (e.coord i)
  have hc := congrArg
    (fun L : Module.Dual k H.rightTranslateVanishingSpan =>
      L (H.rightTranslateVanishingSpanLinearMap g (e j)))
    (polynomialFunctionSubspaceDualCoefficients_spec G
      H.rightTranslateVanishingSpan (e.coord i))
  change
    ((c.sum fun x a => a • polynomialFunctionSubspaceEvaluation G
      H.rightTranslateVanishingSpan x)
      (H.rightTranslateVanishingSpanLinearMap g (e j))) =
      e.repr (H.rightTranslateVanishingSpanLinearMap g (e j)) i at hc
  rw [← hc]
  change
    polynomialFunctionEvalAddHom G g
        (c.sum fun x a => a • Variety.PolynomialFunction.pullback
          (AlgebraicGroup.leftMulMorphism G x) (e j).val) =
      (LinearMap.applyₗ (R := k)
        (M := H.rightTranslateVanishingSpan) (M₂ := k)
        (H.rightTranslateVanishingSpanLinearMap g (e j)))
        (c.sum fun x a => a • polynomialFunctionSubspaceEvaluation G
          H.rightTranslateVanishingSpan x)
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro x hx
  simp only [Variety.PolynomialFunction.pullback,
    AlgebraicGroup.leftMulMorphism_apply,
    polynomialFunctionSubspaceEvaluation,
    ClosedSubgroup.rightTranslateVanishingSpanLinearMap]
  rw [polynomialFunctionEvalAddHom_apply]
  simp only [polynomialFunction_smul_apply]
  rw [map_smul]
  rw [LinearMap.applyₗ_apply_apply]
  simp only [LinearMap.restrict_apply, smul_eq_mul]
  congr 1

end

end Theory.AlgebraicGroup
