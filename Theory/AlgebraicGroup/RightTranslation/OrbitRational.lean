module

public import Theory.AlgebraicGroup.RightTranslation.Orbit
import all Theory.AlgebraicGroup.RightTranslation.Orbit
public import Theory.AlgebraicGroup.Representations.Matrix

/-!
# Rationality of a regular function's translation orbit

The right translates of one regular function span a finite-dimensional space.
Point evaluations span its dual, so every matrix coefficient of the translation
action is a finite linear combination of left translates of regular functions.
The same construction after inversion supplies the inverse matrix coefficients.

`Orbit` is imported internally as well to prove the pointwise formula of its
existing action, whose implementation is not exposed. The public formula below
lets subsequent modules use ordinary imports.

This is the coordinate-ring construction underlying the rational modules used
in GLS3, Section 1.14. It supplies rationality, not the existence of a regular
function of any prescribed highest weight.
-/

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]
variable (G : Variety k) [AlgebraicGroup G] (f : G.PolynomialFunction)

/-- The actual action by right translations on the finite orbit span of `f`. -/
@[expose] public noncomputable def rightTranslateOrbitRationalRepresentation :
    RationalRepresentation G (rightTranslateOrbitSpan G f) :=
  ⟨(rightTranslateOrbitRepresentation G f).asGroupHom⟩

omit [IsAlgClosed k] in
/-- The constructed action has the usual right-translation formula. -/
public theorem rightTranslateOrbitRationalRepresentation_apply
    (g : Variety.Point G) (q : rightTranslateOrbitSpan G f) (x : Variety.Point G) :
    (((rightTranslateOrbitRationalRepresentation G f).action g).1 q).val x =
      q.val (x * g) := by rfl

private noncomputable def orbitMatrixCoefficient
    (e : Module.Basis (Fin (Module.finrank k (rightTranslateOrbitSpan G f))) k
      (rightTranslateOrbitSpan G f))
    (i j : Fin (Module.finrank k (rightTranslateOrbitSpan G f))) :
    G.PolynomialFunction :=
  (polynomialFunctionSubspaceDualCoefficients G
    (rightTranslateOrbitSpan G f) (e.coord i)).sum fun x a =>
      a • Variety.PolynomialFunction.pullback (leftMulMorphism G x) (e j).val

omit [IsAlgClosed k] in
private theorem orbitMatrixCoefficient_apply
    (e : Module.Basis (Fin (Module.finrank k (rightTranslateOrbitSpan G f))) k
      (rightTranslateOrbitSpan G f))
    (i j : Fin (Module.finrank k (rightTranslateOrbitSpan G f)))
    (g : Variety.Point G) :
    orbitMatrixCoefficient G f e i j g =
      e.repr (((rightTranslateOrbitRationalRepresentation G f).action g).1 (e j)) i := by
  let c := polynomialFunctionSubspaceDualCoefficients G
    (rightTranslateOrbitSpan G f) (e.coord i)
  let q := ((rightTranslateOrbitRationalRepresentation G f).action g).1 (e j)
  have hc := congrArg (fun L : Module.Dual k (rightTranslateOrbitSpan G f) => L q)
    (polynomialFunctionSubspaceDualCoefficients_spec G
      (rightTranslateOrbitSpan G f) (e.coord i))
  change (c.sum fun x a => a • polynomialFunctionSubspaceEvaluation G
    (rightTranslateOrbitSpan G f) x) q = e.repr q i at hc
  rw [← hc]
  change polynomialFunctionEvalAddHom G g
      (c.sum fun x a => a • Variety.PolynomialFunction.pullback
        (leftMulMorphism G x) (e j).val) =
    (LinearMap.applyₗ (R := k) (M := rightTranslateOrbitSpan G f) (M₂ := k) q)
      (c.sum fun x a => a • polynomialFunctionSubspaceEvaluation G
        (rightTranslateOrbitSpan G f) x)
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro x _
  simp only [Variety.PolynomialFunction.pullback, leftMulMorphism_apply,
    polynomialFunctionSubspaceEvaluation]
  rw [polynomialFunctionEvalAddHom_apply]
  simp only [polynomialFunction_smul_apply]
  rw [map_smul, LinearMap.applyₗ_apply_apply]
  rfl

/-- Right translation on a regular function's finite orbit span is rational. -/
public theorem rightTranslateOrbitRationalRepresentation_isRational :
    IsRationalRepresentation (rightTranslateOrbitRationalRepresentation G f) := by
  let ρ := rightTranslateOrbitRationalRepresentation G f
  let e := Module.finBasis k (rightTranslateOrbitSpan G f)
  let c := orbitMatrixCoefficient G f e
  let cInv := fun i j => Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism G)
    (c i j)
  have hc : ∀ i j g, c i j g = e.repr ((ρ.action g).1 (e j)) i :=
    orbitMatrixCoefficient_apply G f e
  have hcInv : ∀ i j g, cInv i j g = e.repr (((ρ.action g)⁻¹).1 (e j)) i := by
    intro i j g
    change c i j g⁻¹ = _
    rw [hc, map_inv]
  let φ := generalLinearRepresentationMorphismOfInverseMatrixCoefficient e ρ.action
    c cInv hc hcInv
  refine ⟨e, φ, ?_⟩
  intro g
  exact glPointEquivOf_generalLinearRepresentationPoint e (ρ.action g)

end Theory.AlgebraicGroup
