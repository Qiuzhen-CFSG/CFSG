module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Triangular
public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor.BasicDensity.NegativeCyclicity.SpanInvariance.Cartan.Differential
import all Theory.AlgebraicGroup.RootSubgroups.Tangent
import all Theory.AlgebraicGroup.Instance.GL

/-!
# Faithful tangent transfer for the actual root coefficients

The differential of the rational representation sends the tangent of each
actual root morphism to its canonical first coefficient. Differentiating the
closed matrix inclusion is injective, and sends the same tangent to the
specialized integral root matrix. Thus matrix Lie relations lift to the carrier
and then pass to every rational factor, in arbitrary characteristic.

The private imports expose the polynomial description of the additive tangent
and the agreement of the two general-linear presentations only inside these
proofs; their public boundaries are preserved.

Source: Steinberg, *Representations of Algebraic Groups* (1963), §§2, 4,
DOI 10.1017/S0027763000011016.
-/

public section

set_option backward.isDefEq.respectTransparency false

open Theory.AlgebraicGroup Theory.AlgebraicGroup.StandardRootSystem
namespace ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
namespace NegativeCyclicity.SpanInvariance.CartanTransfer
attribute [local instance] LieRing.ofAssociativeRing
noncomputable section
universe u
variable {F : Type u} [Field F] [IsAlgClosed F]

/-- Evaluating a general-linear matrix coordinate gives the corresponding
chosen-basis coefficient of the represented automorphism. -/
private theorem matrixCoordinate_eq_basis_coord
    {V : Type*} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (b : Module.Basis (Fin (Module.finrank F V)) F V)
    (x : Variety.Point (glVarietyOf F V))
    (i j : Fin (Module.finrank F V)) :
    Bor1.generalLinearMatrixCoordinateOf V i j x =
      b.coord i (((glPointEquivOf F V b x :
        LinearMap.GeneralLinearGroup F V) : Module.End F V) (b j)) := by
  change generalLinearMatrixCoordinate (Module.finrank F V) i j x = _
  rw [generalLinearMatrixCoordinate_apply]
  change glMatrixOfPoint (Module.finrank F V) x i j = _
  have hb := glPointEquivOf_apply_basis V b x j
  have hc := congrArg (b.coord i) hb
  rw [Module.Basis.coord_equivFun_symm] at hc
  exact hc.symm


/-- The tangent vector of the actual root morphism at zero. -/
def rootTangent (r : F4Chevalley.Root) : IdentityPointDerivation (F4Chevalley.Carrier (k := F)) :=
  identityTangentMorphismLinearMap (F4Chevalley.rootMorphism r) kPlusIdentityDerivation

/-- The canonical coefficient operators arise from a Lie homomorphism in every characteristic. -/
theorem exists_coefficient_lieHom {B : AlgebraicFactor F} (p : RootExpansion B.action) :
    ∃ d : IdentityPointDerivation (F4Chevalley.Carrier (k := F)) →ₗ⁅F⁆ Module.End F B.Space,
      ∀ r : F4Chevalley.Root, d (rootTangent r) = p.coeff r 1 := by
  obtain ⟨b, f, hf⟩ := B.irreducible.1
  let d := (Bor1.ReeF4CartanDifferential.generalLinearIdentityTangentLieHom b).comp
    (identityTangentMorphismLieHom f)
  refine ⟨d, fun r => ?_⟩
  rw [p.coeff_one_eq_rootOperator]
  apply LinearMap.ext_on b.span_eq
  rintro _ ⟨j, rfl⟩
  apply b.ext_elem
  intro i
  change b.coord i (Bor1.generalLinearIdentityTangentLinearMap b
      (identityTangentMorphismLinearMap f (rootTangent r)) (b j)) =
    b.coord i (EndNode.Multiplicity.rootOperator B r (b j))
  rw [Bor1.ReeF4CartanDifferential.generalLinearIdentityTangentLinearMap_apply_basis_coord,
    EndNode.Multiplicity.dual_rootOperator]
  let q := (F4Chevalley.rootMorphism (k := F) r).toVariety.pullbackAlgHom
    (f.toVariety.pullbackAlgHom (Bor1.generalLinearMatrixCoordinateOf B.Space i j))
  change kPlusIdentityDerivation q = _
  have hp : kPlusPolynomialFunctionAlgEquiv q =
      EndNode.Multiplicity.rootPolynomial B r (b.coord i) (b j) := by
    apply Polynomial.funext
    intro t
    rw [kPlusPolynomialFunctionAlgEquiv_eval, EndNode.Multiplicity.rootPolynomial_eval]
    change Bor1.generalLinearMatrixCoordinateOf B.Space i j
      (f.onPoints (algebraicRootElement r t)) = _
    rw [matrixCoordinate_eq_basis_coord b, hf]
  rw [kPlusIdentityDerivation_apply, hp, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
  simp


open RootPairing.IntegralGeckConstruction

/-- A scalar polynomial along the actual root curve computes its tangent derivative. -/
theorem rootTangent_apply_of_polynomial (r : F4Chevalley.Root)
    (a : Variety.PolynomialFunction (F4Chevalley.Carrier (k := F))) (q : Polynomial F)
    (hq : ∀ t, q.eval t = a (algebraicRootElement r t)) :
    rootTangent r a = q.coeff 1 := by
  let c := (F4Chevalley.rootMorphism (k := F) r).toVariety.pullbackAlgHom a
  have hc : kPlusPolynomialFunctionAlgEquiv c = q := by
    apply Polynomial.funext
    intro t
    rw [kPlusPolynomialFunctionAlgEquiv_eval, hq]
    rfl
  change kPlusIdentityDerivation c = _
  rw [kPlusIdentityDerivation_apply, hc, ← Polynomial.coeff_zero_eq_eval_zero,
    Polynomial.coeff_derivative]
  simp

/-- The faithful matrix realization differentiated at the identity. -/
def naturalDifferential :
    IdentityPointDerivation (F4Chevalley.Carrier (k := F)) →ₗ⁅F⁆
      Module.End F (F4Chevalley.BasisIndex → F) :=
  (Bor1.ReeF4CartanDifferential.generalLinearIdentityTangentLieHom
    (carrierBasis (P := typeF4RootPairing) (b := typeF4RootPairing_base) (k := F))).comp
    (identityTangentMorphismLieHom (F4Chevalley.ambientClosedCarrier (k := F)).inclusion)

/-- Closed inclusion and general-linear coordinates detect every tangent vector. -/
theorem naturalDifferential_injective : Function.Injective (naturalDifferential (F := F)) :=
  (Bor1.ReeF4CartanDifferential.generalLinearIdentityTangentLinearMap_injective
    (carrierBasis (P := typeF4RootPairing) (b := typeF4RootPairing_base) (k := F))).comp
    (identityTangentMorphismLieHom_inclusion_injective (F4Chevalley.ambientClosedCarrier (k := F)))

/-- The differentiated root morphism is the specialized integral root matrix. -/
theorem naturalDifferential_rootTangent (r : F4Chevalley.Root) :
    naturalDifferential (F := F) (rootTangent (F := F) r) =
      (specializeMatrix (S := F) (F4Chevalley.integralOperators.rootOperator r)).mulVecLin := by
  let b := carrierBasis (P := typeF4RootPairing) (b := typeF4RootPairing_base) (k := F)
  apply LinearMap.ext_on b.span_eq
  rintro _ ⟨j, rfl⟩
  apply b.ext_elem
  intro i
  change b.coord i (Bor1.generalLinearIdentityTangentLinearMap b
      (identityTangentMorphismLinearMap (F4Chevalley.ambientClosedCarrier (k := F)).inclusion
        (rootTangent r)) (b j)) = _
  rw [Bor1.ReeF4CartanDifferential.generalLinearIdentityTangentLinearMap_apply_basis_coord]
  let A (n : ℕ) := specializeMatrix (S := F) (F4Chevalley.integralOperators.rootDividedPower r n)
  let q : Polynomial F := Polynomial.C (b.coord i (b j)) +
    Polynomial.C (b.coord i ((A 1).mulVecLin (b j))) * Polynomial.X +
    Polynomial.C (b.coord i ((A 2).mulVecLin (b j))) * Polynomial.X ^ 2 +
    Polynomial.C (b.coord i ((A 3).mulVecLin (b j))) * Polynomial.X ^ 3
  change rootTangent r
    ((F4Chevalley.ambientClosedCarrier (k := F)).inclusion.toVariety.pullbackAlgHom
      (generalLinearMatrixCoordinate (Module.finrank F (F4Chevalley.BasisIndex → F)) i j)) = _
  rw [rootTangent_apply_of_polynomial r _ q (by
    intro t
    change q.eval t = Bor1.generalLinearMatrixCoordinateOf (F4Chevalley.BasisIndex → F) i j
      ((F4Chevalley.ambientClosedCarrier (k := F)).inclusion.onPoints
        ((F4Chevalley.rootMorphism r).onPoints (kPlusPoint t)))
    rw [F4Chevalley.rootMorphism_inclusion_apply, matrixCoordinate_eq_basis_coord b,
      F4Chevalley.ambientRootMorphism_apply, glPointEquivOf_generalLinearRepresentationPoint]
    change q.eval t = b.coord i
      ((Matrix.GeneralLinearGroup.toLin (F4Chevalley.rootCurve r t) :
        Module.End F (F4Chevalley.BasisIndex → F)) (b j))
    rw [Matrix.GeneralLinearGroup.toLin_apply, Matrix.mulVecLin_apply,
      F4Chevalley.rootCurve_matrix_formula]
    simp only [q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, map_add, map_smul, smul_eq_mul, Matrix.mulVecLin_apply, A]
    ring)]
  simp [q, A, F4Chevalley.dividedPower_one, Module.Basis.coord_apply]

/-- Tangent matrices in the carrier's original Cartan-plus-root basis. -/
def matrixDifferential :
    IdentityPointDerivation (F4Chevalley.Carrier (k := F)) →ₗ⁅F⁆
      Matrix F4Chevalley.BasisIndex F4Chevalley.BasisIndex F :=
  (LinearMap.toMatrixAlgEquiv' (R := F) (n := F4Chevalley.BasisIndex)).toLieEquiv.toLieHom.comp
    (naturalDifferential (F := F))

theorem matrixDifferential_injective : Function.Injective (matrixDifferential (F := F)) :=
  (LinearMap.toMatrixAlgEquiv' (R := F) (n := F4Chevalley.BasisIndex)).injective.comp
    (naturalDifferential_injective (F := F))

@[simp] theorem matrixDifferential_rootTangent (r : F4Chevalley.Root) :
    matrixDifferential (rootTangent (F := F) r) =
      specializeMatrix (S := F) (F4Chevalley.integralOperators.rootOperator r) := by
  change LinearMap.toMatrixAlgEquiv' (naturalDifferential (F := F) (rootTangent r)) = _
  rw [naturalDifferential_rootTangent]
  exact LinearMap.toMatrixAlgEquiv'_toLinAlgEquiv' _

end
end NegativeCyclicity.SpanInvariance.CartanTransfer
end ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.AlgebraicTensor
