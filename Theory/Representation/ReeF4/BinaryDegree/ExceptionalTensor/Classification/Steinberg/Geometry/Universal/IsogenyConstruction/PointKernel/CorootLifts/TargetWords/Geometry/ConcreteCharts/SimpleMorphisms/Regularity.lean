module

public import Theory.Representation.ReeF4.BinaryDegree.ExceptionalTensor.Classification.Steinberg.Geometry.Universal.IsogenyConstruction.PointKernel.CorootLifts.TargetWords.Geometry.ConcreteCharts.SimpleMorphisms.Polynomial
public import Theory.AlgebraicGroup.RootSystems.AlgebraicGroups.F4ChevalleyCorootWords
public import Theory.AlgebraicGroup.Instance.PSL
public import Theory.AlgebraicGroup.CoordinateRing.Point

/-!
# Regularity of the polynomial simple-root SL₂ candidate

An identity and a multiplication law for the explicit polynomial matrix give
an action by invertible matrices. Its entries are polynomial functions on SL₂;
composition with inversion supplies regular inverse entries. This constructs
an ambient algebraic-group morphism without an abstract recognition theorem.
The matrix laws remain explicit inputs to this conditional construction.
-/

public noncomputable section
open Theory.AlgebraicGroup.StandardRootSystem
open RootPairing.IntegralGeckConstruction
namespace Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Polynomial coordinate matrix on SL₂. -/
@[expose] def sl2CoordinateMatrix :
    Matrix (Fin 2) (Fin 2) (slVariety k 2).PolynomialFunction :=
  Matrix.of fun r c => Variety.PolynomialFunction.ofPolynomial _
    (MvPolynomial.X (ULift.up (r, c)))

lemma sl2CoordinateMatrix_eval (x : Variety.Point (slVariety k 2)) :
    (sl2CoordinateMatrix (k := k)).map
      (polynomialFunctionPointAlgHom _ x) = slPointMatrix 2 x := by
  ext r c
  change evalPolynomial x.val (MvPolynomial.X (ULift.up (r, c))) = _
  rw [evalPolynomial_X]
  rfl

/-- Polynomial entries of the rank-one candidate in the actual carrier basis. -/
@[expose] def simpleSL2Coefficient (i : typeF4RootPairing_base.support)
    (r c : Fin (Module.finrank k (BasisIndex → k))) :
    (slVariety k 2).PolynomialFunction :=
  simpleSL2Matrix i sl2CoordinateMatrix
    ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := k)).symm r)
    ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := k)).symm c)

lemma simpleSL2Coefficient_apply (i : typeF4RootPairing_base.support)
    (r c : Fin (Module.finrank k (BasisIndex → k)))
    (x : Variety.Point (slVariety k 2)) :
    simpleSL2Coefficient i r c x =
      simpleSL2Matrix i (slPointMatrix 2 x)
        ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := k)).symm r)
        ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := k)).symm c) := by
  have h := simpleSL2Matrix_map (polynomialFunctionPointAlgHom _ x).toRingHom i
    (sl2CoordinateMatrix (k := k))
  rw [show (sl2CoordinateMatrix (k := k)).map
      (polynomialFunctionPointAlgHom _ x).toRingHom = slPointMatrix 2 x from
    sl2CoordinateMatrix_eval x] at h
  exact (congrArg (fun A => A
    ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := k)).symm r)
    ((carrierIndexEquiv (b := typeF4RootPairing_base) (k := k)).symm c)) h).symm

variable (i : typeF4RootPairing_base.support)
variable (hone : simpleSL2Matrix i (1 : Matrix (Fin 2) (Fin 2) k) = 1)
variable (hmul : ∀ A B : Matrix.SpecialLinearGroup (Fin 2) k,
  simpleSL2Matrix i ((A * B : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
    simpleSL2Matrix i (A : Matrix (Fin 2) (Fin 2) k) *
      simpleSL2Matrix i (B : Matrix (Fin 2) (Fin 2) k))

/-- The explicit matrices become units from the SL₂ multiplication law. -/
@[expose] def simpleSL2Units : Matrix.SpecialLinearGroup (Fin 2) k →*
    (Matrix BasisIndex BasisIndex k)ˣ where
  toFun A := {
    val := simpleSL2Matrix i (↑A)
    inv := simpleSL2Matrix i (↑A⁻¹)
    val_inv := by rw [← hmul, mul_inv_cancel]; exact hone
    inv_val := by rw [← hmul, inv_mul_cancel]; exact hone }
  map_one' := Units.ext hone
  map_mul' A B := Units.ext (hmul A B)

private def simpleSL2LinearRepresentation :
    Variety.Point (slVariety k 2) →* LinearMap.GeneralLinearGroup k (BasisIndex → k) :=
  Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
    ((simpleSL2Units i hone hmul).comp (slPointMulEquiv 2).toMonoidHom)

private lemma simpleSL2LinearRepresentation_coefficient
    (r c : Fin (Module.finrank k (BasisIndex → k)))
    (x : Variety.Point (slVariety k 2)) :
    simpleSL2Coefficient i r c x =
      (carrierBasis (b := typeF4RootPairing_base) (k := k)).repr
        ((simpleSL2LinearRepresentation i hone hmul x : Module.End k (BasisIndex → k))
          ((carrierBasis (b := typeF4RootPairing_base) (k := k)) c)) r := by
  rw [simpleSL2Coefficient_apply]
  simp [carrierBasis, simpleSL2LinearRepresentation, Module.Basis.reindex_apply]
  rfl

private def simpleSL2InverseCoefficient
    (r c : Fin (Module.finrank k (BasisIndex → k))) :
    (slVariety k 2).PolynomialFunction :=
  Variety.PolynomialFunction.pullback (invMorphism (slVariety k 2))
    (simpleSL2Coefficient i r c)

private lemma simpleSL2LinearRepresentation_inverseCoefficient
    (r c : Fin (Module.finrank k (BasisIndex → k)))
    (x : Variety.Point (slVariety k 2)) :
    simpleSL2InverseCoefficient i r c x =
      (carrierBasis (b := typeF4RootPairing_base) (k := k)).repr
        ((((simpleSL2LinearRepresentation i hone hmul x)⁻¹ :
          LinearMap.GeneralLinearGroup k (BasisIndex → k)) : Module.End k (BasisIndex → k))
          ((carrierBasis (b := typeF4RootPairing_base) (k := k)) c)) r := by
  change simpleSL2Coefficient i r c x⁻¹ = _
  rw [simpleSL2LinearRepresentation_coefficient i hone hmul, map_inv]

/-- The polynomial candidate gives a regular ambient map once its matrix laws hold. -/
def simpleSL2AmbientMorphism : Morphism (slVariety k 2) (Ambient k) :=
  generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    (carrierBasis (b := typeF4RootPairing_base) (k := k))
    (simpleSL2LinearRepresentation i hone hmul)
    (simpleSL2Coefficient i) (simpleSL2InverseCoefficient i)
    (simpleSL2LinearRepresentation_coefficient i hone hmul)
    (simpleSL2LinearRepresentation_inverseCoefficient i hone hmul)

lemma simpleSL2AmbientMorphism_apply (x : Variety.Point (slVariety k 2)) :
    (simpleSL2AmbientMorphism i hone hmul).onPoints x =
      matrixToAmbient (simpleSL2Units i hone hmul (slPointEquiv 2 x)) := by
  change matrixToAmbient (simpleSL2Units i hone hmul (slPointMulEquiv 2 x)) = _
  rw [slPointMulEquiv_apply]

end Theory.AlgebraicGroup.F4Chevalley.ConcreteCharts
