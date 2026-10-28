module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Frobenius.PointAction
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Frobenius.RegularLift.CliffordFunctor
public import Theory.AlgebraicGroup.Variety.AffineDuality

/-!
# Regular Frobenius on the concrete Clifford Spin variety

For every nonnegative exponent, including zero and one, coordinate Frobenius
on the standard eight-dimensional hyperbolic space lifts to a regular group
endomorphism of the exact closed left-regular Spin carrier.

The semilinear Clifford construction in `CliffordFunctor` preserves the genuine
Spin group. Its value on a Clifford element with coefficients `a_l` in the
carrier's chosen basis is the sum of `a_l^(2^n)` times the images of those basis
vectors. Evaluation of the regular left-regular representation at `1` supplies
the input coefficient polynomials. Multiplication by each fixed basis vector
then gives all output matrix coefficients. Composing with group inversion gives
the inverse matrix coefficients, so the general-linear morphism is regular.
Its image lies in the exact Spin carrier, permitting codomain restriction.

Clifford conjugation identifies this morphism's point map with
`frobeniusPointAut`. The argument does not assume that the chosen Clifford basis
is defined over the prime field, or that the inverse of the Spin-to-Omega point
bijection is regular.

Source: the nonnegative-exponent regularity in GLS3, Theorem 1.15.4(a), and the
ordinary Frobenius construction in §§2.1–2.2. This module supplies the concrete
regular lift; the root pinning and later Steinberg packaging are separate.
-/

public section

open Theory.AlgebraicGroup CliffordAlgebra
open scoped BigOperators
noncomputable section
universe u
namespace Triality.SimplyConnected.RegularLift
variable (k : Type u) [Field k] [IsAlgClosed k]

private abbrev C := CliffordAlgebra (quadraticForm k)
private instance : Module.Finite k (C k) := (standardHyperbolicSplit 4).moduleFinite
private abbrev basis := (cliffordModel k).cliffordBasis

private def carrierRepresentation : RationalRepresentation (groupVariety k) (C k) :=
  ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).symm.toMonoidHom.comp
    ((Units.mulLeftLinearEquiv k (C k)).comp
      (spinGroup.toUnits.comp (pointEquiv k).toMonoidHom))⟩

private theorem carrierRepresentation_apply (g : Points k) (x : C k) :
    ((carrierRepresentation k).action g : Module.End k (C k)) x =
      (pointEquiv k g : C k) * x := rfl

private theorem inclusion_representation (g : Points k) :
    glPointEquivOf k (C k) (basis k) ((cliffordModel k).spin.inclusion.onPoints g) =
      (carrierRepresentation k).action g := by
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).injective
  change _ = (LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).symm _)
  rw [MulEquiv.apply_symm_apply]
  exact (cliffordModel k).spinLinear_points g

private def valueCoefficient (i : Fin (Module.finrank k (C k))) :
    (groupVariety k).PolynomialFunction :=
  rationalRepresentationLinearMatrixCoefficient (carrierRepresentation k) (basis k)
    (cliffordModel k).spin.inclusion ((basis k).coord i) 1

private theorem valueCoefficient_apply (i : Fin (Module.finrank k (C k))) (g : Points k) :
    valueCoefficient k i g = (basis k).repr (pointEquiv k g : C k) i := by
  rw [valueCoefficient, rationalRepresentationLinearMatrixCoefficient_apply _ _ _
    (inclusion_representation k), carrierRepresentation_apply, mul_one]
  rfl

variable [CharP k 2]

private def mappedRepresentation (n : ℕ) : Points k →* LinearMap.GeneralLinearGroup k (C k) :=
  (carrierRepresentation k).action.comp (pointHom k (iterateFrobeniusEquiv k 2 n))

private theorem mappedRepresentation_apply (n : ℕ) (g : Points k) (x : C k) :
    (mappedRepresentation k n g : Module.End k (C k)) x =
      cliffordMap 4 (iterateFrobeniusEquiv k 2 n) (pointEquiv k g) * x := by
  change ((carrierRepresentation k).action
    (pointHom k (iterateFrobeniusEquiv k 2 n) g) : Module.End k (C k)) x = _
  rw [carrierRepresentation_apply, pointEquiv_pointHom, spinMap_coe]

private def matrixCoefficient (n : ℕ) (i j : Fin (Module.finrank k (C k))) :
    (groupVariety k).PolynomialFunction :=
  ∑ l, algebraMap k (groupVariety k).PolynomialFunction
      ((basis k).repr (cliffordMap 4 (iterateFrobeniusEquiv k 2 n) (basis k l) *
        basis k j) i) * valueCoefficient k l ^ (2 ^ n)

private theorem matrixCoefficient_apply (n : ℕ) (i j : Fin (Module.finrank k (C k)))
    (g : Points k) :
    matrixCoefficient k n i j g =
      (basis k).repr ((mappedRepresentation k n g : Module.End k (C k)) (basis k j)) i := by
  rw [mappedRepresentation_apply, cliffordMap_mul_repr]
  change Variety.PolynomialFunction.evalAlgHom (groupVariety k) g
    (∑ l, algebraMap k (groupVariety k).PolynomialFunction
      ((basis k).repr (cliffordMap 4 (iterateFrobeniusEquiv k 2 n) (basis k l) *
        basis k j) i) * valueCoefficient k l ^ (2 ^ n)) = _
  rw [map_sum]
  simp only [map_mul, map_pow, AlgHom.commutes]
  change (∑ l, (basis k).repr
      (cliffordMap 4 (iterateFrobeniusEquiv k 2 n) (basis k l) * basis k j) i *
        (valueCoefficient k l g) ^ (2 ^ n)) = _
  simp only [valueCoefficient_apply]
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

private def inverseMatrixCoefficient (n : ℕ) (i j : Fin (Module.finrank k (C k))) :
    (groupVariety k).PolynomialFunction :=
  Variety.PolynomialFunction.pullback (Theory.AlgebraicGroup.invMorphism (groupVariety k))
    (matrixCoefficient k n i j)

private theorem inverseMatrixCoefficient_apply (n : ℕ)
    (i j : Fin (Module.finrank k (C k))) (g : Points k) :
    inverseMatrixCoefficient k n i j g =
      (basis k).repr ((((mappedRepresentation k n g)⁻¹ : LinearMap.GeneralLinearGroup k (C k)) :
        Module.End k (C k)) (basis k j)) i := by
  change matrixCoefficient k n i j g⁻¹ = _
  rw [matrixCoefficient_apply, map_inv]

private def ambientMorphism (n : ℕ) :
    Theory.AlgebraicGroup.Morphism (groupVariety k) (glVarietyOf k (C k)) :=
  generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    (basis k) (mappedRepresentation k n) (matrixCoefficient k n)
    (inverseMatrixCoefficient k n) (matrixCoefficient_apply k n)
    (inverseMatrixCoefficient_apply k n)

private theorem ambientMorphism_apply (n : ℕ) (g : Points k) :
    (ambientMorphism k n).onPoints g =
      (cliffordModel k).spin.inclusion.onPoints (pointHom k (iterateFrobeniusEquiv k 2 n) g) := by
  apply (glPointEquivOf k (C k) (basis k)).injective
  change glPointEquivOf k (C k) (basis k)
      (generalLinearRepresentationPoint (basis k) (mappedRepresentation k n g)) = _
  rw [glPointEquivOf_generalLinearRepresentationPoint, inclusion_representation]
  rfl

private theorem ambientMorphism_mem (n : ℕ) (g : Points k) :
    (ambientMorphism k n).onPoints g ∈ (cliffordModel k).spin.toSubgroup := by
  rw [ambientMorphism_apply]
  exact ((cliffordModel k).spin.pointEquiv _).property

end RegularLift

open RegularLift

variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

/-- Ordinary Frobenius as a regular endomorphism of the exact Clifford Spin variety. -/
def regularFrobeniusLift (n : ℕ) :
    Theory.AlgebraicGroup.Morphism (groupVariety k) (groupVariety k) :=
  (ambientMorphism k n).codRestrictClosedSubgroup (cliffordModel k).spin (ambientMorphism_mem k n)

/-- The regular lift realizes the prescribed coordinate Frobenius point automorphism. -/
@[simp] theorem regularFrobeniusLift_onPoints (n : ℕ) (g : Points k) :
    (regularFrobeniusLift k n).onPoints g = frobeniusPointAut k n g := by
  apply (cliffordModel k).spin.inclusion_injective
  rw [regularFrobeniusLift, Theory.AlgebraicGroup.Morphism.codRestrictClosedSubgroup_inclusion_apply,
    ambientMorphism_apply, pointHom_frobenius]
  rfl

end Triality.SimplyConnected
