module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.Frobenius
public import Theory.AlgebraicGroup.Variety.AffineDuality

/-!
# Polynomial roots of the Spin Frobenius coordinates

Every coordinate of the `n`th regular Frobenius on the concrete Spin carrier
is a `2 ^ n`th power of a polynomial function, over every algebraically closed
field of characteristic two. The carrier's Clifford basis is arbitrary.

In that basis the semilinear Clifford map gives each output matrix entry as
a sum of constant coefficients times `2 ^ n`th powers of input coefficients.
Extracting roots of those constants gives the required polynomial functions.
Apply the same construction after group inversion and take a determinant to
handle the inverse-determinant coordinate of the general-linear embedding.

This is the coefficient compatibility required to reverse an incoming
bijective isogeny after Frobenius. Sources: GLS3, Chapter 1, §§1.10–1.12 and
1.15 (`refs/KGroup/GLS3/Chapter1.tex`); the concrete semilinear construction is
`SimplyConnectedModel/Frobenius/RegularLift/CliffordFunctor.lean`.
-/

public section
open Theory.AlgebraicGroup CliffordAlgebra
open scoped BigOperators
noncomputable section
universe u
namespace Triality.SimplyConnected.ReverseIsogeny
open RegularLift
variable (k : Type u) [Field k] [IsAlgClosed k]

private abbrev C := CliffordAlgebra (quadraticForm k)
private instance : Module.Finite k (C k) := (standardHyperbolicSplit 4).moduleFinite
private abbrev basis := (cliffordModel k).cliffordBasis
private abbrev Index := Fin (Module.finrank k (C k))

private def leftRepresentation : RationalRepresentation (groupVariety k) (C k) :=
  ⟨(LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).symm.toMonoidHom.comp
    ((Units.mulLeftLinearEquiv k (C k)).comp
      (spinGroup.toUnits.comp (pointEquiv k).toMonoidHom))⟩

private theorem leftRepresentation_apply (g : Points k) (x : C k) :
    ((leftRepresentation k).action g : Module.End k (C k)) x =
      (pointEquiv k g : C k) * x := rfl

private theorem inclusion_representation (g : Points k) :
    glPointEquivOf k (C k) (basis k) ((cliffordModel k).spin.inclusion.onPoints g) =
      (leftRepresentation k).action g := by
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).injective
  change _ = (LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).symm _)
  rw [MulEquiv.apply_symm_apply]
  exact (cliffordModel k).spinLinear_points g

private theorem inclusion_eq (g : Points k) :
    (cliffordModel k).spin.inclusion.onPoints g =
      generalLinearRepresentationPoint (basis k) ((leftRepresentation k).action g) := by
  apply (glPointEquivOf k (C k) (basis k)).injective
  rw [inclusion_representation, glPointEquivOf_generalLinearRepresentationPoint]

private def valueCoefficient (i : Index k) : (groupVariety k).PolynomialFunction :=
  rationalRepresentationLinearMatrixCoefficient (leftRepresentation k) (basis k)
    (cliffordModel k).spin.inclusion ((basis k).coord i) 1

private theorem valueCoefficient_apply (i : Index k) (g : Points k) :
    valueCoefficient k i g = (basis k).repr (pointEquiv k g : C k) i := by
  rw [valueCoefficient, rationalRepresentationLinearMatrixCoefficient_apply _ _ _
    (inclusion_representation k), leftRepresentation_apply, mul_one]
  rfl

variable [CharP k 2]

private theorem frobenius_clifford (n : ℕ) (g : Points k) :
    (pointEquiv k ((regularFrobeniusLift k n).onPoints g) : C k) =
      cliffordMap 4 (iterateFrobeniusEquiv k 2 n) (pointEquiv k g) := by
  have h := DFunLike.congr_fun (pointHom_frobenius k n) g
  change pointHom k (iterateFrobeniusEquiv k 2 n) g = frobeniusPointAut k n g at h
  rw [regularFrobeniusLift_onPoints, ← h, pointEquiv_pointHom, spinMap_coe]

private def rootMatrixCoefficient (n : ℕ) (i j : Index k) :
    (groupVariety k).PolynomialFunction :=
  ∑ l, algebraMap k (groupVariety k).PolynomialFunction
      ((iterateFrobeniusEquiv k 2 n).symm
        ((basis k).repr (cliffordMap 4 (iterateFrobeniusEquiv k 2 n) (basis k l) *
          basis k j) i)) * valueCoefficient k l

private theorem rootMatrixCoefficient_pow (n : ℕ) (i j : Index k) (g : Points k) :
    (rootMatrixCoefficient k n i j g) ^ (2 ^ n) =
      (basis k).repr (((leftRepresentation k).action
        ((regularFrobeniusLift k n).onPoints g) : Module.End k (C k)) (basis k j)) i := by
  rw [leftRepresentation_apply, frobenius_clifford, cliffordMap_mul_repr]
  change (iterateFrobeniusEquiv k 2 n)
    (Variety.PolynomialFunction.evalAlgHom (groupVariety k) g
      (∑ l, algebraMap k (groupVariety k).PolynomialFunction
        ((iterateFrobeniusEquiv k 2 n).symm
          ((basis k).repr (cliffordMap 4 (iterateFrobeniusEquiv k 2 n) (basis k l) *
            basis k j) i)) * valueCoefficient k l)) = _
  rw [map_sum, map_sum]
  simp only [map_mul, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply,
    RingEquiv.apply_symm_apply]
  simp only [show ∀ l, Variety.PolynomialFunction.evalAlgHom (groupVariety k) g
    (valueCoefficient k l) = (basis k).repr (pointEquiv k g : C k) l from
      fun l => valueCoefficient_apply k l g]
  apply Finset.sum_congr rfl
  intro l _
  exact mul_comm _ _

/-- Frobenius coordinates have polynomial roots even in the arbitrary Clifford basis. -/
theorem regularFrobeniusLift_coordinate_roots (n : ℕ) :
    ∀ i : (groupVariety k).Coordinates, ∃ f : (groupVariety k).PolynomialFunction,
      ∀ g, ((regularFrobeniusLift k n).onPoints g).val i = (f g) ^ (2 ^ n) := by
  classical
  intro c
  change Sum (Index k × Index k) PUnit at c
  cases c with
  | inl ij =>
    obtain ⟨i, j⟩ := ij
    refine ⟨rootMatrixCoefficient k n i j, fun g => ?_⟩
    change ((cliffordModel k).spin.inclusion.onPoints
      ((regularFrobeniusLift k n).onPoints g)).val (Sum.inl (i, j)) = _
    rw [inclusion_eq, generalLinearRepresentationPoint_matrix]
    exact (rootMatrixCoefficient_pow k n i j g).symm
  | inr c =>
    cases c
    let M : Matrix (Index k) (Index k) (groupVariety k).PolynomialFunction :=
      fun i j => Variety.PolynomialFunction.pullback
        (Theory.AlgebraicGroup.invMorphism (groupVariety k)) (rootMatrixCoefficient k n i j)
    refine ⟨M.det, fun g => ?_⟩
    change ((cliffordModel k).spin.inclusion.onPoints
      ((regularFrobeniusLift k n).onPoints g)).val (Sum.inr PUnit.unit) = _
    rw [inclusion_eq, generalLinearRepresentationPoint_scalar]
    symm
    let ev : (groupVariety k).PolynomialFunction →+* k :=
      (iterateFrobeniusEquiv k 2 n).toRingHom.comp
        (Variety.PolynomialFunction.evalAlgHom (groupVariety k) g).toRingHom
    change ev M.det = _
    rw [RingHom.map_det]
    calc
      _ = (LinearMap.toMatrix (basis k) (basis k)
          ((((leftRepresentation k).action ((regularFrobeniusLift k n).onPoints g))⁻¹ :
            LinearMap.GeneralLinearGroup k (C k)) : Module.End k (C k))).det := by
        congr 1
        ext i j
        change (rootMatrixCoefficient k n i j g⁻¹) ^ (2 ^ n) = _
        rw [rootMatrixCoefficient_pow, map_inv, map_inv, LinearMap.toMatrix_apply]
      _ = _ := generalLinear_toMatrix_inv_det (basis k) _

end Triality.SimplyConnected.ReverseIsogeny
