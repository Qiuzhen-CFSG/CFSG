module
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.TorusCoordinates
public import Theory.AlgebraicGroup.Representations.Matrix
import all Theory.AlgebraicGroup.RootSubgroups.Tangent

/-!
# Polynomial coefficients of the natural Spin action

The regular Spin cover, followed by the ordinary linear inclusion, supplies
regular matrix coefficients in the standard hyperbolic basis. Pullback along
an additive curve gives genuine univariate polynomials. Their evaluation,
identity values, and isotropic-column identities are proved here.

Only the polynomial-function equivalence from `RootSubgroups.Tangent` is used
through its private import; no tangent-space assertion enters these proofs.
Source: GLS3 §§1.9, 1.10 and 1.14 (`refs/KGroup/GLS3/Chapter1.tex`).
-/

public section
open Theory Theory.AlgebraicGroup
noncomputable section
namespace Triality.SimplyConnected.Pinning.NaturalCoefficients
universe u
variable (k : Type u) [Field k] [IsAlgClosed k]
/-- The eight standard hyperbolic coordinates. -/
abbrev Index := Fin 4 ⊕ Fin 4
/-- The basis with the first and second coordinates of each hyperbolic pair. -/
@[expose] def basis : Module.Basis Index k (QuadraticSpace k) :=
  (Pi.basisFun k (Fin 4)).prod (Pi.basisFun k (Fin 4))
private def linearMorphism : AlgebraicGroup.Morphism (groupVariety k)
    (glVarietyOf k (QuadraticSpace k)) :=
  (cliffordModel k).omega.inclusion.comp (cliffordModel k).spinCover

private def representation : RationalRepresentation (groupVariety k) (QuadraticSpace k) where
  action := (LinearMap.GeneralLinearGroup.generalLinearEquiv k (QuadraticSpace k)).symm.toMonoidHom.comp
    ((quadraticIsometrySubgroup (quadraticForm k)).subtype.comp (naturalAction k))

private lemma linearMorphism_points (g : Points k) :
    glPointEquivOf k (QuadraticSpace k) (cliffordModel k).basis
      ((linearMorphism k).onPoints g) = (representation k).action g := by
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (QuadraticSpace k)).injective
  change LinearMap.GeneralLinearGroup.generalLinearEquiv k (QuadraticSpace k)
      (glPointEquivOf k (QuadraticSpace k) (cliffordModel k).basis
        ((cliffordModel k).omega.inclusion.onPoints ((cliffordModel k).spinCover.onPoints g))) = _
  rw [(cliffordModel k).omegaLinear_points]
  simp only [representation, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.apply_symm_apply]
  rfl

private def coordinate (p q : Index) : (groupVariety k).PolynomialFunction :=
  rationalRepresentationLinearMatrixCoefficient (representation k) (cliffordModel k).basis
    (linearMorphism k) ((basis k).coord p) (basis k q)

private lemma coordinate_apply (p q : Index) (g : Points k) :
    coordinate k p q g = (basis k).coord p ((naturalAction k g).1 (basis k q)) := by
  rw [coordinate, rationalRepresentationLinearMatrixCoefficient_apply
    (representation k) (cliffordModel k).basis (linearMorphism k) (linearMorphism_points k)]
  rfl

/-- A genuine polynomial coefficient of a regular additive curve in Spin. -/
def polynomial (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (p q : Index) : Polynomial k :=
  kPlusPolynomialFunctionAlgEquiv (f.toVariety.pullbackAlgHom (coordinate k p q))
lemma polynomial_eval (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (p q : Index) (a : k) :
    (polynomial k f p q).eval a =
      (basis k).coord p ((naturalAction k (f.onPoints (kPlusPoint a))).1 (basis k q)) := by
  rw [polynomial, kPlusPolynomialFunctionAlgEquiv_eval]
  exact coordinate_apply k p q _

open scoped BigOperators

/-- Forget which of the two coordinates in a hyperbolic plane is selected. -/
@[expose] def pairIndex : Index → Fin 4 := Sum.elim id id

omit [IsAlgClosed k] in
lemma basis_apply (q : Index) : basis k q =
    match q with
    | .inl i => (Pi.single i 1, 0)
    | .inr i => (0, Pi.single i 1) := by
  cases q <;> simp [basis]

omit [IsAlgClosed k] in
lemma basis_coord_inl (v : QuadraticSpace k) (i : Fin 4) :
    (basis k).coord (.inl i) v = v.1 i := by simp [basis]
omit [IsAlgClosed k] in
lemma basis_coord_inr (v : QuadraticSpace k) (i : Fin 4) :
    (basis k).coord (.inr i) v = v.2 i := by simp [basis]

/-- The actual natural-action matrix in the hyperbolic basis. -/
@[expose] def pointMatrix (g : Points k) : Matrix Index Index k :=
  LinearMap.toMatrix (basis k) (basis k) (naturalAction k g).1.toLinearMap

lemma pointMatrix_apply (g : Points k) (p q : Index) :
    pointMatrix k g p q = (basis k).coord p ((naturalAction k g).1 (basis k q)) := by
  rw [pointMatrix, LinearMap.toMatrix_apply]
  rfl

lemma pointMatrix_one : pointMatrix k 1 = 1 := by
  simp [pointMatrix]

lemma pointMatrix_mul (g h : Points k) :
    pointMatrix k (g * h) = pointMatrix k g * pointMatrix k h := by
  simp only [pointMatrix, map_mul]
  exact LinearMap.toMatrix_mul (basis k) _ _

lemma polynomial_eval_matrix (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (p q : Index) (a : k) :
    (polynomial k f p q).eval a = pointMatrix k (f.onPoints (kPlusPoint a)) p q :=
  (polynomial_eval k f p q a).trans (pointMatrix_apply k _ p q).symm

lemma polynomial_eval_zero (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k))
    (p q : Index) :
    (polynomial k f p q).eval 0 = if p = q then 1 else 0 := by
  rw [polynomial_eval_matrix, kPlusPoint_zero, map_one, pointMatrix_one, Matrix.one_apply]

lemma polynomial_isotropic_column
    (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k)) (q : Index) :
    ∑ i : Fin 4, polynomial k f (.inl i) q * polynomial k f (.inr i) q = 0 := by
  apply Polynomial.funext
  intro a
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_zero,
    polynomial_eval, basis_coord_inl, basis_coord_inr]
  rw [← hyperbolicForm_apply]
  rw [(mem_quadraticIsometrySubgroup _ _).1 (naturalAction k (f.onPoints (kPlusPoint a))).2]
  cases q <;> simp [basis_apply, quadraticForm, hyperbolicForm_apply]

lemma polynomial_diagonal_ne_zero
    (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k)) (p : Index) :
    polynomial k f p p ≠ 0 := by
  intro h
  have he := polynomial_eval_zero k f p p
  simp [h] at he

variable [CharP k 2]
lemma pointMatrix_injective : Function.Injective (pointMatrix k) := by
  intro g h hgh
  apply naturalAction_injective k
  apply Subtype.ext
  apply LinearEquiv.toLinearMap_injective
  exact (LinearMap.toMatrix (basis k) (basis k)).injective hgh

lemma curve_square (f : AlgebraicGroup.Morphism (KPlus k) (groupVariety k)) (a : k) :
    f.onPoints (kPlusPoint a) * f.onPoints (kPlusPoint a) = 1 := by
  rw [← map_mul, ← f.onPoints.map_one]
  congr 1
  apply (additiveGroupPointEquiv k).injective
  change a + a = 0
  exact CharTwo.add_self_eq_zero a

end Triality.SimplyConnected.Pinning.NaturalCoefficients
