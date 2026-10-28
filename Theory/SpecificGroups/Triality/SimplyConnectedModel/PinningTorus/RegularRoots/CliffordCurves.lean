module

public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.ClosedRoots
public import Theory.SpecificGroups.Triality.SimplyConnectedModel.PinningTorus.RegularRoots.CliffordCurves.IsotropicPair
public import Theory.AlgebraicGroup.Representations.Matrix
import Mathlib.Tactic.NormNum
/-!
# Explicit regular Clifford lifts of the D4 root curves

For each signed coordinate root, choose the corresponding two orthogonal
isotropic basis vectors `u, v`. The element `1 + a • (u v)` belongs to the
generated Spin group, and Clifford conjugation gives exactly the fixed
orthogonal root matrix in characteristic two. Faithfulness of the natural
action identifies this element with the anchored `rootPoint`.

In the carrier's actual Clifford basis, left multiplication has matrix
coefficients affine in `a`. The inverse coefficients are obtained by pulling
back along additive inversion. These polynomials construct a genuine morphism
into the general-linear variety, whose points lie in the exact closed Spin
carrier. Codomain restriction gives `cliffordRootMorphism`, with the original
root numbering and parameter. The point inverse to the Spin cover is used
only to identify the prescribed anchor, not to infer regularity.

The closed-root and parameter-recovery infrastructure is imported directly;
`rootParametrizationOfMorphism` can now be applied without extra premises.
The D4 root-realization assembly remains separate.

Source: GLS3, §§1.9–1.12, especially the classical Spin model in 1.10.7(d)
and the normalized root parameters in 1.12.1
(`refs/KGroup/GLS3/Chapter1.tex`).
-/

public section
noncomputable section
open Theory.AlgebraicGroup.CliffordIsotropicPair
namespace Triality.SimplyConnected.Pinning
open CliffordAlgebra Theory.AlgebraicGroup
universe u
variable (k : Type u) [Field k] [IsAlgClosed k] [CharP k 2]

private def rootAxis (i : Fin 4) (s : ℝ) : QuadraticSpace k :=
  if s = 1 then (Pi.single i 1, 0) else (0, Pi.single i 1)

private def rootU (r : RootIndex) : QuadraticSpace k := rootAxis k r.1.1.1 r.2.1.1
private def rootV (r : RootIndex) : QuadraticSpace k := rootAxis k r.1.1.2 r.2.2.1

omit [IsAlgClosed k] [CharP k 2] in
private lemma rootAxis_isotropic (i : Fin 4) (s : ℝ) :
    quadraticForm k (rootAxis k i s) = 0 := by
  classical
  unfold rootAxis
  split <;> simp [quadraticForm]

omit [IsAlgClosed k] [CharP k 2] in
private lemma rootAxes_ortho (r : RootIndex) :
    (quadraticForm k).IsOrtho (rootU k r) (rootV k r) := by
  classical
  apply QuadraticMap.isOrtho_polarBilin.mp
  change (hyperbolicForm 4).polarBilin (rootU k r) (rootV k r) = 0
  rw [hyperbolicForm_polar]
  unfold rootU rootV rootAxis
  split <;> split <;> simp [Pi.single_apply, r.1.2.ne, r.1.2.ne']

omit [IsAlgClosed k] in
private lemma root_action_formula (r : RootIndex) (a : k) (z : QuadraticSpace k) :
    z + a • ((quadraticForm k).polarBilin (rootV k r) z • rootU k r -
      (quadraticForm k).polarBilin (rootU k r) z • rootV k r) =
      (evenOrthogonalRootQuadraticPoint 4 r a).1 z := by
  classical
  have hn : (-1 : ℝ) ≠ 1 := by norm_num
  rcases r with ⟨⟨⟨i, j⟩, hij⟩, ⟨s, hs⟩, ⟨t, ht⟩⟩
  rcases hs with hs | hs <;> rcases ht with ht | ht <;>
    subst s <;> subst t
  all_goals
    simp only [rootU, rootV, rootAxis, hn, if_false, if_true, quadraticForm, hyperbolicForm_polar]
    apply Prod.ext <;> funext p <;>
    simp [hn,
      evenOrthogonalRootQuadraticPoint, evenOrthogonalRootIsometry,
      hyperbolicLowerRoot, hyperbolicLowerRootLinearEquiv,
      hyperbolicUpperRoot, hyperbolicUpperRootLinearEquiv,
      hyperbolicSkewUpperRoot, hyperbolicSkewUpperRootLinearEquiv,
      Pi.single_apply, CharTwo.neg_eq, sub_eq_add_neg, add_assoc]

/-- The product of the two signed isotropic coordinate vectors of a D4 root. -/
def rootBivector (r : RootIndex) : CliffordAlgebra (quadraticForm k) :=
  ι (quadraticForm k) (rootU k r) * ι (quadraticForm k) (rootV k r)

/-- The anchored root point is the explicit Clifford unit `1 + a uv`. -/
theorem rootPoint_clifford (r : RootIndex) (a : k) :
    (pointEquiv k (rootPoint k r a) : CliffordAlgebra (quadraticForm k)) =
      1 + a • rootBivector k r := by
  let sx : spinGroup (quadraticForm k) :=
    ⟨1 + a • rootBivector k r,
      curve_mem_spin (quadraticForm k) (rootU k r) (rootV k r)
        (rootAxis_isotropic k _ _) (rootAxis_isotropic k _ _)
        (rootAxes_ortho k r) (standardHyperbolicSplit 4) (by simp) a⟩
  have he : (pointEquiv k).symm sx = rootPoint k r a := by
    apply (eq_rootPoint_iff k r a _).mpr
    apply Subtype.ext
    apply LinearEquiv.ext
    intro z
    apply CliffordAlgebra.ι_injective_of_actionForm (quadraticForm k)
      (standardHyperbolicSplit 4).actionForm
    rw [naturalAction_clifford, MulEquiv.apply_symm_apply]
    change (1 + a • rootBivector k r) * ι (quadraticForm k) z *
      star (1 + a • rootBivector k r) = _
    rw [rootBivector, curve_star (quadraticForm k) (rootU k r) (rootV k r)
      (rootAxes_ortho k r),
      curve_conj (quadraticForm k) (rootU k r) (rootV k r)
        (rootAxis_isotropic k _ _) (rootAxis_isotropic k _ _) (rootAxes_ortho k r),
      root_action_formula]
  have h := congrArg (fun x => (pointEquiv k x : CliffordAlgebra (quadraticForm k))) he
  simpa only [MulEquiv.apply_symm_apply] using h.symm

private abbrev C := CliffordAlgebra (quadraticForm k)
private instance : Module.Finite k (C k) := (standardHyperbolicSplit 4).moduleFinite
private abbrev basis := (cliffordModel k).cliffordBasis

private def carrierRepresentation : Points k →* LinearMap.GeneralLinearGroup k (C k) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).symm.toMonoidHom.comp
    ((Units.mulLeftLinearEquiv k (C k)).comp
      (spinGroup.toUnits.comp (pointEquiv k).toMonoidHom))

omit [CharP k 2] in
private theorem carrierRepresentation_apply (g : Points k) (x : C k) :
    (carrierRepresentation k g : Module.End k (C k)) x =
      (pointEquiv k g : C k) * x := rfl

omit [CharP k 2] in
private theorem inclusion_representation (g : Points k) :
    glPointEquivOf k (C k) (basis k) ((cliffordModel k).spin.inclusion.onPoints g) =
      carrierRepresentation k g := by
  apply (LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).injective
  change _ = (LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k))
    ((LinearMap.GeneralLinearGroup.generalLinearEquiv k (C k)).symm _)
  rw [MulEquiv.apply_symm_apply]
  exact (cliffordModel k).spinLinear_points g

private def rootPointMap (r : RootIndex) : Variety.Point (KPlus k) →* Points k where
  toFun x := rootPoint k r (x.val PUnit.unit)
  map_one' := rootPoint_zero k r
  map_mul' x y := by
    rw [kPlusPoint_coordinate_mul, rootPoint_add]

private def rootRepresentation (r : RootIndex) :
    Variety.Point (KPlus k) →* LinearMap.GeneralLinearGroup k (C k) :=
  (carrierRepresentation k).comp (rootPointMap k r)

private theorem rootRepresentation_apply (r : RootIndex)
    (x : Variety.Point (KPlus k)) (c : C k) :
    (rootRepresentation k r x : Module.End k (C k)) c =
      c + (x.val PUnit.unit) • (rootBivector k r * c) := by
  change (carrierRepresentation k (rootPoint k r (x.val PUnit.unit)) : Module.End k (C k)) c = _
  rw [carrierRepresentation_apply, rootPoint_clifford, add_mul, one_mul, smul_mul_assoc]

private def matrixCoefficient (r : RootIndex) (i j : Fin (Module.finrank k (C k))) :
    (KPlus k).PolynomialFunction :=
  Variety.PolynomialFunction.ofPolynomial (KPlus k)
    (MvPolynomial.C ((basis k).repr (basis k j) i) +
      MvPolynomial.X PUnit.unit *
        MvPolynomial.C ((basis k).repr (rootBivector k r * basis k j) i))

private theorem matrixCoefficient_apply (r : RootIndex)
    (i j : Fin (Module.finrank k (C k))) (x : Variety.Point (KPlus k)) :
    matrixCoefficient k r i j x =
      (basis k).repr ((rootRepresentation k r x : Module.End k (C k)) (basis k j)) i := by
  rw [rootRepresentation_apply]
  change evalPolynomial x.val _ = _
  simp [evalPolynomial, map_add, map_smul]

private def inverseMatrixCoefficient (r : RootIndex)
    (i j : Fin (Module.finrank k (C k))) : (KPlus k).PolynomialFunction :=
  Variety.PolynomialFunction.pullback (Theory.AlgebraicGroup.invMorphism (KPlus k))
    (matrixCoefficient k r i j)

private theorem inverseMatrixCoefficient_apply (r : RootIndex)
    (i j : Fin (Module.finrank k (C k))) (x : Variety.Point (KPlus k)) :
    inverseMatrixCoefficient k r i j x =
      (basis k).repr ((((rootRepresentation k r x)⁻¹ : LinearMap.GeneralLinearGroup k (C k)) :
        Module.End k (C k)) (basis k j)) i := by
  change matrixCoefficient k r i j x⁻¹ = _
  rw [matrixCoefficient_apply, map_inv]

private def ambientMorphism (r : RootIndex) : Morphism (KPlus k) (glVarietyOf k (C k)) :=
  generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    (basis k) (rootRepresentation k r) (matrixCoefficient k r)
    (inverseMatrixCoefficient k r) (matrixCoefficient_apply k r)
    (inverseMatrixCoefficient_apply k r)

private theorem ambientMorphism_apply (r : RootIndex) (x : Variety.Point (KPlus k)) :
    (ambientMorphism k r).onPoints x =
      (cliffordModel k).spin.inclusion.onPoints (rootPoint k r (x.val PUnit.unit)) := by
  apply (glPointEquivOf k (C k) (basis k)).injective
  change glPointEquivOf k (C k) (basis k)
      (generalLinearRepresentationPoint (basis k) (rootRepresentation k r x)) = _
  rw [glPointEquivOf_generalLinearRepresentationPoint, inclusion_representation]
  rfl

private theorem ambientMorphism_mem (r : RootIndex) (x : Variety.Point (KPlus k)) :
    (ambientMorphism k r).onPoints x ∈ (cliffordModel k).spin.toSubgroup := by
  rw [ambientMorphism_apply]
  exact ((cliffordModel k).spin.pointEquiv _).property

/-- The regular root curve in the fixed Clifford Spin carrier. -/
def cliffordRootMorphism (r : RootIndex) : Morphism (KPlus k) (groupVariety k) :=
  (ambientMorphism k r).codRestrictClosedSubgroup (cliffordModel k).spin
    (ambientMorphism_mem k r)

/-- The Clifford curve has exactly the prescribed root-point normalization. -/
@[simp] theorem cliffordRootMorphism_onPoints (r : RootIndex) (x : Variety.Point (KPlus k)) :
    (cliffordRootMorphism k r).onPoints x = rootPoint k r (x.val PUnit.unit) := by
  apply (cliffordModel k).spin.inclusion_injective
  rw [cliffordRootMorphism, Morphism.codRestrictClosedSubgroup_inclusion_apply,
    ambientMorphism_apply]

/-- In particular, the source parameter is unchanged. -/
@[simp] theorem cliffordRootMorphism_kPlusPoint (r : RootIndex) (a : k) :
    (cliffordRootMorphism k r).onPoints (kPlusPoint a) = rootPoint k r a :=
  cliffordRootMorphism_onPoints k r (kPlusPoint a)

/-- The explicit root curve intertwines the genuine regular Spin cover. -/
theorem cliffordRootMorphism_cover (r : RootIndex) :
    (rootCover k).comp (cliffordRootMorphism k r) = omegaRootMorphism k r :=
  rootMorphism_cover_of_points k r (cliffordRootMorphism k r)
    (cliffordRootMorphism_kPlusPoint k r)

end Triality.SimplyConnected.Pinning
