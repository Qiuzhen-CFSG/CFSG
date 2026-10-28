module

public import Mathlib.RingTheory.Derivation.Basic
public import Theory.AlgebraicGroup.CoordinateRing.Tensor
public import Theory.AlgebraicGroup.Representations.Algebraic.WeightSetFinite

/-!
# Identity tangents of root subgroups

This module models the tangent space of an algebraic group at the identity by
derivations of its coordinate algebra into the residue field.  Evaluation on
ambient coordinates embeds this space in a finite-dimensional coordinate
space, pullback supplies the functorial differential of group morphisms, and
conjugation supplies its rational representation.  A public evaluation theorem
records the representation action without exposing its private implementation,
so later tangent-centralizer arguments can compare coordinate pullbacks.  Its
rationality follows by differentiating the regular two-variable conjugation
family in the second variable: the product coordinate-ring tensor equivalence
makes every resulting tangent matrix coefficient regular in the first
variable.  Consequently restriction to every closed subtorus is spanned by
character weight spaces.

For a one-parameter closed subgroup, the public canonical derivative on the
additive group pushes forward to a nonzero ambient identity tangent.  The range lemma
below also records that this vector comes from the subgroup's own identity
tangent space.  If the subgroup has torus root weight `chi`, equivariance of
its parametrization makes this tangent a vector of inverse weight `chi⁻¹`.
This is the lower-layer tangent input used to prove finiteness and multiplicity
results for the roots of GLS3, Definitions 1.9.1--1.9.3; it uses no clause of
GLS3 Theorem 1.9.5.
-/

universe u

namespace Theory.AlgebraicGroup

open scoped TensorProduct

variable {k : Type u} [Field k] [IsAlgClosed k]

public noncomputable instance identityPointModule (K : Variety k) [AlgebraicGroup K] :
    Module (Variety.PolynomialFunction K) k :=
  Module.compHom k (polynomialFunctionPointAlgHom K 1).toRingHom

public noncomputable abbrev IdentityPointDerivation
    (K : Variety k) [AlgebraicGroup K] :=
  Derivation k (Variety.PolynomialFunction K) k

noncomputable def coordinateTangentMap
    (K : Variety k) [AlgebraicGroup K] :
    IdentityPointDerivation K →ₗ[k] K.Coordinates → k where
  toFun D i := D (Variety.PolynomialFunction.ofPolynomial K (MvPolynomial.X i))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsAlgClosed k] in
lemma coordinateTangentMap_injective (K : Variety k) [AlgebraicGroup K] :
    Function.Injective (coordinateTangentMap K) := by
  intro D E hDE
  apply Derivation.ext_of_adjoin_eq_top
    (Set.range fun i : K.Coordinates ↦
      Variety.PolynomialFunction.ofPolynomial K (MvPolynomial.X i))
  · rw [Algebra.adjoin_range_eq_range_aeval]
    apply (AlgHom.range_eq_top _).2
    intro f
    obtain ⟨p, hp⟩ := f.representedBy
    refine ⟨p, ?_⟩
    apply Variety.PolynomialFunction.ext
    intro x
    rw [hp]
    have haeval :
        MvPolynomial.aeval (fun i : K.Coordinates ↦
          Variety.PolynomialFunction.ofPolynomial K (MvPolynomial.X i)) =
          evaluationAlgHom K := by
      apply MvPolynomial.algHom_ext
      intro i
      apply Variety.PolynomialFunction.ext
      intro y
      rw [MvPolynomial.aeval_X]
      rfl
    rw [haeval]
    rfl
  · rintro _ ⟨i, rfl⟩
    exact congrFun hDE i

public noncomputable instance identityPointDerivationFiniteDimensional
    (K : Variety k) [AlgebraicGroup K] :
    FiniteDimensional k (IdentityPointDerivation K) :=
  FiniteDimensional.of_injective (coordinateTangentMap K)
    (coordinateTangentMap_injective K)

/-- The linear action on the identity tangent induced by conjugation by a
group point. -/
@[expose]
public noncomputable def identityTangentConjugationLinearMap
    (K : Variety k) [AlgebraicGroup K] (g : Variety.Point K) :
    IdentityPointDerivation K →ₗ[k] IdentityPointDerivation K where
  toFun D := {
    toLinearMap := D.toLinearMap.comp
      (AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom.toLinearMap
    map_one_eq_zero' := by simp
    leibniz' := by
      intro f h
      change D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom (f * h)) =
        f • D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom h) +
          h • D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom f)
      rw [map_mul, Derivation.leibniz]
      change f ((AlgebraicGroup.conjugationByMorphism K g).toFun 1) *
            D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom h) +
          h ((AlgebraicGroup.conjugationByMorphism K g).toFun 1) *
            D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom f) =
        f 1 * D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom h) +
          h 1 * D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom f)
      rw [AlgebraicGroup.conjugationByMorphism_apply]
      simp }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

omit [IsAlgClosed k] in
/-- Conjugation transports an identity derivation by pullback along the
conjugation morphism. -/
@[simp] public theorem identityTangentConjugationLinearMap_apply
    (K : Variety k) [AlgebraicGroup K] (g : Variety.Point K)
    (D : IdentityPointDerivation K) (a : Variety.PolynomialFunction K) :
    identityTangentConjugationLinearMap K g D a =
      D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom a) := rfl

omit [IsAlgClosed k] in
lemma identityTangentConjugationLinearMap_one
    (K : Variety k) [AlgebraicGroup K] :
    identityTangentConjugationLinearMap K 1 = LinearMap.id := by
  apply LinearMap.ext
  intro D
  apply Derivation.ext
  intro f
  change D ((AlgebraicGroup.conjugationByMorphism K 1).pullbackAlgHom f) = D f
  apply congrArg D
  apply Variety.PolynomialFunction.ext
  intro x
  change f ((AlgebraicGroup.conjugationByMorphism K 1).toFun x) = f x
  rw [AlgebraicGroup.conjugationByMorphism_apply]
  simp

omit [IsAlgClosed k] in
lemma identityTangentConjugationLinearMap_mul
    (K : Variety k) [AlgebraicGroup K] (g h : Variety.Point K) :
    identityTangentConjugationLinearMap K (g * h) =
      (identityTangentConjugationLinearMap K g).comp
        (identityTangentConjugationLinearMap K h) := by
  apply LinearMap.ext
  intro D
  apply Derivation.ext
  intro f
  change D ((AlgebraicGroup.conjugationByMorphism K (g * h)).pullbackAlgHom f) =
    D ((AlgebraicGroup.conjugationByMorphism K h).pullbackAlgHom
      ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom f))
  apply congrArg D
  apply Variety.PolynomialFunction.ext
  intro x
  change f ((AlgebraicGroup.conjugationByMorphism K (g * h)).toFun x) =
    f ((AlgebraicGroup.conjugationByMorphism K g).toFun
      ((AlgebraicGroup.conjugationByMorphism K h).toFun x))
  simp only [AlgebraicGroup.conjugationByMorphism_apply]
  congr 1
  group

public noncomputable def identityTangentRepresentation
    (K : Variety k) [AlgebraicGroup K] :
    RationalRepresentation K (IdentityPointDerivation K) where
  action := {
    toFun := fun g ↦ {
      val := identityTangentConjugationLinearMap K g
      inv := identityTangentConjugationLinearMap K g⁻¹
      val_inv := by
        change (identityTangentConjugationLinearMap K g).comp
          (identityTangentConjugationLinearMap K g⁻¹) = LinearMap.id
        rw [← identityTangentConjugationLinearMap_mul, mul_inv_cancel,
          identityTangentConjugationLinearMap_one]
      inv_val := by
        change (identityTangentConjugationLinearMap K g⁻¹).comp
          (identityTangentConjugationLinearMap K g) = LinearMap.id
        rw [← identityTangentConjugationLinearMap_mul, inv_mul_cancel,
          identityTangentConjugationLinearMap_one] }
    map_one' := by
      apply Units.ext
      exact identityTangentConjugationLinearMap_one K
    map_mul' := by
      intro g h
      apply Units.ext
      exact identityTangentConjugationLinearMap_mul K g h }

omit [IsAlgClosed k] in
private lemma identityTangentRepresentation_action_apply_private
    (K : Variety k) [AlgebraicGroup K] (g : Variety.Point K)
    (D : IdentityPointDerivation K) (f : Variety.PolynomialFunction K) :
    (((identityTangentRepresentation K).action g).1 D) f =
      D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom f) := rfl

omit [IsAlgClosed k] in
/-- Evaluation of the identity-tangent conjugation representation is pullback
along conjugation.  This is the stable public specification of
`identityTangentRepresentation`; its construction remains private. -/
public theorem identityTangentRepresentation_action_apply
    (K : Variety k) [AlgebraicGroup K] (g : Variety.Point K)
    (D : IdentityPointDerivation K) (f : Variety.PolynomialFunction K) :
    (((identityTangentRepresentation K).action g).1 D) f =
      D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom f) :=
  identityTangentRepresentation_action_apply_private K g D f

private noncomputable def conjugationFamilyMorphism
    (K : Variety k) [AlgebraicGroup K] :
    Variety.Morphism (Variety.prod K K) K := by
  let g := Variety.Morphism.fst K K
  let x := Variety.Morphism.snd K K
  let gx := (AlgebraicGroup.mulMorphism K).comp (g.pair x)
  let ginv := (AlgebraicGroup.invMorphism K).comp g
  exact (AlgebraicGroup.mulMorphism K).comp (gx.pair ginv)

omit [IsAlgClosed k] in
private lemma conjugationFamilyMorphism_apply
    (K : Variety k) [AlgebraicGroup K] (g x : Variety.Point K) :
    (conjugationFamilyMorphism K).toFun
        ((Variety.prodPointEquiv K K).symm (g, x)) =
      g * x * g⁻¹ := by
  simp [conjugationFamilyMorphism, AlgebraicGroup.mulMorphism,
    AlgebraicGroup.invMorphism, Variety.Morphism.comp, Variety.Morphism.pair,
    Variety.Morphism.fst, Variety.Morphism.snd, Variety.prodPointEquiv]

private noncomputable def tensorRightDerivation
    (K : Variety k) [AlgebraicGroup K]
    (D : IdentityPointDerivation K)
    (z : K.PolynomialFunction ⊗[k] K.PolynomialFunction) :
    K.PolynomialFunction :=
  TensorProduct.rid k K.PolynomialFunction
    ((D.toLinearMap.lTensor K.PolynomialFunction) z)

private def polynomialFunctionEvaluation
    (K : Variety k) (g : Variety.Point K) :
    K.PolynomialFunction →ₗ[k] k where
  toFun q := q g
  map_add' _ _ := rfl
  map_smul' a q := polynomialFunction_smul_apply K a q g

private noncomputable def tensorLeftSlice
    (K : Variety k)
    (z : K.PolynomialFunction ⊗[k] K.PolynomialFunction)
    (g : Variety.Point K) : K.PolynomialFunction :=
  TensorProduct.lid k K.PolynomialFunction
    (((polynomialFunctionEvaluation K g).rTensor K.PolynomialFunction) z)

omit [IsAlgClosed k] in
private lemma tensorLeftSlice_apply
    (K : Variety k)
    (z : K.PolynomialFunction ⊗[k] K.PolynomialFunction)
    (g x : Variety.Point K) :
    tensorLeftSlice K z g x =
      polynomialFunctionTensor K K z
        ((Variety.prodPointEquiv K K).symm (g, x)) := by
  induction z with
  | zero => simp [tensorLeftSlice]
  | tmul f q =>
      rw [tensorLeftSlice, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        polynomialFunctionTensor_tmul, polynomialFunction_smul_apply]
      rfl
  | add z w hz hw =>
      rw [show tensorLeftSlice K (z + w) g =
        tensorLeftSlice K z g + tensorLeftSlice K w g by
          simp only [tensorLeftSlice, map_add]]
      rw [show polynomialFunctionTensor K K (z + w) =
        polynomialFunctionTensor K K z + polynomialFunctionTensor K K w by
          exact map_add (polynomialFunctionTensor K K) z w]
      change tensorLeftSlice K z g x + tensorLeftSlice K w g x =
        polynomialFunctionTensor K K z
            ((Variety.prodPointEquiv K K).symm (g, x)) +
          polynomialFunctionTensor K K w
            ((Variety.prodPointEquiv K K).symm (g, x))
      rw [hz, hw]

omit [IsAlgClosed k] in
private lemma tensorRightDerivation_apply
    (K : Variety k) [AlgebraicGroup K]
    (D : IdentityPointDerivation K)
    (z : K.PolynomialFunction ⊗[k] K.PolynomialFunction)
    (g : Variety.Point K) :
    tensorRightDerivation K D z g =
      D (tensorLeftSlice K z g) := by
  induction z with
  | zero => simp [tensorRightDerivation, tensorLeftSlice]
  | tmul f q =>
      rw [tensorRightDerivation, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
        tensorLeftSlice, LinearMap.rTensor_tmul, TensorProduct.lid_tmul,
        polynomialFunction_smul_apply]
      change D.toLinearMap q * f g =
        D.toLinearMap ((polynomialFunctionEvaluation K g) f • q)
      rw [D.toLinearMap.map_smul]
      change D q * f g = f g * D q
      exact mul_comm _ _
  | add z w hz hw =>
      rw [show tensorRightDerivation K D (z + w) =
        tensorRightDerivation K D z + tensorRightDerivation K D w by
          simp only [tensorRightDerivation, map_add]]
      rw [show tensorLeftSlice K (z + w) g =
        tensorLeftSlice K z g + tensorLeftSlice K w g by
          simp only [tensorLeftSlice, map_add]]
      change polynomialFunctionEvalAddHom K g
          (tensorRightDerivation K D z + tensorRightDerivation K D w) =
        D.toLinearMap (tensorLeftSlice K z g + tensorLeftSlice K w g)
      rw [map_add, map_add]
      change tensorRightDerivation K D z g + tensorRightDerivation K D w g =
        D (tensorLeftSlice K z g) + D (tensorLeftSlice K w g)
      rw [hz, hw]

private noncomputable def tangentConjugationCoefficient
    (K : Variety k) [AlgebraicGroup K]
    (D : IdentityPointDerivation K) (q : K.PolynomialFunction) :
    K.PolynomialFunction :=
  tensorRightDerivation K D
    ((polynomialFunction_prod_algEquiv K K).symm
      ((conjugationFamilyMorphism K).pullbackAlgHom q))

omit [IsAlgClosed k] in
private lemma tangentConjugationCoefficient_apply
    (K : Variety k) [AlgebraicGroup K]
    (D : IdentityPointDerivation K) (q : K.PolynomialFunction)
    (g : Variety.Point K) :
    tangentConjugationCoefficient K D q g =
      D ((AlgebraicGroup.conjugationByMorphism K g).pullbackAlgHom q) := by
  rw [tangentConjugationCoefficient, tensorRightDerivation_apply]
  congr 1
  apply Variety.PolynomialFunction.ext
  intro x
  rw [tensorLeftSlice_apply]
  change ((polynomialFunction_prod_algEquiv K K)
      ((polynomialFunction_prod_algEquiv K K).symm
        ((conjugationFamilyMorphism K).pullbackAlgHom q)))
      ((Variety.prodPointEquiv K K).symm (g, x)) = _
  rw [(polynomialFunction_prod_algEquiv K K).apply_symm_apply]
  change q ((conjugationFamilyMorphism K).toFun
      ((Variety.prodPointEquiv K K).symm (g, x))) =
    q ((AlgebraicGroup.conjugationByMorphism K g).toFun x)
  rw [conjugationFamilyMorphism_apply,
    AlgebraicGroup.conjugationByMorphism_apply]

private noncomputable def coordinateTangentFunctional
    (K : Variety k) [AlgebraicGroup K] (c : K.Coordinates) :
    Module.Dual k (IdentityPointDerivation K) where
  toFun D := coordinateTangentMap K D c
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsAlgClosed k] in
private lemma tangentDual_mem_span_coordinate
    (K : Variety k) [AlgebraicGroup K]
    (L : Module.Dual k (IdentityPointDerivation K)) :
    L ∈ Submodule.span k (Set.range (coordinateTangentFunctional K)) := by
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro D hD
  have hcoord : coordinateTangentMap K D = 0 := by
    funext c
    have hc : D ∈ LinearMap.ker (coordinateTangentFunctional K c) :=
      (Submodule.mem_iInf _).1 hD c
    exact LinearMap.mem_ker.mp hc
  have hDzero : D = 0 := coordinateTangentMap_injective K hcoord
  rw [hDzero]
  exact L.map_zero

private noncomputable def tangentDualCoordinates
    (K : Variety k) [AlgebraicGroup K]
    (L : Module.Dual k (IdentityPointDerivation K)) :
    K.Coordinates →₀ k :=
  Classical.choose (Finsupp.mem_span_range_iff_exists_finsupp.mp
    (tangentDual_mem_span_coordinate K L))

omit [IsAlgClosed k] in
private lemma tangentDualCoordinates_spec
    (K : Variety k) [AlgebraicGroup K]
    (L : Module.Dual k (IdentityPointDerivation K)) :
    (tangentDualCoordinates K L).sum
        (fun c a => a • coordinateTangentFunctional K c) = L :=
  Classical.choose_spec (Finsupp.mem_span_range_iff_exists_finsupp.mp
    (tangentDual_mem_span_coordinate K L))

omit [IsAlgClosed k] in
private noncomputable def identityTangentMatrixCoefficient
    (K : Variety k) [AlgebraicGroup K]
    (e : Module.Basis (Fin (Module.finrank k (IdentityPointDerivation K))) k
      (IdentityPointDerivation K))
    (i j : Fin (Module.finrank k (IdentityPointDerivation K))) :
    K.PolynomialFunction :=
  (tangentDualCoordinates K (e.coord i)).sum fun c a =>
    a • tangentConjugationCoefficient K (e j)
      (Variety.PolynomialFunction.ofPolynomial K (MvPolynomial.X c))

omit [IsAlgClosed k] in
private lemma identityTangentMatrixCoefficient_apply
    (K : Variety k) [AlgebraicGroup K]
    (e : Module.Basis (Fin (Module.finrank k (IdentityPointDerivation K))) k
      (IdentityPointDerivation K))
    (i j : Fin (Module.finrank k (IdentityPointDerivation K)))
    (g : Variety.Point K) :
    identityTangentMatrixCoefficient K e i j g =
      e.repr (((identityTangentRepresentation K).action g :
        Module.End k (IdentityPointDerivation K)) (e j)) i := by
  let c := tangentDualCoordinates K (e.coord i)
  have hc := congrArg
    (fun L : Module.Dual k (IdentityPointDerivation K) =>
      L (((identityTangentRepresentation K).action g :
        Module.End k (IdentityPointDerivation K)) (e j)))
    (tangentDualCoordinates_spec K (e.coord i))
  change
    (c.sum fun x a => a • coordinateTangentFunctional K x)
        (((identityTangentRepresentation K).action g :
          Module.End k (IdentityPointDerivation K)) (e j)) =
      e.repr (((identityTangentRepresentation K).action g :
        Module.End k (IdentityPointDerivation K)) (e j)) i at hc
  rw [← hc]
  change polynomialFunctionEvalAddHom K g
      (c.sum fun x a => a • tangentConjugationCoefficient K (e j)
        (Variety.PolynomialFunction.ofPolynomial K (MvPolynomial.X x))) =
    (LinearMap.applyₗ (R := k) (M := IdentityPointDerivation K) (M₂ := k)
      (((identityTangentRepresentation K).action g :
        Module.End k (IdentityPointDerivation K)) (e j)))
      (c.sum fun x a => a • coordinateTangentFunctional K x)
  rw [map_finsuppSum, map_finsuppSum]
  apply Finsupp.sum_congr
  intro x hx
  change
    (c x • tangentConjugationCoefficient K (e j)
      (Variety.PolynomialFunction.ofPolynomial K (MvPolynomial.X x))) g =
    (c x • coordinateTangentFunctional K x)
      (((identityTangentRepresentation K).action g :
        Module.End k (IdentityPointDerivation K)) (e j))
  rw [polynomialFunction_smul_apply, LinearMap.smul_apply]
  congr 1
  rw [tangentConjugationCoefficient_apply]
  rfl

/-- Conjugation on the tangent space at the identity is a rational
representation. -/
public theorem identityTangentRepresentation_isRational
    (K : Variety k) [AlgebraicGroup K] :
    IsRationalRepresentation (identityTangentRepresentation K) := by
  let e := Module.finBasis k (IdentityPointDerivation K)
  let matrixCoefficient := identityTangentMatrixCoefficient K e
  let inverseMatrixCoefficient := fun i j =>
    Variety.PolynomialFunction.pullback (AlgebraicGroup.invMorphism K)
      (matrixCoefficient i j)
  have hm : ∀ i j g, matrixCoefficient i j g =
      e.repr (((identityTangentRepresentation K).action g :
        Module.End k (IdentityPointDerivation K)) (e j)) i := by
    exact identityTangentMatrixCoefficient_apply K e
  have him : ∀ i j g, inverseMatrixCoefficient i j g =
      e.repr (((((identityTangentRepresentation K).action g)⁻¹ :
        LinearMap.GeneralLinearGroup k (IdentityPointDerivation K)) :
        Module.End k (IdentityPointDerivation K)) (e j)) i := by
    intro i j g
    change matrixCoefficient i j g⁻¹ = _
    rw [hm]
    simp
  let f := generalLinearRepresentationMorphismOfInverseMatrixCoefficient
    e (identityTangentRepresentation K).action matrixCoefficient
      inverseMatrixCoefficient hm him
  refine ⟨e, f, ?_⟩
  intro g
  change glPointEquivOf k (IdentityPointDerivation K) e
    (generalLinearRepresentationPoint e
      ((identityTangentRepresentation K).action g)) =
        (identityTangentRepresentation K).action g
  exact glPointEquivOf_generalLinearRepresentationPoint e
    ((identityTangentRepresentation K).action g)

/-- The identity tangent is spanned by its character weight spaces after
restriction to any closed subtorus. -/
public theorem identityTangentRepresentation_weightSpace_iSup_eq_top
    (K : Variety k) [AlgebraicGroup K]
    (T : ClosedSubgroup K) (hT : IsSubtorus T) :
    (⨆ chi : TorusWeight T,
      weightSpace (identityTangentRepresentation K) T chi) = ⊤ :=
  closedSubtorusRepresentation_weightSpace_iSup_eq_top
    (identityTangentRepresentation K)
      (identityTangentRepresentation_isRational K) T hT

/-- The maximal-torus specialization of the identity-tangent weight-space
spanning theorem. -/
public theorem maximalTorus_identityTangentRepresentation_weightSpace_iSup_eq_top
    (K : Variety k) [AlgebraicGroup K]
    (T : ClosedSubgroup K) (hT : IsMaximalTorus T) :
    (⨆ chi : TorusWeight T,
      weightSpace (identityTangentRepresentation K) T chi) = ⊤ :=
  identityTangentRepresentation_weightSpace_iSup_eq_top K T hT.1

lemma kPlusEvaluationAlgHom_injective :
    Function.Injective (evaluationAlgHom (KPlus k)) := by
  intro p q hpq
  apply MvPolynomial.funext
  intro v
  let x : Variety.Point (KPlus k) := ⟨v, by simp⟩
  exact congrArg (fun f : Variety.PolynomialFunction (KPlus k) ↦ f x) hpq

noncomputable def kPlusPolynomialFunctionAlgEquiv :
    Variety.PolynomialFunction (KPlus k) ≃ₐ[k] Polynomial k :=
  (AlgEquiv.ofBijective (evaluationAlgHom (KPlus k))
    ⟨kPlusEvaluationAlgHom_injective,
      evaluationRingHom_surjective (KPlus k)⟩).symm.trans
        (MvPolynomial.uniqueAlgEquiv k PUnit)

lemma kPlusPolynomialFunctionAlgEquiv_eval
    (f : Variety.PolynomialFunction (KPlus k)) (t : k) :
    (kPlusPolynomialFunctionAlgEquiv f).eval t = f (kPlusPoint t) := by
  let E : MvPolynomial PUnit k ≃ₐ[k]
      Variety.PolynomialFunction (KPlus k) :=
    AlgEquiv.ofBijective (evaluationAlgHom (KPlus k))
      ⟨kPlusEvaluationAlgHom_injective,
        evaluationRingHom_surjective (KPlus k)⟩
  let q : MvPolynomial PUnit k := E.symm f
  have h := congrArg
    (fun q : Variety.PolynomialFunction (KPlus k) ↦ q (kPlusPoint t))
    (E.apply_symm_apply f)
  change MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ t) q =
    f (kPlusPoint t) at h
  calc
    (kPlusPolynomialFunctionAlgEquiv f).eval t =
        ((MvPolynomial.uniqueAlgEquiv k PUnit) q).eval t := by
      rfl
    _ = MvPolynomial.eval₂ (RingHom.id k) (fun _ ↦ t) q := by
      simpa using
        (MvPolynomial.eval₂_const_uniqueAlgEquiv
          (R := k) (S := k) (f := q) (φ := RingHom.id k) (a := t))
    _ = f (kPlusPoint t) := h

omit [IsAlgClosed k] in
lemma kPlusPoint_zero : kPlusPoint (0 : k) = 1 := by
  apply (additiveGroupPointEquiv k).injective
  rfl

public noncomputable def kPlusIdentityDerivation : IdentityPointDerivation (KPlus k) where
  toLinearMap := {
    toFun := fun f ↦ (kPlusPolynomialFunctionAlgEquiv f).derivative.eval 0
    map_add' := by
      intro f g
      rw [map_add, Polynomial.derivative_add, Polynomial.eval_add]
    map_smul' := by
      intro c f
      rw [map_smul, Polynomial.derivative_smul, Polynomial.eval_smul]
      rfl }
  map_one_eq_zero' := by simp
  leibniz' := by
    intro f g
    change (kPlusPolynomialFunctionAlgEquiv (f * g)).derivative.eval 0 =
      f 1 * (kPlusPolynomialFunctionAlgEquiv g).derivative.eval 0 +
        g 1 * (kPlusPolynomialFunctionAlgEquiv f).derivative.eval 0
    rw [map_mul, Polynomial.derivative_mul, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_mul,
      kPlusPolynomialFunctionAlgEquiv_eval,
      kPlusPolynomialFunctionAlgEquiv_eval, kPlusPoint_zero]
    ring

lemma kPlusIdentityDerivation_apply
    (f : Variety.PolynomialFunction (KPlus k)) :
    kPlusIdentityDerivation f =
      (kPlusPolynomialFunctionAlgEquiv f).derivative.eval 0 := rfl

lemma kPlusIdentityDerivation_smulParameter
    (f g : Variety.PolynomialFunction (KPlus k)) (c : k)
    (h : ∀ t, f (kPlusPoint t) = g (kPlusPoint (c * t))) :
    kPlusIdentityDerivation f = c * kPlusIdentityDerivation g := by
  let P := kPlusPolynomialFunctionAlgEquiv f
  let Q := kPlusPolynomialFunctionAlgEquiv g
  have hpoly : P = Q.comp (Polynomial.C c * Polynomial.X) := by
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_comp, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_X, kPlusPolynomialFunctionAlgEquiv_eval,
      kPlusPolynomialFunctionAlgEquiv_eval]
    exact h t
  change P.derivative.eval 0 = c * Q.derivative.eval 0
  rw [hpoly, Polynomial.derivative_comp]
  simp

@[expose]
public noncomputable def identityTangentMorphismLinearMap
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K) :
    IdentityPointDerivation H →ₗ[k] IdentityPointDerivation K where
  toFun D := {
    toLinearMap := D.toLinearMap.comp f.toVariety.pullbackAlgHom.toLinearMap
    map_one_eq_zero' := by simp
    leibniz' := by
      intro p q
      change D (f.toVariety.pullbackAlgHom (p * q)) =
        p • D (f.toVariety.pullbackAlgHom q) +
          q • D (f.toVariety.pullbackAlgHom p)
      rw [map_mul, Derivation.leibniz]
      change p (f.onPoints 1) * D (f.toVariety.pullbackAlgHom q) +
          q (f.onPoints 1) * D (f.toVariety.pullbackAlgHom p) =
        p 1 * D (f.toVariety.pullbackAlgHom q) +
          q 1 * D (f.toVariety.pullbackAlgHom p)
      rw [map_one] }
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

omit [IsAlgClosed k] in
@[simp]
public theorem identityTangentMorphismLinearMap_apply
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K)
    (D : IdentityPointDerivation H)
    (a : Variety.PolynomialFunction K) :
    identityTangentMorphismLinearMap f D a =
      D (f.toVariety.pullbackAlgHom a) := rfl

/- The identity differential of a closed-subgroup inclusion is injective. -/
omit [IsAlgClosed k] in
public theorem identityTangentMorphismLinearMap_inclusion_injective
    {K : Variety k} [AlgebraicGroup K] (H : ClosedSubgroup K) :
    Function.Injective
      (identityTangentMorphismLinearMap H.inclusion) := by
  intro D E hDE
  apply Derivation.ext
  intro a
  obtain ⟨b, hb⟩ := H.restrictionRingHom_surjective a
  have h := congrArg (fun T : IdentityPointDerivation K => T b) hDE
  change D (H.restrictionRingHom b) = E (H.restrictionRingHom b) at h
  simpa [hb] using h

@[expose]
public noncomputable def oneParameterTangent
    {K : Variety k} [AlgebraicGroup K] (X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety) :
    IdentityPointDerivation K :=
  identityTangentMorphismLinearMap (X.inclusion.comp x.hom)
    kPlusIdentityDerivation

public lemma oneParameterTangent_apply
    {K : Variety k} [AlgebraicGroup K] (X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (f : Variety.PolynomialFunction K) :
    oneParameterTangent X x f = kPlusIdentityDerivation
      ((X.inclusion.comp x.hom).toVariety.pullbackAlgHom f) := rfl

/-- The ambient tangent selected by a one-parameter parametrization is in the
range of the subgroup-inclusion differential. -/
public lemma oneParameterTangent_mem_range_inclusion
    {K : Variety k} [AlgebraicGroup K] (X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety) :
    oneParameterTangent X x ∈
      LinearMap.range (identityTangentMorphismLinearMap X.inclusion) := by
  refine ⟨identityTangentMorphismLinearMap x.hom kPlusIdentityDerivation, ?_⟩
  rw [oneParameterTangent]
  apply Derivation.ext
  intro f
  rfl

/-- Rescaling a one-parameter parametrization rescales its ambient tangent by
the same scalar. -/
public lemma oneParameterTangent_rescale
    {K : Variety k} [AlgebraicGroup K] (X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    (c : k) (hc : c ≠ 0) :
    oneParameterTangent X (x.rescale c hc) =
      c • oneParameterTangent X x := by
  apply Derivation.ext
  intro f
  rw [oneParameterTangent_apply]
  let p : Variety.PolynomialFunction (KPlus k) :=
    (X.inclusion.comp (x.rescale c hc).hom).toVariety.pullbackAlgHom f
  let q : Variety.PolynomialFunction (KPlus k) :=
    (X.inclusion.comp x.hom).toVariety.pullbackAlgHom f
  have hpq : ∀ t,
      p (kPlusPoint t) = q (kPlusPoint (c * t)) := by
    intro t
    rfl
  change kPlusIdentityDerivation p = c * kPlusIdentityDerivation q
  exact kPlusIdentityDerivation_smulParameter p q c hpq

public lemma oneParameterTangent_ne_zero
    {K : Variety k} [AlgebraicGroup K] (X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety) :
    oneParameterTangent X x ≠ 0 := by
  obtain ⟨F, hF⟩ :=
    oneParameterParametrization_exists_ambient_parameterPolynomial X x
  intro hzero
  have hvalue := congrArg (fun D : IdentityPointDerivation K ↦ D F) hzero
  rw [oneParameterTangent_apply, Derivation.zero_apply] at hvalue
  have hpoly : kPlusPolynomialFunctionAlgEquiv
      ((X.inclusion.comp x.hom).toVariety.pullbackAlgHom F) = Polynomial.X := by
    apply Polynomial.funext
    intro t
    rw [kPlusPolynomialFunctionAlgEquiv_eval, Polynomial.eval_X]
    change F (X.inclusion.onPoints (x.hom.onPoints (kPlusPoint t))) = t
    exact hF t
  rw [kPlusIdentityDerivation_apply, hpoly] at hvalue
  simp at hvalue

omit [IsAlgClosed k] in
lemma TorusCharacter.pointCharacter_inv_apply
    {T : Variety k} [AlgebraicGroup T]
    (χ : TorusCharacter T) (s : Variety.Point T) :
    (χ⁻¹).pointCharacter s = (χ.pointCharacter s)⁻¹ := by
  change ((dPointEquiv 1 ((χ.onPoints s)⁻¹) 0 : k)) =
    ((dPointEquiv 1 (χ.onPoints s) 0 : k))⁻¹
  have hmul := congrFun
    (dPointEquiv_mul 1 (χ.onPoints s)⁻¹ (χ.onPoints s)) 0
  rw [inv_mul_cancel, dPointEquiv_one] at hmul
  simp only [Pi.one_apply, Pi.mul_apply] at hmul
  have hu : dPointEquiv 1 ((χ.onPoints s)⁻¹) 0 =
      (dPointEquiv 1 (χ.onPoints s) 0)⁻¹ := by
    calc
    dPointEquiv 1 ((χ.onPoints s)⁻¹) 0 =
        dPointEquiv 1 ((χ.onPoints s)⁻¹) 0 *
          dPointEquiv 1 (χ.onPoints s) 0 *
            (dPointEquiv 1 (χ.onPoints s) 0)⁻¹ := by simp
    _ = 1 * (dPointEquiv 1 (χ.onPoints s) 0)⁻¹ := by rw [← hmul]
    _ = (dPointEquiv 1 (χ.onPoints s) 0)⁻¹ := one_mul _
  simpa using congrArg Units.val hu

omit [IsAlgClosed k] in
lemma TorusCharacter.pointCharacter_apply_inv
    {T : Variety k} [AlgebraicGroup T]
    (χ : TorusCharacter T) (s : Variety.Point T) :
    χ.pointCharacter s⁻¹ = (χ.pointCharacter s)⁻¹ := by
  change ((dPointEquiv 1 (χ.onPoints s⁻¹) 0 : k)) =
    ((dPointEquiv 1 (χ.onPoints s) 0 : k))⁻¹
  rw [map_inv]
  exact TorusCharacter.pointCharacter_inv_apply χ s

public lemma oneParameterTangent_isWeightVector
    {K : Variety k} [AlgebraicGroup K] (T X : ClosedSubgroup K)
    (x : OneParameterParametrization X.carrierVariety)
    {χ : TorusWeight T}
    (hχ : RootWeightEquation T X χ) :
    IsWeightVector (identityTangentRepresentation K) T
      (oneParameterTangent X x) χ⁻¹ := by
  refine ⟨oneParameterTangent_ne_zero X x, ?_⟩
  intro s
  apply Derivation.ext
  intro f
  let c : k := (χ⁻¹).pointCharacter s
  let p : Variety.PolynomialFunction (KPlus k) :=
    (X.inclusion.comp x.hom).toVariety.pullbackAlgHom f
  let q : Variety.PolynomialFunction (KPlus k) :=
    (X.inclusion.comp x.hom).toVariety.pullbackAlgHom
      ((AlgebraicGroup.conjugationByMorphism K (T.includePoint s)).pullbackAlgHom f)
  have hscale : ∀ t, q (kPlusPoint t) = p (kPlusPoint (c * t)) := by
    intro t
    change f ((AlgebraicGroup.conjugationByMorphism K (T.includePoint s)).toFun
        (X.inclusion.onPoints (x.hom.onPoints (kPlusPoint t)))) =
      f (X.inclusion.onPoints (x.hom.onPoints (kPlusPoint (c * t))))
    congr 1
    rw [AlgebraicGroup.conjugationByMorphism_apply]
    have hroot := hχ x t s⁻¹
    have hXinc (y : Variety.Point X.carrierVariety) :
        X.includePoint y = X.inclusion.onPoints y := by
      apply Variety.Point.ext
      funext i
      rfl
    have hTinc (y : Variety.Point T.carrierVariety) :
        T.includePoint y = T.inclusion.onPoints y := by
      apply Variety.Point.ext
      funext i
      rfl
    simp_rw [hXinc] at hroot
    rw [hTinc, map_inv, inv_inv] at hroot
    change T.inclusion.onPoints s *
        X.inclusion.onPoints (x.hom.onPoints (kPlusPoint t)) *
          (T.inclusion.onPoints s)⁻¹ =
      X.inclusion.onPoints
        (x.hom.onPoints (kPlusPoint (χ.pointCharacter s⁻¹ * t))) at hroot
    rw [hTinc]
    simpa [c, TorusCharacter.pointCharacter_inv_apply,
      TorusCharacter.pointCharacter_apply_inv] using hroot
  have hderiv := kPlusIdentityDerivation_smulParameter q p c hscale
  change kPlusIdentityDerivation q = c • kPlusIdentityDerivation p
  simpa only [smul_eq_mul] using hderiv

end Theory.AlgebraicGroup
