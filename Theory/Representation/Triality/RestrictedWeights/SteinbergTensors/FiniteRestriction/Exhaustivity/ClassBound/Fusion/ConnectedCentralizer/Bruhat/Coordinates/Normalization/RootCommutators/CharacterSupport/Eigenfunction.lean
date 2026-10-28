module

public import Theory.Representation.Triality.RestrictedWeights.SteinbergTensors.FiniteRestriction.Exhaustivity.ClassBound.Fusion.ConnectedCentralizer.Bruhat.Coordinates.Normalization.RootCommutators.CharacterSupport.Contracts
public import Theory.AlgebraicGroup.Morphism.Operations

/-!
Equivariant extension of the exact parameter of a realized root subgroup.

Extend the affine parameter to an ambient polynomial function, then pull that
function back along inverse conjugation on `T × K`. The scalar characters form
a basis of the torus coordinate algebra. Extracting one basis coefficient in
the first factor gives a polynomial function on the second factor: this follows
from the tensor-product description of functions on an affine product.
Translation scales that coefficient by its character, and the root-weight
equation makes its restriction equal to the original affine parameter.

The argument uses regular functions, with no restriction on the characteristic.
This proves the extension contract used in the character-support geometry for
GLS3, 1.12.1(b) and 1.12.7(b), `refs/KGroup/GLS3/Chapter1.tex`.
-/

namespace Theory.AlgebraicGroup
universe u
variable {k : Type u} [Field k]
open scoped TensorProduct
open _root_.Module

private def slice (V W : Variety k) (y : Variety.Point W) :
    Variety.PolynomialFunction (Variety.prod V W) →ₐ[k]
      Variety.PolynomialFunction V :=
  ((Variety.Morphism.id V).pair (Variety.Morphism.const V W y)).pullbackAlgHom

private lemma slice_apply (V W : Variety k) (y : Variety.Point W)
    (f : Variety.PolynomialFunction (Variety.prod V W)) (x : Variety.Point V) :
    slice V W y f x = f ((Variety.prodPointEquiv V W).symm (x, y)) := rfl

/-- Applying a linear functional to the first-variable slices of a regular
function gives a regular function of the second variable. -/
private theorem exists_slice_coefficient (V W : Variety k)
    (L : Variety.PolynomialFunction V →ₗ[k] k)
    (f : Variety.PolynomialFunction (Variety.prod V W)) :
    ∃ F : Variety.PolynomialFunction W,
      ∀ y : Variety.Point W, F y = L (slice V W y f) := by
  obtain ⟨t, rfl⟩ := polynomialFunctionTensor_surjective V W f
  induction t using TensorProduct.induction_on with
  | zero =>
      refine ⟨0, ?_⟩
      intro y
      simp only [map_zero, polynomialFunction_zero_apply]
  | add a b ha hb =>
      obtain ⟨F, hF⟩ := ha
      obtain ⟨G, hG⟩ := hb
      refine ⟨F + G, ?_⟩
      intro y
      change F y + G y = _
      rw [hF, hG, map_add, map_add, map_add]
  | tmul a b =>
      refine ⟨L a • b, ?_⟩
      intro y
      have hs : slice V W y (polynomialFunctionTensor V W (a ⊗ₜ[k] b)) =
          b y • a := by
        apply Variety.PolynomialFunction.ext
        intro x
        rw [slice_apply, polynomialFunctionTensor_tmul,
          polynomialFunction_mul_apply, polynomialFunctionLeft_apply,
          polynomialFunctionRight_apply, Equiv.apply_symm_apply,
          polynomialFunction_smul_apply]
        exact mul_comm _ _
      rw [hs, map_smul, polynomialFunction_smul_apply, smul_eq_mul, mul_comm]

private noncomputable def characterBasis [IsAlgClosed k]
    (T : Variety k) [AlgebraicGroup T] (hT : IsTorus T) :
    Basis (TorusCharacter T) k (Variety.PolynomialFunction T) :=
  Basis.mk (torusCharacter_scalarPolynomialFunction_linearIndependent T)
    (by
      intro f _
      exact polynomialFunction_mem_span_scalarCharacters T hT.isMulCommutative
        (IsTorus.all_semisimple hT) f)

private theorem characterBasis_apply [IsAlgClosed k]
    (T : Variety k) [AlgebraicGroup T] (hT : IsTorus T) (chi : TorusCharacter T) :
    characterBasis T hT chi = chi.scalarPolynomialFunction :=
  Basis.mk_apply _ _ _

/-- Translation multiplies a character coefficient by that character's value. -/
private theorem characterCoefficient_leftMul [IsAlgClosed k]
    (T : Variety k) [AlgebraicGroup T] (hT : IsTorus T)
    (chi : TorusCharacter T) (s : Variety.Point T)
    (p : Variety.PolynomialFunction T) :
    (characterBasis T hT).coord chi ((leftMulMorphism T s).pullbackAlgHom p) =
      chi.pointCharacter s * (characterBasis T hT).coord chi p := by
  classical
  let L := (characterBasis T hT).coord chi
  have hcoord (eta : TorusCharacter T) :
      L eta.scalarPolynomialFunction = if eta = chi then 1 else 0 := by
    change (characterBasis T hT).coord chi eta.scalarPolynomialFunction = _
    rw [← characterBasis_apply T hT eta, Basis.coord_apply, Basis.repr_self_apply]
  change L ((leftMulMorphism T s).pullbackAlgHom p) = chi.pointCharacter s * L p
  have hp := polynomialFunction_mem_span_scalarCharacters T hT.isMulCommutative
    (IsTorus.all_semisimple hT) p
  induction hp using Submodule.span_induction with
  | mem p hp =>
      obtain ⟨eta, rfl⟩ := hp
      have he : (leftMulMorphism T s).pullbackAlgHom eta.scalarPolynomialFunction =
          eta.pointCharacter s • eta.scalarPolynomialFunction := by
        apply Variety.PolynomialFunction.ext
        intro t
        change eta.scalarPolynomialFunction ((leftMulMorphism T s).toFun t) = _
        rw [leftMulMorphism_apply, polynomialFunction_smul_apply,
          TorusCharacter.scalarPolynomialFunction_apply,
          TorusCharacter.scalarPolynomialFunction_apply, map_mul]
      rw [he, map_smul, smul_eq_mul, hcoord]
      split_ifs with h
      · subst eta
        rfl
      · simp only [mul_zero]
  | zero => simp only [map_zero, mul_zero]
  | add a b ha hb hla hlb =>
      rw [map_add, map_add, map_add, hla, hlb, mul_add]
  | smul a p hp ih =>
      rw [map_smul, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ih]
      ring

private def inverseConjugationFamily
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K) :
    Variety.Morphism (Variety.prod T.carrierVariety K) K :=
  let s := T.inclusion.toVariety.comp (Variety.Morphism.fst T.carrierVariety K)
  let g := Variety.Morphism.snd T.carrierVariety K
  (mulMorphism K).comp
    (((mulMorphism K).comp (((invMorphism K).comp s).pair g)).pair s)

private theorem inverseConjugationFamily_apply
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (s : Variety.Point T.carrierVariety) (g : Variety.Point K) :
    (inverseConjugationFamily T).toFun
        ((Variety.prodPointEquiv T.carrierVariety K).symm (s, g)) =
      (T.includePoint s)⁻¹ * g * T.includePoint s := by
  simp only [inverseConjugationFamily, Variety.Morphism.comp,
    Variety.Morphism.pair, mulMorphism, invMorphism, Variety.Morphism.fst,
    Variety.Morphism.snd, Equiv.apply_symm_apply]
  rfl

private theorem conjugation_slice_apply
    {K : Variety k} [AlgebraicGroup K] (T : ClosedSubgroup K)
    (f : Variety.PolynomialFunction K)
    (g : Variety.Point K) (s : Variety.Point T.carrierVariety) :
    slice T.carrierVariety K g ((inverseConjugationFamily T).pullbackAlgHom f) s =
      f ((T.includePoint s)⁻¹ * g * T.includePoint s) := by
  rw [slice_apply]
  change f ((inverseConjugationFamily T).toFun _) = _
  rw [inverseConjugationFamily_apply]

/-- Every affine parametrization of a realized root subgroup extends to an
ambient polynomial eigenfunction for the inverse-conjugation torus action. -/
public theorem rootParameterEigenfunctionExtension_of_realization
    [IsAlgClosed k] {K : Variety k} [AlgebraicGroup K]
    {T : ClosedSubgroup K} (hT : IsSubtorus T)
    (D : RootGroupData K T) (hD : D.IsRealization) :
    RootParameterEigenfunctionExtension D := by
  classical
  intro c x
  obtain ⟨f, hf⟩ := oneParameterParametrization_exists_ambient_parameterPolynomial
    (D.rootSubgroup c) x
  let chi := D.rootWeight c
  let L := (characterBasis T.carrierVariety hT).coord chi
  let q := (inverseConjugationFamily T).pullbackAlgHom f
  obtain ⟨F, hF⟩ := exists_slice_coefficient T.carrierVariety K L q
  refine ⟨F, ?_, ?_⟩
  · intro z
    have hs : slice T.carrierVariety K
        ((D.rootSubgroup c).includePoint (x.value z)) q =
        z • chi.scalarPolynomialFunction := by
      apply Variety.PolynomialFunction.ext
      intro s
      rw [conjugation_slice_apply, (hD.2.2.1 c).2 x z s, hf,
        polynomialFunction_smul_apply, TorusCharacter.scalarPolynomialFunction_apply]
      exact mul_comm _ _
    rw [hF, hs, map_smul]
    have hL : L chi.scalarPolynomialFunction = 1 := by
      change (characterBasis T.carrierVariety hT).coord chi chi.scalarPolynomialFunction = 1
      rw [← characterBasis_apply T.carrierVariety hT chi,
        Basis.coord_apply, Basis.repr_self_apply]
      simp
    rw [hL, smul_eq_mul, mul_one]
  · intro s g
    have hs : slice T.carrierVariety K ((T.includePoint s)⁻¹ * g * T.includePoint s) q =
        (leftMulMorphism T.carrierVariety s).pullbackAlgHom
          (slice T.carrierVariety K g q) := by
      apply Variety.PolynomialFunction.ext
      intro t
      change slice T.carrierVariety K ((T.includePoint s)⁻¹ * g * T.includePoint s) q t =
        slice T.carrierVariety K g q ((leftMulMorphism T.carrierVariety s).toFun t)
      rw [leftMulMorphism_apply, conjugation_slice_apply, conjugation_slice_apply]
      have hmul : T.includePoint (s * t) = T.includePoint s * T.includePoint t :=
        T.inclusion.map_mul s t
      rw [hmul, mul_inv_rev]
      simp only [mul_assoc]
    rw [hF, hs, hF]
    exact characterCoefficient_leftMul T.carrierVariety hT chi s _

end Theory.AlgebraicGroup
