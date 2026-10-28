module

public import Mathlib.RingTheory.Bialgebra.Convolution
public import Theory.AlgebraicGroup.CoordinateRing.Hopf.Bialgebra
public import Theory.AlgebraicGroup.RootSubgroups.Tangent

/-!
# The Lie algebra of an algebraic group at the identity

The identity tangent of an affine algebraic group is the space of derivations
of its coordinate algebra into the residue field at the identity.  This module
equips that space with its canonical Lie bracket: embed point derivations in
the convolution algebra dual to coordinate comultiplication and take the
commutator.  A four-term product formula proves that the commutator is again a
point derivation.  Associativity of convolution then supplies the Jacobi
identity, and scalar compatibility makes the tangent a finite-dimensional Lie
algebra.

The construction is functorial for algebraic-group morphisms.  In particular,
the differential of a closed-subgroup inclusion identifies its tangent with a
Lie subalgebra of the ambient tangent.  For a torus this gives the canonical
toral Lie subalgebra used to compare conjugation weights with Lie root spaces.
The construction uses only the coordinate Hopf operations and no root-subgroup
existence, uniqueness, or multiplicity result.
-/

open scoped TensorProduct
open scoped Coalgebra
open WithConv

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

/-! ## Convolution -/

/-- The convolution product of two identity-point derivations, regarded as a
linear functional on the coordinate algebra. -/
@[expose]
public noncomputable def identityTangentConvolution
    (K : Variety k) [AlgebraicGroup K]
    (D E : IdentityPointDerivation K) :
    Variety.PolynomialFunction K →ₗ[k] k := by
  let _ : Bialgebra k (Variety.PolynomialFunction K) :=
    coordinateBialgebra K
  exact (toConv D.toLinearMap * toConv E.toLinearMap).ofConv

omit [IsAlgClosed k] in
private theorem identityTangentConvolution_mul
    (K : Variety k) [AlgebraicGroup K]
    (D E : IdentityPointDerivation K)
    (a b : Variety.PolynomialFunction K) :
    identityTangentConvolution K D E (a * b) =
      a 1 * identityTangentConvolution K D E b +
      b 1 * identityTangentConvolution K D E a +
        D a * E b + E a * D b := by
  let _ : Bialgebra k (Variety.PolynomialFunction K) :=
    coordinateBialgebra K
  let ra := Coalgebra.Repr.arbitrary k a
  let rb := Coalgebra.Repr.arbitrary k b
  change
    (toConv D.toLinearMap * toConv E.toLinearMap).ofConv (a * b) =
      a 1 * (toConv D.toLinearMap * toConv E.toLinearMap).ofConv b +
      b 1 * (toConv D.toLinearMap * toConv E.toLinearMap).ofConv a +
        D a * E b + E a * D b
  rw [(ra.mul rb).convMul_apply, ra.convMul_apply, rb.convMul_apply]
  simp only [Coalgebra.Repr.mul_index, Coalgebra.Repr.mul_left,
    Coalgebra.Repr.mul_right, Finset.sum_product]
  change
    (∑ x ∈ ra.index, ∑ y ∈ rb.index,
      D (ra.left x * rb.left y) * E (ra.right x * rb.right y)) =
      a 1 * (∑ y ∈ rb.index, D (rb.left y) * E (rb.right y)) +
      b 1 * (∑ x ∈ ra.index, D (ra.left x) * E (ra.right x)) +
        D a * E b + E a * D b
  have hD (p q : Variety.PolynomialFunction K) :
      D (p * q) = p 1 * D q + q 1 * D p := D.leibniz p q
  have hE (p q : Variety.PolynomialFunction K) :
      E (p * q) = p 1 * E q + q 1 * E p := E.leibniz p q
  simp_rw [hD, hE]
  change
    (∑ x ∈ ra.index, ∑ y ∈ rb.index,
      (ra.left x 1 * D (rb.left y) + rb.left y 1 * D (ra.left x)) *
        (ra.right x 1 * E (rb.right y) + rb.right y 1 * E (ra.right x))) = _
  have sum_counit_mul_map
      {c : Variety.PolynomialFunction K} {ι : Type u}
      (r : Coalgebra.Repr k c ι)
      (f : Variety.PolynomialFunction K →ₗ[k] k) :
      ∑ x ∈ r.index, r.left x 1 * f (r.right x) = f c := by
    have h := Coalgebra.sum_counit_tmul_map_eq (R := k) f c (repr := r)
    have h' := congrArg (LinearMap.mul' k k) h
    have counit_apply (q : Variety.PolynomialFunction K) :
        Coalgebra.counit (R := k) q = q 1 := rfl
    simpa only [map_sum, LinearMap.mul'_apply, one_mul, counit_apply] using h'
  have sum_map_mul_counit
      {c : Variety.PolynomialFunction K} {ι : Type u}
      (r : Coalgebra.Repr k c ι)
      (f : Variety.PolynomialFunction K →ₗ[k] k) :
      ∑ x ∈ r.index, f (r.left x) * r.right x 1 = f c := by
    have h := Coalgebra.sum_map_tmul_counit_eq (R := k) f c (repr := r)
    have h' := congrArg (LinearMap.mul' k k) h
    have counit_apply (q : Variety.PolynomialFunction K) :
        Coalgebra.counit (R := k) q = q 1 := rfl
    simpa only [map_sum, LinearMap.mul'_apply, mul_one, counit_apply] using h'
  have sum_eval_mul_eval
      {c : Variety.PolynomialFunction K} {ι : Type u}
      (r : Coalgebra.Repr k c ι) :
      ∑ x ∈ r.index, r.left x 1 * r.right x 1 = c 1 := by
    simpa only [AlgHom.toLinearMap_apply, coordinateCounit_apply] using
      (sum_counit_mul_map r (coordinateCounit K).toLinearMap)
  have sum_product
      {ι κ : Type u} (s : Finset ι) (t : Finset κ)
      (p r : ι → k) (q u : κ → k) :
      (∑ x ∈ s, ∑ y ∈ t, p x * q y * (r x * u y)) =
        (∑ x ∈ s, p x * r x) * (∑ y ∈ t, q y * u y) := by
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro y hy
    ring
  have h1 :
      (∑ x ∈ ra.index, ∑ y ∈ rb.index,
        ra.left x 1 * D (rb.left y) * (ra.right x 1 * E (rb.right y))) =
          a 1 * (∑ y ∈ rb.index, D (rb.left y) * E (rb.right y)) := by
    calc
      _ = (∑ x ∈ ra.index, ra.left x 1 * ra.right x 1) *
          (∑ y ∈ rb.index, D (rb.left y) * E (rb.right y)) :=
        sum_product ra.index rb.index
          (fun x => ra.left x 1) (fun x => ra.right x 1)
          (fun y => D (rb.left y)) (fun y => E (rb.right y))
      _ = _ := by rw [sum_eval_mul_eval ra]
  have h2 :
      (∑ x ∈ ra.index, ∑ y ∈ rb.index,
        rb.left y 1 * D (ra.left x) * (ra.right x 1 * E (rb.right y))) =
          D a * E b := by
    calc
      _ = ∑ x ∈ ra.index, ∑ y ∈ rb.index,
          D (ra.left x) * rb.left y 1 * (ra.right x 1 * E (rb.right y)) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = (∑ x ∈ ra.index, D (ra.left x) * ra.right x 1) *
          (∑ y ∈ rb.index, rb.left y 1 * E (rb.right y)) :=
        sum_product ra.index rb.index
          (fun x => D (ra.left x)) (fun x => ra.right x 1)
          (fun y => rb.left y 1) (fun y => E (rb.right y))
      _ = _ := by
        exact congrArg₂ (· * ·)
          (sum_map_mul_counit ra D.toLinearMap)
          (sum_counit_mul_map rb E.toLinearMap)
  have h3 :
      (∑ x ∈ ra.index, ∑ y ∈ rb.index,
        ra.left x 1 * D (rb.left y) * (rb.right y 1 * E (ra.right x))) =
          E a * D b := by
    calc
      _ = ∑ x ∈ ra.index, ∑ y ∈ rb.index,
          ra.left x 1 * D (rb.left y) * (E (ra.right x) * rb.right y 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = (∑ x ∈ ra.index, ra.left x 1 * E (ra.right x)) *
          (∑ y ∈ rb.index, D (rb.left y) * rb.right y 1) :=
        sum_product ra.index rb.index
          (fun x => ra.left x 1) (fun x => E (ra.right x))
          (fun y => D (rb.left y)) (fun y => rb.right y 1)
      _ = _ := by
        exact congrArg₂ (· * ·)
          (sum_counit_mul_map ra E.toLinearMap)
          (sum_map_mul_counit rb D.toLinearMap)
  have h4 :
      (∑ x ∈ ra.index, ∑ y ∈ rb.index,
        rb.left y 1 * D (ra.left x) * (rb.right y 1 * E (ra.right x))) =
          (∑ x ∈ ra.index, D (ra.left x) * E (ra.right x)) * b 1 := by
    calc
      _ = ∑ x ∈ ra.index, ∑ y ∈ rb.index,
          D (ra.left x) * rb.left y 1 * (E (ra.right x) * rb.right y 1) := by
        apply Finset.sum_congr rfl
        intro x hx
        apply Finset.sum_congr rfl
        intro y hy
        ring
      _ = (∑ x ∈ ra.index, D (ra.left x) * E (ra.right x)) *
          (∑ y ∈ rb.index, rb.left y 1 * rb.right y 1) :=
        sum_product ra.index rb.index
          (fun x => D (ra.left x)) (fun x => E (ra.right x))
          (fun y => rb.left y 1) (fun y => rb.right y 1)
      _ = _ := by rw [sum_eval_mul_eval rb]
  simp_rw [mul_add, add_mul]
  simp only [Finset.sum_add_distrib]
  rw [h1, h2, h3, h4]
  ring

/-- The canonical bracket on identity-point derivations, obtained as the
commutator in the convolution algebra. -/
@[expose]
public noncomputable def identityTangentBracket
    (K : Variety k) [AlgebraicGroup K]
    (D E : IdentityPointDerivation K) : IdentityPointDerivation K :=
  Derivation.mk'
    (identityTangentConvolution K D E - identityTangentConvolution K E D)
    (by
      intro a b
      change
        identityTangentConvolution K D E (a * b) -
            identityTangentConvolution K E D (a * b) =
          a 1 * (identityTangentConvolution K D E b -
            identityTangentConvolution K E D b) +
          b 1 * (identityTangentConvolution K D E a -
            identityTangentConvolution K E D a)
      rw [identityTangentConvolution_mul, identityTangentConvolution_mul]
      ring)

omit [IsAlgClosed k] in
@[simp]
public theorem identityTangentBracket_apply
    (K : Variety k) [AlgebraicGroup K]
    (D E : IdentityPointDerivation K) (a : Variety.PolynomialFunction K) :
    identityTangentBracket K D E a =
      identityTangentConvolution K D E a -
        identityTangentConvolution K E D a := rfl

section LieStructure

variable (K : Variety k) [AlgebraicGroup K]

noncomputable local instance : Bialgebra k (Variety.PolynomialFunction K) :=
  coordinateBialgebra K

private abbrev TangentConvolutionAlgebra :=
  WithConv (Variety.PolynomialFunction K →ₗ[k] k)

private noncomputable def identityTangentToConvolution :
    IdentityPointDerivation K →ₗ[k] TangentConvolutionAlgebra K where
  toFun D := toConv D.toLinearMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

omit [IsAlgClosed k] in
private theorem identityTangentToConvolution_injective :
    Function.Injective (identityTangentToConvolution K) := by
  intro D E h
  apply Derivation.ext
  intro a
  exact congrArg (fun F : TangentConvolutionAlgebra K => F a) h

/-- The bracket operation underlying the canonical identity-tangent Lie
algebra. -/
public noncomputable instance identityTangentBracketInst :
    Bracket (IdentityPointDerivation K) (IdentityPointDerivation K) :=
  ⟨identityTangentBracket K⟩

omit [IsAlgClosed k] in
private theorem identityTangentToConvolution_map_bracket
    (D E : IdentityPointDerivation K) :
    identityTangentToConvolution K ⁅D, E⁆ =
      identityTangentToConvolution K D * identityTangentToConvolution K E -
        identityTangentToConvolution K E * identityTangentToConvolution K D := by
  apply WithConv.ext
  apply LinearMap.ext
  intro a
  exact identityTangentBracket_apply K D E a

/-- The canonical Lie-ring structure on the identity tangent of an algebraic
group. -/
public noncomputable instance identityTangentLieRing :
    LieRing (IdentityPointDerivation K) where
  add_lie D E F := by
    apply identityTangentToConvolution_injective K
    simp only [identityTangentToConvolution_map_bracket, map_add, add_mul, mul_add]
    abel
  lie_add D E F := by
    apply identityTangentToConvolution_injective K
    simp only [identityTangentToConvolution_map_bracket, map_add, add_mul, mul_add]
    abel
  lie_self D := by
    apply identityTangentToConvolution_injective K
    simp only [identityTangentToConvolution_map_bracket, sub_self, map_zero]
  leibniz_lie D E F := by
    apply identityTangentToConvolution_injective K
    simp only [identityTangentToConvolution_map_bracket, map_add,
      mul_sub_left_distrib, mul_sub_right_distrib, mul_assoc]
    abel

/-- The canonical finite-dimensional Lie algebra on the identity tangent of
an algebraic group. -/
public noncomputable instance identityTangentLieAlgebra :
    LieAlgebra k (IdentityPointDerivation K) where
  lie_smul t D E := by
    apply identityTangentToConvolution_injective K
    simp only [identityTangentToConvolution_map_bracket, map_smul,
      Algebra.smul_mul_assoc, Algebra.mul_smul_comm, smul_sub]

end LieStructure

/-! ## Functoriality -/

omit [IsAlgClosed k] in
private theorem identityTangentConvolution_map
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K)
    (D E : IdentityPointDerivation H) :
    (identityTangentConvolution H D E).comp
        f.toVariety.pullbackAlgHom.toLinearMap =
      identityTangentConvolution K
        (identityTangentMorphismLinearMap f D)
        (identityTangentMorphismLinearMap f E) := by
  let _ : Bialgebra k (Variety.PolynomialFunction H) := coordinateBialgebra H
  let _ : Bialgebra k (Variety.PolynomialFunction K) := coordinateBialgebra K
  let pb : Variety.PolynomialFunction K →ₐc[k]
      Variety.PolynomialFunction H := by
    apply BialgHom.ofAlgHom f.toVariety.pullbackAlgHom
    · apply AlgHom.ext
      intro a
      change a (f.onPoints 1) = a 1
      rw [map_one]
    · apply AlgHom.ext
      intro a
      apply polynomialFunctionTensor_injective H H
      apply Variety.PolynomialFunction.ext
      intro z
      let xy := Variety.prodPointEquiv H H z
      generalize hxy : xy = p
      obtain ⟨x, y⟩ := p
      have hz : z = (Variety.prodPointEquiv H H).symm (x, y) := by
        apply (Variety.prodPointEquiv H H).injective
        change xy = (x, y)
        exact hxy
      rw [hz]
      have hmap (t : Variety.PolynomialFunction K ⊗[k]
          Variety.PolynomialFunction K) :
          polynomialFunctionTensor H H
              (Algebra.TensorProduct.map f.toVariety.pullbackAlgHom
                f.toVariety.pullbackAlgHom t)
              ((Variety.prodPointEquiv H H).symm (x, y)) =
            polynomialFunctionTensor K K t
              ((Variety.prodPointEquiv K K).symm
                (f.onPoints x, f.onPoints y)) := by
        induction t using TensorProduct.induction_on with
        | zero => simp
        | add s t hs ht =>
            simpa [map_add, Variety.PolynomialFunction.toFun] using
              congrArg₂ (· + ·) hs ht
        | tmul g h =>
            rw [Algebra.TensorProduct.map_tmul, polynomialFunctionTensor_tmul,
              polynomialFunctionTensor_tmul]
            rfl
      change polynomialFunctionTensor H H
          (Algebra.TensorProduct.map f.toVariety.pullbackAlgHom
            f.toVariety.pullbackAlgHom (coordinateComultiplication K a)) _ =
        polynomialFunctionTensor H H
          (coordinateComultiplication H (f.toVariety.pullbackAlgHom a)) _
      rw [hmap, coordinateComultiplication_apply,
        coordinateComultiplication_apply]
      change a (f.onPoints x * f.onPoints y) = a (f.onPoints (x * y))
      rw [f.onPoints.map_mul]
  change ((toConv D.toLinearMap * toConv E.toLinearMap).ofConv).comp
      f.toVariety.pullbackAlgHom.toLinearMap =
    (toConv (identityTangentMorphismLinearMap f D).toLinearMap *
      toConv (identityTangentMorphismLinearMap f E).toLinearMap).ofConv
  have hpb : pb.toLinearMap = f.toVariety.pullbackAlgHom.toLinearMap := rfl
  rw [← hpb]
  rw [LinearMap.convMul_comp_coalgHom_distrib
    (toConv D.toLinearMap) (toConv E.toLinearMap) pb.toCoalgHom]
  rfl

/-- The identity differential of an algebraic-group morphism, as a homomorphism
of the canonical tangent Lie algebras. -/
@[expose]
public noncomputable def identityTangentMorphismLieHom
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K) :
    IdentityPointDerivation H →ₗ⁅k⁆ IdentityPointDerivation K where
  __ := identityTangentMorphismLinearMap f
  map_lie' := by
    intro D E
    apply Derivation.ext
    intro a
    change
      identityTangentConvolution H D E (f.toVariety.pullbackAlgHom a) -
          identityTangentConvolution H E D (f.toVariety.pullbackAlgHom a) =
        identityTangentConvolution K
            (identityTangentMorphismLinearMap f D)
            (identityTangentMorphismLinearMap f E) a -
          identityTangentConvolution K
            (identityTangentMorphismLinearMap f E)
            (identityTangentMorphismLinearMap f D) a
    rw [← identityTangentConvolution_map f D E,
      ← identityTangentConvolution_map f E D]
    rfl

omit [IsAlgClosed k] in
@[simp]
public theorem identityTangentMorphismLieHom_apply
    {H K : Variety k} [AlgebraicGroup H] [AlgebraicGroup K]
    (f : AlgebraicGroup.Morphism H K) (D : IdentityPointDerivation H) :
    identityTangentMorphismLieHom f D = identityTangentMorphismLinearMap f D := rfl

omit [IsAlgClosed k] in
public theorem identityTangentMorphismLieHom_inclusion_injective
    {K : Variety k} [AlgebraicGroup K] (H : ClosedSubgroup K) :
    Function.Injective (identityTangentMorphismLieHom H.inclusion) := by
  change Function.Injective (identityTangentMorphismLinearMap H.inclusion)
  exact identityTangentMorphismLinearMap_inclusion_injective H

end Theory.AlgebraicGroup
