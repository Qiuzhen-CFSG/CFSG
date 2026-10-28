module

public import Mathlib.Algebra.Lie.AdjointAction.Derivation
public import Theory.AlgebraicGroup.Bor1.RepresentationDifferential
public import Theory.AlgebraicGroup.RootSubgroups.TangentLie

/-!
# The adjoint differential on the identity tangent

The Bor1 differential API and the RootSubgroups tangent API construct the same
conjugation operator on identity-point derivations.  This module records that
equality explicitly and identifies the differential of the rational
RootSubgroups conjugation representation with the canonical convolution Lie
bracket: the differential in direction `D`, applied to `E`, is `[D,E]`.

The calculation expands coordinate comultiplication twice.  Differentiating
the positive conjugation factor gives the convolution `D * E`, while the
antipode identity differentiates inversion to a minus sign and gives
`- E * D`.  This is the affine-coordinate form of Bor1 Chapter 1,
Sections 3.13--3.14, where `d(Ad)(D)` is identified with `ad D`.  It uses no
root-subgroup existence or multiplicity theorem and, in particular, no clause
of GLS3 Theorem 1.9.5.

As an immediate consequence, a tangent fixed by every Bor1 conjugation map is
central in the canonical tangent Lie algebra: all of its rational matrix
coefficients are constant, so every infinitesimal adjoint operator kills it.
The converse requires the separate characteristic-zero connected integration
of differential invariants.
-/

open scoped TensorProduct Coalgebra
open WithConv

universe u

namespace Theory.AlgebraicGroup

variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
/-- The Bor1 and RootSubgroups constructions of tangent conjugation are the
same linear map. -/
public theorem Bor1.identityTangentConjugationLinearMap_eq_root
    (G : Variety k) [AlgebraicGroup G] (g : G.Point) :
    Bor1.identityTangentConjugationLinearMap G g =
      identityTangentConjugationLinearMap G g := by
  ext D a
  rfl

private def polynomialFunctionEvaluationLinearMap
    (G : Variety k) (x : G.Point) : G.PolynomialFunction →ₗ[k] k where
  toFun := fun a => a x
  map_add' _ _ := rfl
  map_smul' c a := by
    rw [polynomialFunction_smul_apply]
    simp [smul_eq_mul]

omit [IsAlgClosed k] in
private lemma coordinateCoalgebraRepr_evaluation
    (G : Variety k) [AlgebraicGroup G]
    (a : G.PolynomialFunction) (x y : G.Point) :
    let _ : Bialgebra k G.PolynomialFunction := coordinateBialgebra G
    let r := Coalgebra.Repr.arbitrary k a
    ∑ i ∈ r.index, r.left i x * r.right i y = a (x * y) := by
  let _ : Bialgebra k G.PolynomialFunction := coordinateBialgebra G
  let r := Coalgebra.Repr.arbitrary k a
  have heval := coordinateComultiplication_apply G a x y
  have hr := r.eq
  change (∑ i ∈ r.index, r.left i ⊗ₜ[k] r.right i) =
    coordinateComultiplication G a at hr
  rw [← hr] at heval
  change polynomialFunctionEvalAddHom (G.prod G)
      ((G.prodPointEquiv G).symm (x, y))
      (polynomialFunctionTensor G G
        (∑ i ∈ r.index, r.left i ⊗ₜ[k] r.right i)) =
    a (x * y) at heval
  simpa only [map_sum, polynomialFunctionTensor_tmul,
    polynomialFunctionEvalAddHom_apply, polynomialFunctionLeft_apply,
    polynomialFunctionRight_apply, polynomialFunction_mul_apply,
    Equiv.apply_symm_apply] using heval

omit [IsAlgClosed k] in
private lemma identityPointDerivation_coordinateAntipode
    (G : Variety k) [AlgebraicGroup G]
    (D : IdentityPointDerivation G) (a : G.PolynomialFunction) :
    D (coordinateAntipode G a) = -D a := by
  let _ : Bialgebra k G.PolynomialFunction := coordinateBialgebra G
  let r := Coalgebra.Repr.arbitrary k a
  have hmul :
      ∑ i ∈ r.index, r.left i * coordinateAntipode G (r.right i) =
        algebraMap k G.PolynomialFunction (a 1) := by
    apply Variety.PolynomialFunction.ext
    intro g
    change polynomialFunctionEvaluationLinearMap G g
      (∑ i ∈ r.index,
        r.left i * coordinateAntipode G (r.right i)) = _
    rw [map_sum]
    change (∑ i ∈ r.index,
      r.left i g * coordinateAntipode G (r.right i) g) = _
    simp_rw [coordinateAntipode_apply]
    rw [polynomialFunction_algebraMap_apply]
    rw [show (∑ i ∈ r.index, r.left i g * r.right i g⁻¹) =
        a (g * g⁻¹) by
      simpa only [r] using coordinateCoalgebraRepr_evaluation G a g g⁻¹]
    simp
  have hD := congrArg D hmul
  rw [map_sum, D.map_algebraMap] at hD
  simp_rw [D.leibniz] at hD
  rw [Finset.sum_add_distrib] at hD
  change
    (∑ i ∈ r.index,
      r.left i 1 * D (coordinateAntipode G (r.right i))) +
      (∑ i ∈ r.index,
        coordinateAntipode G (r.right i) 1 * D (r.left i)) = 0 at hD
  simp only [coordinateAntipode_apply, inv_one] at hD
  have hleft :
      ∑ i ∈ r.index,
          r.left i 1 * D (coordinateAntipode G (r.right i)) =
        D (coordinateAntipode G a) := by
    have h := Coalgebra.sum_counit_tmul_map_eq
      (R := k) (D.toLinearMap.comp (coordinateAntipode G).toLinearMap)
        a (repr := r)
    have h' := congrArg (LinearMap.mul' k k) h
    have counit_apply (q : G.PolynomialFunction) :
        Coalgebra.counit (R := k) q = q 1 := rfl
    simp only [map_sum, LinearMap.mul'_apply, LinearMap.comp_apply,
      counit_apply, one_mul] at h'
    change (∑ i ∈ r.index,
      r.left i 1 * D (coordinateAntipode G (r.right i))) =
        D (coordinateAntipode G a) at h'
    exact h'
  have hright :
      ∑ i ∈ r.index,
          r.right i 1 * D (r.left i) = D a := by
    have h := Coalgebra.sum_map_tmul_counit_eq
      (R := k) D.toLinearMap a (repr := r)
    have h' := congrArg (LinearMap.mul' k k) h
    have counit_apply (q : G.PolynomialFunction) :
        Coalgebra.counit (R := k) q = q 1 := rfl
    simp only [map_sum, LinearMap.mul'_apply, counit_apply, mul_one] at h'
    change (∑ i ∈ r.index, D (r.left i) * r.right i 1) = D a at h'
    simpa only [mul_comm] using h'
  rw [hleft, hright] at hD
  exact eq_neg_of_add_eq_zero_left hD

private noncomputable def identityTangentAdjointCoefficient
    (G : Variety k) [AlgebraicGroup G]
    (E : IdentityPointDerivation G) (a : G.PolynomialFunction) :
    G.PolynomialFunction := by
  classical
  let _ : Bialgebra k G.PolynomialFunction := coordinateBialgebra G
  let r := Coalgebra.Repr.arbitrary k a
  let s (i : G.PolynomialFunction × G.PolynomialFunction) :=
    Coalgebra.Repr.arbitrary k (r.right i)
  exact ∑ i ∈ r.index, ∑ j ∈ (s i).index,
    E ((s i).left j) •
      (r.left i * coordinateAntipode G ((s i).right j))

omit [IsAlgClosed k] in
private lemma identityTangentAdjointCoefficient_apply
    (G : Variety k) [AlgebraicGroup G]
    (E : IdentityPointDerivation G) (a : G.PolynomialFunction)
    (g : G.Point) :
    identityTangentAdjointCoefficient G E a g =
      identityTangentConjugationLinearMap G g E a := by
  classical
  let _ : Bialgebra k G.PolynomialFunction := coordinateBialgebra G
  let r := Coalgebra.Repr.arbitrary k a
  let s (i : G.PolynomialFunction × G.PolynomialFunction) :=
    Coalgebra.Repr.arbitrary k (r.right i)
  have hinner (i : G.PolynomialFunction × G.PolynomialFunction)
      (x : G.Point) :
      ∑ j ∈ (s i).index, (s i).left j x * (s i).right j g⁻¹ =
        r.right i (x * g⁻¹) := by
    simpa only [s] using
      coordinateCoalgebraRepr_evaluation G (r.right i) x g⁻¹
  have houter (x : G.Point) :
      ∑ i ∈ r.index, r.left i g * r.right i (x * g⁻¹) =
        a (g * (x * g⁻¹)) := by
    simpa only [r] using coordinateCoalgebraRepr_evaluation G a g (x * g⁻¹)
  have hpull :
      (AlgebraicGroup.conjugationByMorphism G g).pullbackAlgHom a =
        ∑ i ∈ r.index, ∑ j ∈ (s i).index,
          (r.left i g * (s i).right j g⁻¹) • (s i).left j := by
    apply Variety.PolynomialFunction.ext
    intro x
    change a (g * x * g⁻¹) =
      polynomialFunctionEvaluationLinearMap G x
        (∑ i ∈ r.index, ∑ j ∈ (s i).index,
          (r.left i g * (s i).right j g⁻¹) • (s i).left j)
    calc
      a (g * x * g⁻¹) =
          ∑ i ∈ r.index, r.left i g * r.right i (x * g⁻¹) := by
        rw [show g * x * g⁻¹ = g * (x * g⁻¹) by group]
        exact (houter x).symm
      _ = ∑ i ∈ r.index, ∑ j ∈ (s i).index,
          (r.left i g * (s i).right j g⁻¹) * (s i).left j x := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← hinner i x]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = polynomialFunctionEvaluationLinearMap G x
          (∑ i ∈ r.index, ∑ j ∈ (s i).index,
            (r.left i g * (s i).right j g⁻¹) • (s i).left j) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [map_smul]
        rfl
  change polynomialFunctionEvalAddHom G g
      (∑ i ∈ r.index, ∑ j ∈ (s i).index,
        E ((s i).left j) •
          (r.left i * coordinateAntipode G ((s i).right j))) =
    E ((AlgebraicGroup.conjugationByMorphism G g).pullbackAlgHom a)
  rw [hpull]
  simp only [map_sum, polynomialFunctionEvalAddHom_apply,
    polynomialFunction_smul_apply, polynomialFunction_mul_apply,
    coordinateAntipode_apply]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [E.map_smul, smul_eq_mul]
  ring

omit [IsAlgClosed k] in
private lemma identityTangentAdjointCoefficient_derivation
    (G : Variety k) [AlgebraicGroup G]
    (D E : IdentityPointDerivation G) (a : G.PolynomialFunction) :
    D (identityTangentAdjointCoefficient G E a) =
      identityTangentBracket G D E a := by
  classical
  let _ : Bialgebra k G.PolynomialFunction := coordinateBialgebra G
  let r := Coalgebra.Repr.arbitrary k a
  let s (i : G.PolynomialFunction × G.PolynomialFunction) :=
    Coalgebra.Repr.arbitrary k (r.right i)
  have hright (i : G.PolynomialFunction × G.PolynomialFunction) :
      ∑ j ∈ (s i).index, E ((s i).left j) * (s i).right j 1 =
        E (r.right i) := by
    have h := Coalgebra.sum_map_tmul_counit_eq
      (R := k) E.toLinearMap (r.right i) (repr := s i)
    have h' := congrArg (LinearMap.mul' k k) h
    have counit_apply (q : G.PolynomialFunction) :
        Coalgebra.counit (R := k) q = q 1 := rfl
    simp only [map_sum, LinearMap.mul'_apply, counit_apply, mul_one] at h'
    change (∑ j ∈ (s i).index,
      E ((s i).left j) * (s i).right j 1) = E (r.right i) at h'
    exact h'
  have hpositive :
      ∑ i ∈ r.index, ∑ j ∈ (s i).index,
          E ((s i).left j) * ((s i).right j 1 * D (r.left i)) =
        identityTangentConvolution G D E a := by
    calc
      _ = ∑ i ∈ r.index,
          D (r.left i) *
            (∑ j ∈ (s i).index,
              E ((s i).left j) * (s i).right j 1) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ∑ i ∈ r.index, D (r.left i) * E (r.right i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hright]
      _ = identityTangentConvolution G D E a := by
        change _ =
          (toConv D.toLinearMap * toConv E.toLinearMap).ofConv a
        exact (r.convMul_apply (toConv D.toLinearMap)
          (toConv E.toLinearMap)).symm
  have hnegative :
      ∑ i ∈ r.index, ∑ j ∈ (s i).index,
          E ((s i).left j) * (r.left i 1 * D ((s i).right j)) =
        identityTangentConvolution G E D a := by
    calc
      _ = ∑ i ∈ r.index,
          r.left i 1 * identityTangentConvolution G E D (r.right i) := by
        apply Finset.sum_congr rfl
        intro i hi
        change _ = r.left i 1 *
          (toConv E.toLinearMap * toConv D.toLinearMap).ofConv (r.right i)
        rw [(s i).convMul_apply]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        rw [show (toConv E.toLinearMap).ofConv ((s i).left j) =
          E ((s i).left j) by rfl]
        rw [show (toConv D.toLinearMap).ofConv ((s i).right j) =
          D ((s i).right j) by rfl]
        ring
      _ = identityTangentConvolution G E D a := by
        have h := Coalgebra.sum_counit_tmul_map_eq
          (R := k) (identityTangentConvolution G E D) a (repr := r)
        have h' := congrArg (LinearMap.mul' k k) h
        have counit_apply (q : G.PolynomialFunction) :
            Coalgebra.counit (R := k) q = q 1 := rfl
        simp only [map_sum, LinearMap.mul'_apply, counit_apply, one_mul] at h'
        change (∑ i ∈ r.index,
          r.left i 1 * identityTangentConvolution G E D (r.right i)) =
            identityTangentConvolution G E D a at h'
        exact h'
  rw [identityTangentBracket_apply]
  rw [← hpositive, ← hnegative]
  change D (∑ i ∈ r.index, ∑ j ∈ (s i).index,
    E ((s i).left j) •
      (r.left i * coordinateAntipode G ((s i).right j))) = _
  simp only [map_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hleibniz : D
      (r.left i * coordinateAntipode G ((s i).right j)) =
      r.left i 1 * D (coordinateAntipode G ((s i).right j)) +
        coordinateAntipode G ((s i).right j) 1 * D (r.left i) :=
    D.leibniz _ _
  rw [D.map_smul, hleibniz]
  rw [identityPointDerivation_coordinateAntipode]
  rw [coordinateAntipode_apply, inv_one]
  change E ((s i).left j) *
      (r.left i 1 * -D ((s i).right j) +
        (s i).right j 1 * D (r.left i)) = _
  ring

/-- The differential of tangent conjugation is the adjoint action for the
canonical convolution Lie bracket. -/
public theorem identityTangentRepresentation_differential_apply
    (G : Variety k) [AlgebraicGroup G]
    (b : Module.Basis (Fin (Module.finrank k (IdentityPointDerivation G))) k
      (IdentityPointDerivation G))
    (f : AlgebraicGroup.Morphism G
      (glVarietyOf k (IdentityPointDerivation G)))
    (hf : ∀ g, glPointEquivOf k (IdentityPointDerivation G) b
      (f.onPoints g) = (identityTangentRepresentation G).action g)
    (D E : IdentityPointDerivation G) :
    Bor1.rationalRepresentationDifferential
        (identityTangentRepresentation G) b f D E = ⁅D, E⁆ := by
  apply Derivation.ext
  intro a
  let l : Module.Dual k (IdentityPointDerivation G) := {
    toFun := fun X => X a
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  change l (Bor1.rationalRepresentationDifferential
      (identityTangentRepresentation G) b f D E) = l ⁅D, E⁆
  rw [Bor1.rationalRepresentationDifferential_linearMatrixCoefficient]
  have hCoefficient :
      rationalRepresentationLinearMatrixCoefficient
          (identityTangentRepresentation G) b f l E =
        identityTangentAdjointCoefficient G E a := by
    apply Variety.PolynomialFunction.ext
    intro g
    rw [rationalRepresentationLinearMatrixCoefficient_apply
      (identityTangentRepresentation G) b f hf]
    rw [identityTangentAdjointCoefficient_apply]
    change (((identityTangentRepresentation G).action g).1 E) a =
      identityTangentConjugationLinearMap G g E a
    rw [identityTangentRepresentation_action_apply]
    rfl
  rw [hCoefficient]
  exact identityTangentAdjointCoefficient_derivation G D E a

/-- A pointwise fixed identity tangent is central for the canonical
convolution Lie bracket. -/
public theorem Bor1.identityTangent_pointwise_fixed_to_mem_lieCenter
    (G : Variety k) [AlgebraicGroup G]
    (D : Theory.AlgebraicGroup.IdentityPointDerivation G)
    (hD : ∀ g : G.Point,
      Bor1.identityTangentConjugationLinearMap G g D = D) :
    D ∈ LieAlgebra.center k
      (Theory.AlgebraicGroup.IdentityPointDerivation G) := by
  obtain ⟨b, f, hf⟩ :=
    Theory.AlgebraicGroup.identityTangentRepresentation_isRational G
  rw [LieModule.mem_maxTrivSubmodule]
  intro E
  rw [← Theory.AlgebraicGroup.identityTangentRepresentation_differential_apply
    G b f hf]
  apply b.ext_elem
  intro i
  change b.coord i
      (Bor1.rationalRepresentationDifferential
        (Theory.AlgebraicGroup.identityTangentRepresentation G) b f E D) =
      b.coord i 0
  rw [Bor1.rationalRepresentationDifferential_linearMatrixCoefficient]
  have hCoefficient :
      rationalRepresentationLinearMatrixCoefficient
          (Theory.AlgebraicGroup.identityTangentRepresentation G)
            b f (b.coord i) D =
        algebraMap k G.PolynomialFunction (b.coord i D) := by
    apply Variety.PolynomialFunction.ext
    intro g
    rw [rationalRepresentationLinearMatrixCoefficient_apply
      (Theory.AlgebraicGroup.identityTangentRepresentation G) b f hf]
    rw [polynomialFunction_algebraMap_apply]
    apply congrArg (b.coord i)
    apply Derivation.ext
    intro a
    rw [Theory.AlgebraicGroup.identityTangentRepresentation_action_apply]
    have hg := congrArg
      (fun X : Theory.AlgebraicGroup.IdentityPointDerivation G => X a) (hD g)
    simpa only [Bor1.identityTangentConjugationLinearMap_apply] using hg
  rw [hCoefficient, E.map_algebraMap]
  simp

end Theory.AlgebraicGroup
