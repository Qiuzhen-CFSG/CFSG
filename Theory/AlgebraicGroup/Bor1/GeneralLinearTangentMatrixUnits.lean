module

public import Mathlib.LinearAlgebra.Transvection.Basic
public import Theory.AlgebraicGroup.Bor1.GeneralLinearTangentCoordinates
public import Theory.AlgebraicGroup.Bor1.TangentDimension
public import Theory.AlgebraicGroup.Dimension.Torus
public import Theory.AlgebraicGroup.PluckerOrbit.Conjugation
public import Theory.AlgebraicGroup.Representations.DiagonalBasis

/-!
# Matrix units in the general-linear identity tangent

Every matrix unit lies in the range of matrix-coordinate differentiation.
Diagonal units come from identity tangents of the diagonal torus. Conjugating
one diagonal tangent by elementary transvections and taking differences
produces the off-diagonal units, which span all endomorphisms.

This proves the surjective half of the general-linear tangent identification.
The diagonal-curve certificate and conjugation formula are exported so that
closed matrix subgroups can reuse the same explicit tangent generators.
-/

open scoped BigOperators

universe u v

namespace Theory.AlgebraicGroup.Bor1

open Theory.AlgebraicGroup

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

variable {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
variable {V : Type v} [AddCommGroup V] [Module k V] [FiniteDimensional k V]

private noncomputable def diagonalIdentityTangentCoordinateLinearMap (n : Nat) :
    IdentityPointDerivation (dVariety k n) →ₗ[k] (Fin n → k) where
  toFun D i := D (Variety.PolynomialFunction.ofPolynomial (dVariety k n)
    (MvPolynomial.X (Sum.inl (ULift.up i))))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private noncomputable def dPositiveCoordinate (n : Nat) (i : Fin n) :
    Variety.PolynomialFunction (dVariety k n) :=
  Variety.PolynomialFunction.ofPolynomial (dVariety k n)
    (MvPolynomial.X (Sum.inl (ULift.up i)))

private noncomputable def dNegativeCoordinate (n : Nat) (i : Fin n) :
    Variety.PolynomialFunction (dVariety k n) :=
  Variety.PolynomialFunction.ofPolynomial (dVariety k n)
    (MvPolynomial.X (Sum.inr (ULift.up i)))

private lemma dPositiveCoordinate_mul_negative (n : Nat) (i : Fin n) :
    dPositiveCoordinate (k := k) n i * dNegativeCoordinate n i = 1 := by
  apply Variety.PolynomialFunction.ext
  intro x
  simp only [dPositiveCoordinate,
    dNegativeCoordinate, Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun, evalPolynomial, MvPolynomial.eval₂_X]
  change dPointEntry n x i * dPointEntryInv n x i = 1
  exact dPoint_entry_mul_inv n x i

private lemma dPositiveCoordinate_one (n : Nat) (i : Fin n) :
    dPositiveCoordinate (k := k) n i (1 : Variety.Point (dVariety k n)) = 1 := by
  simp only [dPositiveCoordinate, Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun, evalPolynomial, MvPolynomial.eval₂_X]
  change dPointEntry n (1 : Variety.Point (dVariety k n)) i = 1
  exact congrArg Units.val (congrFun (dPointEquiv_one (k := k) n) i)

private lemma dNegativeCoordinate_one (n : Nat) (i : Fin n) :
    dNegativeCoordinate (k := k) n i (1 : Variety.Point (dVariety k n)) = 1 := by
  simp only [dNegativeCoordinate, Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun, evalPolynomial, MvPolynomial.eval₂_X]
  change dPointEntryInv n (1 : Variety.Point (dVariety k n)) i = 1
  have h := dPoint_entry_mul_inv n (1 : Variety.Point (dVariety k n)) i
  have hp : dPointEntry n (1 : Variety.Point (dVariety k n)) i = 1 :=
    congrArg Units.val (congrFun (dPointEquiv_one (k := k) n) i)
  rw [hp, one_mul] at h
  exact h

private lemma diagonalIdentityTangentCoordinateLinearMap_injective (n : Nat) :
    Function.Injective (diagonalIdentityTangentCoordinateLinearMap (k := k) n) := by
  intro D E hDE
  apply coordinateTangentMap_injective (dVariety k n)
  funext c
  cases c with
  | inl i =>
      change D (dPositiveCoordinate n i.down) = E (dPositiveCoordinate n i.down)
      exact congrFun hDE i.down
  | inr i =>
      change D (dNegativeCoordinate n i.down) = E (dNegativeCoordinate n i.down)
      have hD := congrArg D (dPositiveCoordinate_mul_negative (k := k) n i.down)
      have hE := congrArg E (dPositiveCoordinate_mul_negative (k := k) n i.down)
      rw [D.leibniz, D.map_one_eq_zero] at hD
      rw [E.leibniz, E.map_one_eq_zero] at hE
      change dPositiveCoordinate n i.down 1 * D (dNegativeCoordinate n i.down) +
        dNegativeCoordinate n i.down 1 * D (dPositiveCoordinate n i.down) = 0 at hD
      change dPositiveCoordinate n i.down 1 * E (dNegativeCoordinate n i.down) +
        dNegativeCoordinate n i.down 1 * E (dPositiveCoordinate n i.down) = 0 at hE
      rw [dPositiveCoordinate_one, dNegativeCoordinate_one] at hD hE
      simp only [one_mul] at hD hE
      have hpos : D (dPositiveCoordinate n i.down) =
          E (dPositiveCoordinate n i.down) := congrFun hDE i.down
      linear_combination hD - hE - hpos

private lemma diagonalIdentityTangentCoordinateLinearMap_bijective (n : Nat) :
    Function.Bijective (diagonalIdentityTangentCoordinateLinearMap (k := k) n) := by
  refine ⟨diagonalIdentityTangentCoordinateLinearMap_injective n, ?_⟩
  have hdim :
      Module.finrank k (IdentityPointDerivation (dVariety k n)) =
        Module.finrank k (Fin n → k) := by
    rw [identityPointDerivation_finrank_eq_dimension, dVariety_dimension_eq,
      Cardinal.toNat_natCast]
    simp
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp
    (diagonalIdentityTangentCoordinateLinearMap_injective n)

private noncomputable def diagonalIdentityTangent (n : Nat) (i : Fin n) :
    IdentityPointDerivation (dVariety k n) :=
  (LinearEquiv.ofBijective
    (diagonalIdentityTangentCoordinateLinearMap (k := k) n)
    (diagonalIdentityTangentCoordinateLinearMap_bijective n)).symm
      (Pi.single i 1)

private lemma diagonalIdentityTangent_coordinate (n : Nat) (i j : Fin n) :
    diagonalIdentityTangentCoordinateLinearMap (k := k) n
      (diagonalIdentityTangent n i) j = if i = j then 1 else 0 := by
  simp [diagonalIdentityTangent, Pi.single_apply, eq_comm]

private noncomputable def chosenBasisDiagonalMorphism
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    AlgebraicGroup.Morphism (dVariety k (Module.finrank k V))
      (glVarietyOf k V) :=
  Classical.choose (exists_basisDiagonalMorphism b)

private lemma chosenBasisDiagonalMorphism_action_basis
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (dVariety k (Module.finrank k V)))
    (i : Fin (Module.finrank k V)) :
    ((glPointEquivOf k V b ((chosenBasisDiagonalMorphism b).onPoints x) :
      LinearMap.GeneralLinearGroup k V) : Module.End k V) (b i) =
        dPointEntry (Module.finrank k V) x i • b i :=
  (Classical.choose_spec (exists_basisDiagonalMorphism b)).2 x i

private lemma chosenBasisDiagonalMorphism_tangent_matrixUnit
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (i : Fin (Module.finrank k V)) :
    generalLinearIdentityTangentLinearMap b
        (identityTangentMorphismLinearMap (chosenBasisDiagonalMorphism b)
          (diagonalIdentityTangent (Module.finrank k V) i)) =
      b.end (i, i) := by
  classical
  apply LinearMap.ext_on b.span_eq
  rintro _ ⟨q, rfl⟩
  apply b.ext_elem
  intro p
  change b.coord p
      (generalLinearIdentityTangentLinearMap b
        (identityTangentMorphismLinearMap (chosenBasisDiagonalMorphism b)
          (diagonalIdentityTangent (Module.finrank k V) i)) (b q)) = _
  rw [generalLinearIdentityTangentLinearMap_apply_basis_coord,
    identityTangentMorphismLinearMap_apply]
  have hpull :
      (chosenBasisDiagonalMorphism b).toVariety.pullbackAlgHom
          (generalLinearMatrixCoordinateOf V p q) =
        if p = q then dPositiveCoordinate (Module.finrank k V) q else 0 := by
    apply Variety.PolynomialFunction.ext
    intro x
    change generalLinearMatrixCoordinate (Module.finrank k V) p q
      ((chosenBasisDiagonalMorphism b).onPoints x) = _
    rw [show generalLinearMatrixCoordinate (Module.finrank k V) p q
        ((chosenBasisDiagonalMorphism b).onPoints x) =
          generalLinearMatrixCoordinateOf V p q
            ((chosenBasisDiagonalMorphism b).onPoints x) by rfl,
      generalLinearMatrixCoordinateOf_eq_basis_coord b,
      chosenBasisDiagonalMorphism_action_basis]
    by_cases hpq : p = q
    · subst p
      simp only [if_pos, map_smul, Module.Basis.coord_apply,
        Module.Basis.repr_self, Finsupp.single_eq_same]
      simp only [smul_eq_mul, mul_one, dPositiveCoordinate, dPointEntry,
        Variety.PolynomialFunction.ofPolynomial,
        Variety.PolynomialFunction.toFun, evalPolynomial,
        MvPolynomial.eval₂_X]
    · simp only [if_neg hpq, polynomialFunction_zero_apply, map_smul,
        Module.Basis.coord_apply, Module.Basis.repr_self]
      rw [Finsupp.single_eq_of_ne hpq]
      simp
  rw [hpull]
  by_cases hpq : p = q
  · subst p
    rw [if_pos rfl]
    change diagonalIdentityTangentCoordinateLinearMap (k := k)
      (Module.finrank k V) (diagonalIdentityTangent (Module.finrank k V) i) q = _
    rw [diagonalIdentityTangent_coordinate]
    by_cases hiq : i = q
    · subst i
      simp [Module.Basis.end_apply_apply]
    · simp [Module.Basis.end_apply_apply, hiq]
  · rw [if_neg hpq, map_zero]
    by_cases hiq : i = q
    · subst i
      simp [Module.Basis.end_apply_apply, hpq]
    · simp [Module.Basis.end_apply_apply, hiq]

private noncomputable def generalLinearPointMulEquivOf
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Variety.Point (glVarietyOf k V) ≃*
      LinearMap.GeneralLinearGroup k V := by
  let eGL : GL (Fin (Module.finrank k V)) k ≃*
      LinearMap.GeneralLinearGroup k
        (Fin (Module.finrank k V) → k) :=
    Matrix.GeneralLinearGroup.toLin
  let eLin : LinearMap.GeneralLinearGroup k
      (Fin (Module.finrank k V) → k) ≃*
        LinearMap.GeneralLinearGroup k V :=
    LinearMap.GeneralLinearGroup.congrLinearEquiv b.equivFun.symm
  exact (translationGLPointMulEquiv (k := k)
    (Module.finrank k V)).trans (eGL.trans eLin)

private lemma generalLinearPointMulEquivOf_apply
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (x : Variety.Point (glVarietyOf k V)) :
    generalLinearPointMulEquivOf b x = glPointEquivOf k V b x := rfl

private noncomputable def generalLinearLinearMatrixCoefficient
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (l : Module.Dual k V) (v : V) :
    Variety.PolynomialFunction (glVarietyOf k V) :=
  ∑ i, ∑ j,
    algebraMap k (Variety.PolynomialFunction (glVarietyOf k V))
      (l (b i) * b.repr v j) *
        generalLinearMatrixCoordinateOf V i j

private lemma generalLinearLinearMatrixCoefficient_apply
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (l : Module.Dual k V) (v : V)
    (x : Variety.Point (glVarietyOf k V)) :
    generalLinearLinearMatrixCoefficient b l v x =
      l (((generalLinearPointMulEquivOf b x :
        LinearMap.GeneralLinearGroup k V) : Module.End k V) v) := by
  classical
  rw [generalLinearLinearMatrixCoefficient]
  change polynomialFunctionEvalAddHom (glVarietyOf k V) x
      (∑ i, ∑ j,
        algebraMap k (Variety.PolynomialFunction (glVarietyOf k V))
          (l (b i) * b.repr v j) *
            generalLinearMatrixCoordinateOf V i j) = _
  rw [map_sum]
  simp only [map_sum, polynomialFunctionEvalAddHom_apply,
    polynomialFunction_mul_apply,
    polynomialFunction_algebraMap_apply]
  simp_rw [generalLinearMatrixCoordinateOf_eq_basis_coord b]
  simp_rw [← generalLinearPointMulEquivOf_apply b x]
  simpa [LinearMap.toMatrix_apply] using
    LinearMap.dual_apply_eq_sum_toMatrix b l
      ((generalLinearPointMulEquivOf b x :
        LinearMap.GeneralLinearGroup k V) : Module.End k V) v

private lemma generalLinearIdentityTangentLinearMap_linearMatrixCoefficient
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (D : IdentityPointDerivation (glVarietyOf k V))
    (l : Module.Dual k V) (v : V) :
    l (generalLinearIdentityTangentLinearMap b D v) =
      D (generalLinearLinearMatrixCoefficient b l v) := by
  classical
  rw [generalLinearIdentityTangentLinearMap,
    generalLinearLinearMatrixCoefficient]
  change l ((∑ i, ∑ j,
    D (generalLinearMatrixCoordinateOf V i j) •
      b.end (i, j)) v) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum]
  simp_rw [Theory.AlgebraicGroup.Module.Basis.end_apply_eq_smul]
  simp only [map_smul]
  simp_rw [D.leibniz]
  have hsmul (q : Variety.PolynomialFunction (glVarietyOf k V)) (a : k) :
      q • a = q 1 * a := rfl
  simp_rw [hsmul]
  simp only [Derivation.map_algebraMap, mul_zero, add_zero,
    polynomialFunction_algebraMap_apply]
  ring_nf

private lemma generalLinearIdentityTangentLinearMap_conjugation
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (g : Variety.Point (glVarietyOf k V))
    (D : IdentityPointDerivation (glVarietyOf k V)) :
    generalLinearIdentityTangentLinearMap b
        (((Theory.AlgebraicGroup.identityTangentRepresentation
          (glVarietyOf k V)).action g).1 D) =
      ((generalLinearConjugationRepresentation
        (generalLinearPointMulEquivOf b g) :
          LinearMap.GeneralLinearGroup k (Module.End k V)) :
            Module.End k (Module.End k V))
        (generalLinearIdentityTangentLinearMap b D) := by
  apply LinearMap.ext
  intro v
  apply b.ext_elem
  intro i
  let xg := generalLinearPointMulEquivOf b g
  let l : Module.Dual k V := b.coord i
  let l' : Module.Dual k V := l.comp xg.toLinearEquiv.toLinearMap
  let v' : V := xg.toLinearEquiv.symm v
  change l (generalLinearIdentityTangentLinearMap b
      (((Theory.AlgebraicGroup.identityTangentRepresentation
        (glVarietyOf k V)).action g).1 D) v) =
    l (((generalLinearConjugationRepresentation xg :
      LinearMap.GeneralLinearGroup k (Module.End k V)) :
        Module.End k (Module.End k V))
          (generalLinearIdentityTangentLinearMap b D) v)
  rw [generalLinearIdentityTangentLinearMap_linearMatrixCoefficient]
  change (((Theory.AlgebraicGroup.identityTangentRepresentation
    (glVarietyOf k V)).action g).1 D)
      (generalLinearLinearMatrixCoefficient b l v) = _
  rw [Theory.AlgebraicGroup.identityTangentRepresentation_action_apply]
  have hpull :
      (AlgebraicGroup.conjugationByMorphism (glVarietyOf k V) g).pullbackAlgHom
          (generalLinearLinearMatrixCoefficient b l v) =
        generalLinearLinearMatrixCoefficient b l' v' := by
    apply Variety.PolynomialFunction.ext
    intro x
    change generalLinearLinearMatrixCoefficient b l v
      ((AlgebraicGroup.conjugationByMorphism (glVarietyOf k V) g).toFun x) = _
    rw [generalLinearLinearMatrixCoefficient_apply,
      generalLinearLinearMatrixCoefficient_apply,
      AlgebraicGroup.conjugationByMorphism_apply]
    rw [map_mul, map_mul, map_inv]
    change l (((xg * generalLinearPointMulEquivOf b x * xg⁻¹ :
      LinearMap.GeneralLinearGroup k V) : Module.End k V) v) =
        l' (((generalLinearPointMulEquivOf b x :
          LinearMap.GeneralLinearGroup k V) : Module.End k V) v')
    rfl
  rw [hpull, ← generalLinearIdentityTangentLinearMap_linearMatrixCoefficient]
  rfl

private lemma transvection_conj_diagonal_matrixUnit
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    {p q : Fin (Module.finrank k V)} (hpq : p ≠ q) :
    let hcoord : b.coord q (b p) = 0 := by
      simp [Module.Basis.coord_apply, hpq]
    let e : V ≃ₗ[k] V := LinearEquiv.transvection hcoord
    e.conj (b.end (q, q)) - b.end (q, q) = b.end (p, q) := by
  dsimp only
  apply b.ext
  intro r
  rw [LinearMap.sub_apply, LinearEquiv.conj_apply]
  change LinearMap.transvection (b.coord q) (b p)
      ((b.end (q, q)) (LinearMap.transvection (b.coord q) (-b p) (b r))) -
        b.end (q, q) (b r) = b.end (p, q) (b r)
  by_cases hrq : r = q
  · subst r
    simp [LinearMap.transvection.apply, Module.Basis.end_apply_apply,
      Ne.symm hpq]
  · simp [LinearMap.transvection.apply, Module.Basis.end_apply_apply,
      Ne.symm hrq]

/-- A chosen-basis diagonal matrix unit is the tangent of a diagonal-torus
morphism, with the point action of that morphism recorded in the same
certificate. -/
public theorem exists_basisDiagonalMorphism_identityTangent_matrixUnit
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (i : Fin (Module.finrank k V)) :
    ∃ (f : AlgebraicGroup.Morphism
        (dVariety k (Module.finrank k V)) (glVarietyOf k V))
      (D : IdentityPointDerivation (dVariety k (Module.finrank k V))),
      (∀ x j,
        ((glPointEquivOf k V b (f.onPoints x) :
          LinearMap.GeneralLinearGroup k V) : Module.End k V) (b j) =
            dPointEntry (Module.finrank k V) x j • b j) ∧
      generalLinearIdentityTangentLinearMap b
          (identityTangentMorphismLinearMap f D) = b.end (i, i) := by
  exact ⟨chosenBasisDiagonalMorphism b,
    diagonalIdentityTangent (Module.finrank k V) i,
    chosenBasisDiagonalMorphism_action_basis b,
    chosenBasisDiagonalMorphism_tangent_matrixUnit b i⟩

/-- Matrix-coordinate differentiation intertwines identity-tangent
conjugation with conjugation of endomorphisms. -/
public theorem generalLinearIdentityTangentLinearMap_conjugation_eq
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (g : Variety.Point (glVarietyOf k V))
    (D : IdentityPointDerivation (glVarietyOf k V)) :
    generalLinearIdentityTangentLinearMap b
        (identityTangentConjugationLinearMap (glVarietyOf k V) g D) =
      ((generalLinearConjugationRepresentation
        (glPointEquivOf k V b g) :
          LinearMap.GeneralLinearGroup k (Module.End k V)) :
            Module.End k (Module.End k V))
        (generalLinearIdentityTangentLinearMap b D) := by
  have hD : identityTangentConjugationLinearMap (glVarietyOf k V) g D =
      (((Theory.AlgebraicGroup.identityTangentRepresentation
        (glVarietyOf k V)).action g).1 D) := by
    apply Derivation.ext
    intro f
    rw [identityTangentConjugationLinearMap_apply,
      Theory.AlgebraicGroup.identityTangentRepresentation_action_apply]
  rw [hD, generalLinearIdentityTangentLinearMap_conjugation]
  rfl

private lemma generalLinearIdentityTangentLinearMap_matrixUnit_mem_range
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (p q : Fin (Module.finrank k V)) :
    b.end (p, q) ∈ LinearMap.range (generalLinearIdentityTangentLinearMap b) := by
  classical
  let Dq : IdentityPointDerivation (glVarietyOf k V) :=
    identityTangentMorphismLinearMap (chosenBasisDiagonalMorphism b)
      (diagonalIdentityTangent (Module.finrank k V) q)
  have hDq : generalLinearIdentityTangentLinearMap b Dq = b.end (q, q) :=
    chosenBasisDiagonalMorphism_tangent_matrixUnit b q
  by_cases hpq : p = q
  · subst p
    exact ⟨Dq, hDq⟩
  · let hcoord : b.coord q (b p) = 0 := by
      simp [Module.Basis.coord_apply, hpq]
    let e : V ≃ₗ[k] V := LinearEquiv.transvection hcoord
    let eg : LinearMap.GeneralLinearGroup k V :=
      LinearMap.GeneralLinearGroup.ofLinearEquiv e
    let g : Variety.Point (glVarietyOf k V) :=
      (generalLinearPointMulEquivOf b).symm eg
    let Dg : IdentityPointDerivation (glVarietyOf k V) :=
      ((Theory.AlgebraicGroup.identityTangentRepresentation
        (glVarietyOf k V)).action g).1 Dq
    refine ⟨Dg - Dq, ?_⟩
    rw [map_sub, generalLinearIdentityTangentLinearMap_conjugation, hDq,
      generalLinearConjugationRepresentation_apply]
    have hg : generalLinearPointMulEquivOf b g = eg :=
      (generalLinearPointMulEquivOf b).apply_symm_apply eg
    rw [hg]
    change e.conj (b.end (q, q)) - b.end (q, q) = b.end (p, q)
    exact transvection_conj_diagonal_matrixUnit b hpq

/-- Every endomorphism is obtained by differentiating matrix coordinates at
the identity of the general-linear variety. -/
public theorem generalLinearIdentityTangentLinearMap_surjective
    (b : Module.Basis (Fin (Module.finrank k V)) k V) :
    Function.Surjective (generalLinearIdentityTangentLinearMap b) := by
  rw [← LinearMap.range_eq_top]
  apply top_unique
  intro A _
  rw [← b.end.sum_repr A]
  apply Submodule.sum_mem
  intro pq _
  exact Submodule.smul_mem _ _
    (generalLinearIdentityTangentLinearMap_matrixUnit_mem_range b pq.1 pq.2)


end Theory.AlgebraicGroup.Bor1
