module

public import Theory.AlgebraicGroup.ClosedSubgroup.Basic
public import Theory.AlgebraicGroup.Representations.Matrix
public import Theory.LinearAlgebra.CliffordAlgebra.LipschitzNormalizer
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis

/-!
# The closed Clifford Spin carrier

This module gives a reusable finite polynomial characterization of the
left-regular image of Mathlib's genuine `spinGroup Q` inside
`GL (CliffordAlgebra Q)` by left multiplication.  It constructs a finite
zero locus from chosen bases and proves the image closed from two explicit
mathematical inputs: forward Spin conjugation on vectors and a reverse
normalizer criterion for generated Lipschitz units.  The final section applies
this interface to a nondegenerate positive odd-dimensional quadratic space
over an algebraically closed field with invertible `2`, producing the concrete
carrier required by the standard odd orthogonal model in GLS3, Theorem
1.10.7(b).  `CliffordSplitSpinCarrier` applies the same equations in arbitrary
characteristic.

Closedness is proved in coordinates.  A finite family of polynomial equations
says that an ambient linear map is left multiplication by its value at `1`,
that this value is even and Clifford-unitary, and that it and its inverse
conjugate a basis of the embedded vector space back into that space.  In the
reverse direction, invertibility of left multiplication recovers a Clifford
unit.  The two conjugation inclusions give equality of the vector range, and
`mem_lipschitzGroup_of_mem_even_of_conjAct_smul_range_ι_eq` then proves, rather
than assumes, membership in the generated Lipschitz group.  Evenness and the
unitary equations finish the exact Spin characterization.
-/

universe u

open scoped BigOperators Pointwise
open CliffordAlgebra

namespace Theory.AlgebraicGroup

set_option linter.unusedSectionVars false

variable {k V : Type u} [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable {Q : QuadraticForm k V}

section PolynomialCharacterization

variable [Module.Finite k (CliffordAlgebra Q)]

/-- The standard multiplicative equivalence from general-linear variety points
to linear automorphisms, expressed using a chosen basis. -/
public noncomputable def cliffordSpinLinearPointMulEquiv
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    Variety.Point (glVarietyOf k (CliffordAlgebra Q)) ≃*
      (CliffordAlgebra Q ≃ₗ[k] CliffordAlgebra Q) :=
  ((((translationGLPointMulEquiv
      (k := k) (Module.finrank k (CliffordAlgebra Q))).trans
    Matrix.GeneralLinearGroup.toLin).trans
      (LinearMap.GeneralLinearGroup.congrLinearEquiv e.equivFun.symm)).trans
        (LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)))

omit [FiniteDimensional k V] [Module.Finite k (CliffordAlgebra Q)] in
/-- The Clifford linear-point equivalence is the standard `glPointEquivOf`
followed by conversion from a general-linear unit to a linear equivalence. -/
public lemma cliffordSpinLinearPointMulEquiv_apply_eq
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    cliffordSpinLinearPointMulEquiv e x =
      LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)
        (glPointEquivOf k (CliffordAlgebra Q) e x) := by
  rfl

private noncomputable def glEntryCoordinate
    (i j : Fin (Module.finrank k (CliffordAlgebra Q))) :
    (glVarietyOf k (CliffordAlgebra Q)).Coordinates :=
  Sum.inl (i, j)

private noncomputable def glMatrixOfPointOf
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    Matrix (Fin (Module.finrank k (CliffordAlgebra Q)))
      (Fin (Module.finrank k (CliffordAlgebra Q))) k :=
  fun i j => x.val (glEntryCoordinate (Q := Q) i j)

omit [FiniteDimensional k V] in
private lemma glPointEquivOf_apply_basis'
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q)))
    (j : Fin (Module.finrank k (CliffordAlgebra Q))) :
    (glPointEquivOf k (CliffordAlgebra Q) e x).1 (e j) =
      e.equivFun.symm (fun l => glMatrixOfPointOf (Q := Q) x l j) := by
  simpa [glMatrixOfPointOf, glEntryCoordinate, glVarietyOf, glMatrixOfPoint] using
    glPointEquivOf_apply_basis (CliffordAlgebra Q) e x j

omit [FiniteDimensional k V] in
private lemma cliffordSpinLinearPointMulEquiv_apply
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (c : Fin (Module.finrank k (CliffordAlgebra Q)) → k)
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    cliffordSpinLinearPointMulEquiv e x (e.equivFun.symm c) =
      e.equivFun.symm ((glMatrixOfPointOf (Q := Q) x).mulVec c) := by
  change (glPointEquivOf k (CliffordAlgebra Q) e x).1 (e.equivFun.symm c) = _
  rw [Module.Basis.equivFun_symm_apply]
  simp_rw [map_sum, map_smul, glPointEquivOf_apply_basis']
  apply e.equivFun.injective
  rw [e.equivFun.apply_symm_apply]
  simp only [map_sum, map_smul, e.equivFun.apply_symm_apply]
  ext i
  simp [Matrix.mulVec, dotProduct, glMatrixOfPointOf, mul_comm]

private noncomputable def pointApplyCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (v : CliffordAlgebra Q)
    (i : Fin (Module.finrank k (CliffordAlgebra Q))) :
    MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k :=
  ∑ j, MvPolynomial.C (e.repr v j) *
    MvPolynomial.X (glEntryCoordinate (Q := Q) i j)

omit [FiniteDimensional k V] in
private lemma eval_pointApplyCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (v : CliffordAlgebra Q)
    (i : Fin (Module.finrank k (CliffordAlgebra Q)))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    evalPolynomial x.val (pointApplyCoordinates e v i) =
      e.repr (cliffordSpinLinearPointMulEquiv e x v) i := by
  rw [pointApplyCoordinates, evalPolynomial_sum]
  simp [evalPolynomial]
  have hv : e.equivFun.symm (e.repr v) = v :=
    e.equivFun.symm_apply_apply v
  rw [← hv, cliffordSpinLinearPointMulEquiv_apply]
  change _ = e.equivFun (e.equivFun.symm
    ((glMatrixOfPointOf (Q := Q) x).mulVec (e.repr v))) i
  rw [e.equivFun.apply_symm_apply]
  simp [Matrix.mulVec, dotProduct, mul_comm]
  change (∑ j, x.val (glEntryCoordinate (Q := Q) i j) * e.repr v j) =
    ∑ j, x.val (glEntryCoordinate (Q := Q) i j) * e.repr v j
  rfl

private noncomputable def polynomialVectorValue
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (p : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    CliffordAlgebra Q :=
  e.equivFun.symm (fun i => evalPolynomial x.val (p i))

omit [FiniteDimensional k V] [Module.Finite k (CliffordAlgebra Q)] in
private lemma repr_polynomialVectorValue
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (p : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q)))
    (i : Fin (Module.finrank k (CliffordAlgebra Q))) :
    e.repr (polynomialVectorValue e p x) i = evalPolynomial x.val (p i) := by
  exact congrFun (e.equivFun.apply_symm_apply _) i

private noncomputable def constantCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (a : CliffordAlgebra Q)
    (i : Fin (Module.finrank k (CliffordAlgebra Q))) :
    MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k :=
  MvPolynomial.C (e.repr a i)

omit [FiniteDimensional k V] [Module.Finite k (CliffordAlgebra Q)] in
private lemma polynomialVectorValue_constantCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (a : CliffordAlgebra Q)
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (constantCoordinates e a) x = a := by
  apply e.repr.injective
  ext i
  rw [repr_polynomialVectorValue]
  simp [constantCoordinates, evalPolynomial]

private noncomputable def linearMapCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (f : CliffordAlgebra Q →ₗ[k] CliffordAlgebra Q)
    (p : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (i : Fin (Module.finrank k (CliffordAlgebra Q))) :
    MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k :=
  ∑ j, MvPolynomial.C (e.repr (f (e j)) i) * p j

omit [FiniteDimensional k V] [Module.Finite k (CliffordAlgebra Q)] in
private lemma polynomialVectorValue_linearMapCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (f : CliffordAlgebra Q →ₗ[k] CliffordAlgebra Q)
    (p : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (linearMapCoordinates e f p) x =
      f (polynomialVectorValue e p x) := by
  apply e.repr.injective
  ext i
  rw [repr_polynomialVectorValue, linearMapCoordinates, evalPolynomial_sum]
  simp_rw [evalPolynomial_mul]
  simp only [evalPolynomial, MvPolynomial.eval₂_C, RingHom.id_apply]
  rw [← e.sum_repr (polynomialVectorValue e p x)]
  simp_rw [map_sum, map_smul]
  simp only [Finsupp.coe_finsetSum, Finsupp.coe_smul, Finset.sum_apply,
    Pi.smul_apply, repr_polynomialVectorValue, smul_eq_mul]
  change (∑ j, e.repr (f (e j)) i * evalPolynomial x.val (p j)) =
    ∑ j, evalPolynomial x.val (p j) * e.repr (f (e j)) i
  apply Finset.sum_congr rfl
  intro j hj
  ring

private noncomputable def mulCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (p q : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (i : Fin (Module.finrank k (CliffordAlgebra Q))) :
    MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k :=
  ∑ j, ∑ l, MvPolynomial.C (e.repr (e j * e l) i) * p j * q l

omit [FiniteDimensional k V] [Module.Finite k (CliffordAlgebra Q)] in
private lemma polynomialVectorValue_mulCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (p q : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (mulCoordinates e p q) x =
      polynomialVectorValue e p x * polynomialVectorValue e q x := by
  apply e.repr.injective
  ext i
  rw [repr_polynomialVectorValue, mulCoordinates, evalPolynomial_sum]
  simp_rw [evalPolynomial_sum]
  simp_rw [evalPolynomial_mul]
  simp only [evalPolynomial, MvPolynomial.eval₂_C, RingHom.id_apply]
  rw [← e.sum_repr (polynomialVectorValue e p x),
    ← e.sum_repr (polynomialVectorValue e q x)]
  simp_rw [Finset.sum_mul, Finset.mul_sum, Algebra.smul_mul_assoc,
    Algebra.mul_smul_comm]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, repr_polynomialVectorValue, smul_eq_mul]
  change (∑ j, ∑ l, e.repr (e j * e l) i * evalPolynomial x.val (p j) *
      evalPolynomial x.val (q l)) =
    ∑ j, ∑ l, evalPolynomial x.val (p j) *
      (evalPolynomial x.val (q l) * e.repr (e j * e l) i)
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro l hl
  ring

private noncomputable def subCoordinates
    (p q : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (i : Fin (Module.finrank k (CliffordAlgebra Q))) :
    MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k :=
  p i - q i

omit [FiniteDimensional k V] [Module.Finite k (CliffordAlgebra Q)] in
private lemma polynomialVectorValue_subCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (p q : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (subCoordinates p q) x =
      polynomialVectorValue e p x - polynomialVectorValue e q x := by
  apply e.repr.injective
  ext i
  simp [subCoordinates, repr_polynomialVectorValue, evalPolynomial]

private noncomputable def submoduleQuotientBasis
    (S : Submodule k (CliffordAlgebra Q)) :
    Module.Basis (Fin (Module.finrank k ((CliffordAlgebra Q) ⧸ S))) k
      ((CliffordAlgebra Q) ⧸ S) :=
  Module.finBasis k ((CliffordAlgebra Q) ⧸ S)

private noncomputable def submoduleMembershipPolynomial
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (S : Submodule k (CliffordAlgebra Q))
    (p : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (r : Fin (Module.finrank k ((CliffordAlgebra Q) ⧸ S))) :
    MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k :=
  ∑ i, MvPolynomial.C
      ((submoduleQuotientBasis (Q := Q) S).repr (S.mkQ (e i)) r) * p i

omit [FiniteDimensional k V] in
private lemma eval_submoduleMembershipPolynomial
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (S : Submodule k (CliffordAlgebra Q))
    (p : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (r : Fin (Module.finrank k ((CliffordAlgebra Q) ⧸ S)))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    evalPolynomial x.val (submoduleMembershipPolynomial e S p r) =
      (submoduleQuotientBasis (Q := Q) S).repr
        (S.mkQ (polynomialVectorValue e p x)) r := by
  rw [submoduleMembershipPolynomial, evalPolynomial_sum]
  simp_rw [evalPolynomial_mul]
  simp only [evalPolynomial, MvPolynomial.eval₂_C, RingHom.id_apply]
  rw [← e.sum_repr (polynomialVectorValue e p x)]
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finsupp.coe_smul,
    Finset.sum_apply, Pi.smul_apply, repr_polynomialVectorValue, smul_eq_mul]
  change (∑ i, (submoduleQuotientBasis (Q := Q) S).repr (S.mkQ (e i)) r *
      evalPolynomial x.val (p i)) =
    ∑ i, evalPolynomial x.val (p i) *
      (submoduleQuotientBasis (Q := Q) S).repr (S.mkQ (e i)) r
  apply Finset.sum_congr rfl
  intro i hi
  ring

omit [FiniteDimensional k V] in
private lemma submoduleMembershipPolynomial_zero_iff
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (S : Submodule k (CliffordAlgebra Q))
    (p : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    (∀ r, evalPolynomial x.val (submoduleMembershipPolynomial e S p r) = 0) ↔
      polynomialVectorValue e p x ∈ S := by
  rw [← Submodule.Quotient.mk_eq_zero]
  constructor
  · intro h
    apply (submoduleQuotientBasis (Q := Q) S).repr.injective
    ext r
    rw [map_zero, Finsupp.zero_apply]
    simpa only [Submodule.mkQ_apply] using
      (eval_submoduleMembershipPolynomial e S p r x).symm.trans (h r)
  · intro h r
    rw [eval_submoduleMembershipPolynomial]
    have h' : S.mkQ (polynomialVectorValue e p x) = 0 := by
      simpa only [Submodule.mkQ_apply] using h
    rw [h', map_zero, Finsupp.zero_apply]

private noncomputable def cliffordStarLinearMap :
    CliffordAlgebra Q →ₗ[k] CliffordAlgebra Q :=
  CliffordAlgebra.reverse.comp CliffordAlgebra.involute.toLinearMap

omit [IsAlgClosed k] [FiniteDimensional k V]
    [Module.Finite k (CliffordAlgebra Q)] in
private lemma cliffordStarLinearMap_apply (a : CliffordAlgebra Q) :
    cliffordStarLinearMap (Q := Q) a = star a := by
  rw [CliffordAlgebra.star_def]
  rfl

private noncomputable def pointValueCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :=
  pointApplyCoordinates e (1 : CliffordAlgebra Q)

private noncomputable def pointStarValueCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :=
  linearMapCoordinates e (cliffordStarLinearMap (Q := Q))
    (pointValueCoordinates e)

private lemma polynomialVectorValue_pointValueCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (pointValueCoordinates e) x =
      cliffordSpinLinearPointMulEquiv e x 1 := by
  apply e.repr.injective
  ext i
  rw [repr_polynomialVectorValue]
  change evalPolynomial x.val (pointApplyCoordinates e 1 i) = _
  rw [eval_pointApplyCoordinates]

private lemma polynomialVectorValue_pointStarValueCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (pointStarValueCoordinates e) x =
      star (cliffordSpinLinearPointMulEquiv e x 1) := by
  rw [pointStarValueCoordinates, polynomialVectorValue_linearMapCoordinates,
    polynomialVectorValue_pointValueCoordinates, cliffordStarLinearMap_apply]

private noncomputable def leftRegularErrorCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (j : Fin (Module.finrank k (CliffordAlgebra Q))) :=
  subCoordinates (pointApplyCoordinates e (e j))
    (mulCoordinates e (pointValueCoordinates e) (constantCoordinates e (e j)))

private noncomputable def starMulSelfErrorCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :=
  subCoordinates
    (mulCoordinates e (pointStarValueCoordinates e) (pointValueCoordinates e))
    (constantCoordinates e (1 : CliffordAlgebra Q))

private noncomputable def mulStarSelfErrorCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :=
  subCoordinates
    (mulCoordinates e (pointValueCoordinates e) (pointStarValueCoordinates e))
    (constantCoordinates e (1 : CliffordAlgebra Q))

private noncomputable def conjugatedVectorCoordinates
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (j : Fin (Module.finrank k V)) :=
  mulCoordinates e
    (mulCoordinates e (pointValueCoordinates e)
      (constantCoordinates e (CliffordAlgebra.ι Q (b j))))
    (pointStarValueCoordinates e)

private noncomputable def inverseConjugatedVectorCoordinates
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (j : Fin (Module.finrank k V)) :=
  mulCoordinates e
    (mulCoordinates e (pointStarValueCoordinates e)
      (constantCoordinates e (CliffordAlgebra.ι Q (b j))))
    (pointValueCoordinates e)

private abbrev SpinCarrierEquationIndex
    (Q : QuadraticForm k V) :=
  (Fin (Module.finrank k (CliffordAlgebra Q)) ×
      Fin (Module.finrank k (CliffordAlgebra Q))) ⊕
    (Fin (Module.finrank k ((CliffordAlgebra Q) ⧸
        (CliffordAlgebra.even Q).toSubmodule)) ⊕
      (Fin (Module.finrank k (CliffordAlgebra Q)) ⊕
        (Fin (Module.finrank k (CliffordAlgebra Q)) ⊕
          ((Fin (Module.finrank k V) ×
              Fin (Module.finrank k ((CliffordAlgebra Q) ⧸
                LinearMap.range (CliffordAlgebra.ι Q)))) ⊕
            (Fin (Module.finrank k V) ×
              Fin (Module.finrank k ((CliffordAlgebra Q) ⧸
                LinearMap.range (CliffordAlgebra.ι Q))))))))

private noncomputable def spinCarrierEquation
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    SpinCarrierEquationIndex Q →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k
  | Sum.inl (i, j) => leftRegularErrorCoordinates e j i
  | Sum.inr (Sum.inl r) =>
      submoduleMembershipPolynomial e (CliffordAlgebra.even Q).toSubmodule
        (pointValueCoordinates e) r
  | Sum.inr (Sum.inr (Sum.inl i)) => starMulSelfErrorCoordinates e i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => mulStarSelfErrorCoordinates e i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (j, r))))) =>
      submoduleMembershipPolynomial e (LinearMap.range (CliffordAlgebra.ι Q))
        (conjugatedVectorCoordinates b e j) r
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, r))))) =>
      submoduleMembershipPolynomial e (LinearMap.range (CliffordAlgebra.ι Q))
        (inverseConjugatedVectorCoordinates b e j) r

private lemma polynomialVectorValue_pointApplyCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (v : CliffordAlgebra Q)
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (pointApplyCoordinates e v) x =
      cliffordSpinLinearPointMulEquiv e x v := by
  apply e.repr.injective
  ext i
  rw [repr_polynomialVectorValue, eval_pointApplyCoordinates]

omit [FiniteDimensional k V] [Module.Finite k (CliffordAlgebra Q)] in
private lemma polynomialVectorValue_eq_zero_iff
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (p : Fin (Module.finrank k (CliffordAlgebra Q)) →
      MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k)
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    (∀ i, evalPolynomial x.val (p i) = 0) ↔
      polynomialVectorValue e p x = 0 := by
  constructor
  · intro h
    apply e.repr.injective
    ext i
    rw [repr_polynomialVectorValue, h, map_zero, Finsupp.zero_apply]
  · intro h i
    have hi := congrArg (fun a : CliffordAlgebra Q => e.repr a i) h
    simpa only [repr_polynomialVectorValue, map_zero, Finsupp.zero_apply] using hi

private lemma polynomialVectorValue_leftRegularErrorCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (j : Fin (Module.finrank k (CliffordAlgebra Q)))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (leftRegularErrorCoordinates e j) x =
      cliffordSpinLinearPointMulEquiv e x (e j) -
        cliffordSpinLinearPointMulEquiv e x 1 * e j := by
  rw [leftRegularErrorCoordinates, polynomialVectorValue_subCoordinates,
    polynomialVectorValue_pointApplyCoordinates,
    polynomialVectorValue_mulCoordinates,
    polynomialVectorValue_pointValueCoordinates,
    polynomialVectorValue_constantCoordinates]

private lemma polynomialVectorValue_starMulSelfErrorCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (starMulSelfErrorCoordinates e) x =
      star (cliffordSpinLinearPointMulEquiv e x 1) * cliffordSpinLinearPointMulEquiv e x 1 - 1 := by
  rw [starMulSelfErrorCoordinates, polynomialVectorValue_subCoordinates,
    polynomialVectorValue_mulCoordinates,
    polynomialVectorValue_pointStarValueCoordinates,
    polynomialVectorValue_pointValueCoordinates,
    polynomialVectorValue_constantCoordinates]

private lemma polynomialVectorValue_mulStarSelfErrorCoordinates
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (mulStarSelfErrorCoordinates e) x =
      cliffordSpinLinearPointMulEquiv e x 1 * star (cliffordSpinLinearPointMulEquiv e x 1) - 1 := by
  rw [mulStarSelfErrorCoordinates, polynomialVectorValue_subCoordinates,
    polynomialVectorValue_mulCoordinates,
    polynomialVectorValue_pointStarValueCoordinates,
    polynomialVectorValue_pointValueCoordinates,
    polynomialVectorValue_constantCoordinates]

private lemma polynomialVectorValue_conjugatedVectorCoordinates
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (j : Fin (Module.finrank k V))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (conjugatedVectorCoordinates b e j) x =
      cliffordSpinLinearPointMulEquiv e x 1 * CliffordAlgebra.ι Q (b j) *
        star (cliffordSpinLinearPointMulEquiv e x 1) := by
  rw [conjugatedVectorCoordinates, polynomialVectorValue_mulCoordinates,
    polynomialVectorValue_mulCoordinates,
    polynomialVectorValue_pointValueCoordinates,
    polynomialVectorValue_constantCoordinates,
    polynomialVectorValue_pointStarValueCoordinates]

private lemma polynomialVectorValue_inverseConjugatedVectorCoordinates
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (j : Fin (Module.finrank k V))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    polynomialVectorValue e (inverseConjugatedVectorCoordinates b e j) x =
      star (cliffordSpinLinearPointMulEquiv e x 1) * CliffordAlgebra.ι Q (b j) *
        cliffordSpinLinearPointMulEquiv e x 1 := by
  rw [inverseConjugatedVectorCoordinates, polynomialVectorValue_mulCoordinates,
    polynomialVectorValue_mulCoordinates,
    polynomialVectorValue_pointStarValueCoordinates,
    polynomialVectorValue_constantCoordinates,
    polynomialVectorValue_pointValueCoordinates]

private structure SpinCarrierSpec
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) : Prop where
  leftRegular : ∀ j, cliffordSpinLinearPointMulEquiv e x (e j) =
    cliffordSpinLinearPointMulEquiv e x 1 * e j
  even : cliffordSpinLinearPointMulEquiv e x 1 ∈ CliffordAlgebra.even Q
  star_mul_self : star (cliffordSpinLinearPointMulEquiv e x 1) *
    cliffordSpinLinearPointMulEquiv e x 1 = 1
  mul_star_self : cliffordSpinLinearPointMulEquiv e x 1 *
    star (cliffordSpinLinearPointMulEquiv e x 1) = 1
  conjugates : ∀ j, cliffordSpinLinearPointMulEquiv e x 1 *
    CliffordAlgebra.ι Q (b j) * star (cliffordSpinLinearPointMulEquiv e x 1) ∈
      LinearMap.range (CliffordAlgebra.ι Q)
  inverseConjugates : ∀ j, star (cliffordSpinLinearPointMulEquiv e x 1) *
    CliffordAlgebra.ι Q (b j) * cliffordSpinLinearPointMulEquiv e x 1 ∈
      LinearMap.range (CliffordAlgebra.ι Q)

private def spinCarrierEquations
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    Set (MvPolynomial (glVarietyOf k (CliffordAlgebra Q)).Coordinates k) :=
  Set.range (spinCarrierEquation b e)

private lemma spinCarrierEquation_zero_iff
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    (∀ q, evalPolynomial x.val (spinCarrierEquation b e q) = 0) ↔
      SpinCarrierSpec b e x := by
  constructor
  · intro h
    constructor
    · intro j
      apply sub_eq_zero.mp
      rw [← polynomialVectorValue_leftRegularErrorCoordinates]
      exact (polynomialVectorValue_eq_zero_iff e _ x).mp fun i =>
        h (Sum.inl (i, j))
    · have heven := (submoduleMembershipPolynomial_zero_iff e
        (CliffordAlgebra.even Q).toSubmodule _ x).mp fun r =>
          h (Sum.inr (Sum.inl r))
      rw [polynomialVectorValue_pointValueCoordinates] at heven
      exact heven
    · apply sub_eq_zero.mp
      rw [← polynomialVectorValue_starMulSelfErrorCoordinates]
      exact (polynomialVectorValue_eq_zero_iff e _ x).mp fun i =>
        h (Sum.inr (Sum.inr (Sum.inl i)))
    · apply sub_eq_zero.mp
      rw [← polynomialVectorValue_mulStarSelfErrorCoordinates]
      exact (polynomialVectorValue_eq_zero_iff e _ x).mp fun i =>
        h (Sum.inr (Sum.inr (Sum.inr (Sum.inl i))))
    · intro j
      rw [← polynomialVectorValue_conjugatedVectorCoordinates]
      exact (submoduleMembershipPolynomial_zero_iff e
        (LinearMap.range (CliffordAlgebra.ι Q)) _ x).mp fun r =>
          h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (j, r))))))
    · intro j
      rw [← polynomialVectorValue_inverseConjugatedVectorCoordinates]
      exact (submoduleMembershipPolynomial_zero_iff e
        (LinearMap.range (CliffordAlgebra.ι Q)) _ x).mp fun r =>
          h (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (j, r))))))
  · intro h q
    rcases q with q | q
    · rcases q with ⟨i, j⟩
      have hz : polynomialVectorValue e (leftRegularErrorCoordinates e j) x = 0 := by
        rw [polynomialVectorValue_leftRegularErrorCoordinates,
          sub_eq_zero.mpr (h.leftRegular j)]
      exact (polynomialVectorValue_eq_zero_iff e _ x).mpr hz i
    · rcases q with r | q
      · exact (submoduleMembershipPolynomial_zero_iff e
          (CliffordAlgebra.even Q).toSubmodule _ x).mpr
            (by
              rw [polynomialVectorValue_pointValueCoordinates]
              exact h.even) r
      · rcases q with i | q
        · have hz : polynomialVectorValue e (starMulSelfErrorCoordinates e) x = 0 := by
            rw [polynomialVectorValue_starMulSelfErrorCoordinates,
              sub_eq_zero.mpr h.star_mul_self]
          exact (polynomialVectorValue_eq_zero_iff e _ x).mpr hz i
        · rcases q with i | q
          · have hz : polynomialVectorValue e (mulStarSelfErrorCoordinates e) x = 0 := by
              rw [polynomialVectorValue_mulStarSelfErrorCoordinates,
                sub_eq_zero.mpr h.mul_star_self]
            exact (polynomialVectorValue_eq_zero_iff e _ x).mpr hz i
          · rcases q with q | q
            · rcases q with ⟨j, r⟩
              exact (submoduleMembershipPolynomial_zero_iff e
                (LinearMap.range (CliffordAlgebra.ι Q)) _ x).mpr
                  (by simpa [polynomialVectorValue_conjugatedVectorCoordinates]
                    using h.conjugates j) r
            · rcases q with ⟨j, r⟩
              exact (submoduleMembershipPolynomial_zero_iff e
                (LinearMap.range (CliffordAlgebra.ι Q)) _ x).mpr
                  (by simpa [polynomialVectorValue_inverseConjugatedVectorCoordinates]
                    using h.inverseConjugates j) r

private lemma spinCarrierSpec_isZariskiClosed
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    IsZariskiClosed (glVarietyOf k (CliffordAlgebra Q))
      {x | SpinCarrierSpec b e x} := by
  refine ⟨spinCarrierEquations b e, ?_⟩
  ext x
  constructor
  · intro hx p hp
    obtain ⟨q, rfl⟩ := hp
    exact (spinCarrierEquation_zero_iff b e x).mpr hx q
  · intro hx
    exact (spinCarrierEquation_zero_iff b e x).mp fun q =>
      hx (spinCarrierEquation b e q) ⟨q, rfl⟩

/-- The left-regular representation of Mathlib's Clifford `spinGroup` as
points of the general-linear variety of the Clifford algebra. -/
public noncomputable def spinLeftRegularPointHom
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    spinGroup Q →* Variety.Point (glVarietyOf k (CliffordAlgebra Q)) :=
  (cliffordSpinLinearPointMulEquiv e).symm.toMonoidHom.comp
    ((Units.mulLeftLinearEquiv k (CliffordAlgebra Q)).comp spinGroup.toUnits)

omit [FiniteDimensional k V] [Module.Finite k (CliffordAlgebra Q)] in
/-- Applying the ambient linear point equivalence to the left-regular Spin
point recovers left multiplication by the underlying Clifford unit. -/
public lemma cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (x : spinGroup Q) :
    cliffordSpinLinearPointMulEquiv e (spinLeftRegularPointHom e x) =
      (spinGroup.toUnits x).mulLeftLinearEquiv k (CliffordAlgebra Q) := by
  exact (cliffordSpinLinearPointMulEquiv e).apply_symm_apply _

omit [IsAlgClosed k] [FiniteDimensional k V]
    [Module.Finite k (CliffordAlgebra Q)] in
private lemma basis_conjugates_mem_range
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (a s : CliffordAlgebra Q)
    (h : ∀ j, a * CliffordAlgebra.ι Q (b j) * s ∈
      LinearMap.range (CliffordAlgebra.ι Q)) (v : V) :
    a * CliffordAlgebra.ι Q v * s ∈ LinearMap.range (CliffordAlgebra.ι Q) := by
  rw [← b.sum_repr v, map_sum]
  simp_rw [map_smul, Finset.mul_sum, Finset.sum_mul,
    Algebra.mul_smul_comm, Algebra.smul_mul_assoc]
  exact Submodule.sum_mem _ fun j hj => Submodule.smul_mem _ _ (h j)

omit [FiniteDimensional k V] [Module.Finite k (CliffordAlgebra Q)] in
private lemma spinLeftRegularPointHom_spec
    (hforward : ∀ (y : spinGroup Q) (v : V),
      (y : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
          star (y : CliffordAlgebra Q) ∈
        LinearMap.range (CliffordAlgebra.ι Q) ∧
      star (y : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
          (y : CliffordAlgebra Q) ∈
        LinearMap.range (CliffordAlgebra.ι Q))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) (x : spinGroup Q) :
    SpinCarrierSpec b e (spinLeftRegularPointHom e x) := by
  constructor
  · intro j
    rw [cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom]
    simp [Units.mulLeftLinearEquiv_apply]
  · rw [cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom]
    simpa using spinGroup.mem_even x.prop
  · rw [cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom]
    rw [Units.mulLeftLinearEquiv_apply, mul_one]
    change star (x : CliffordAlgebra Q) * (x : CliffordAlgebra Q) = 1
    exact spinGroup.star_mul_self_of_mem x.prop
  · rw [cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom]
    rw [Units.mulLeftLinearEquiv_apply, mul_one]
    change (x : CliffordAlgebra Q) * star (x : CliffordAlgebra Q) = 1
    exact spinGroup.mul_star_self_of_mem x.prop
  · intro j
    rw [cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom]
    rw [Units.mulLeftLinearEquiv_apply, mul_one]
    change (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q (b j) *
      star (x : CliffordAlgebra Q) ∈ LinearMap.range (CliffordAlgebra.ι Q)
    exact (hforward x (b j)).1
  · intro j
    rw [cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom]
    rw [Units.mulLeftLinearEquiv_apply, mul_one]
    change star (x : CliffordAlgebra Q) * CliffordAlgebra.ι Q (b j) *
      (x : CliffordAlgebra Q) ∈ LinearMap.range (CliffordAlgebra.ι Q)
    exact (hforward x (b j)).2

omit [FiniteDimensional k V] [Module.Finite k (CliffordAlgebra Q)] in
private lemma spinCarrierSpec_mem_spinLeftRegularPointHom_range
    (hreverse : ∀ {u : (CliffordAlgebra Q)ˣ},
      (↑u : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q →
      ConjAct.toConjAct u • LinearMap.range (CliffordAlgebra.ι Q) =
        LinearMap.range (CliffordAlgebra.ι Q) →
      u ∈ lipschitzGroup Q)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q)))
    (hx : SpinCarrierSpec b e x) :
    x ∈ (spinLeftRegularPointHom e).range := by
  let F := cliffordSpinLinearPointMulEquiv e x
  let a : CliffordAlgebra Q := F 1
  have hleft : F.toLinearMap = Algebra.lmul k (CliffordAlgebra Q) a := by
    apply e.ext
    intro j
    exact hx.leftRegular j
  have hFUnit : IsUnit F.toLinearMap := by
    exact ⟨LinearMap.GeneralLinearGroup.ofLinearEquiv F, rfl⟩
  have hlmulUnit : IsUnit ((Algebra.lmul k (CliffordAlgebra Q)) a) := by
    rw [← hleft]
    exact hFUnit
  have haUnit : IsUnit a := Algebra.lmul_isUnit_iff.mp hlmulUnit
  rcases haUnit with ⟨u, hu⟩
  have hstarMul : star (u : CliffordAlgebra Q) * (u : CliffordAlgebra Q) = 1 := by
    simpa [a, F, hu] using hx.star_mul_self
  have hmulStar : (u : CliffordAlgebra Q) * star (u : CliffordAlgebra Q) = 1 := by
    simpa [a, F, hu] using hx.mul_star_self
  have huMulInv : (u : CliffordAlgebra Q) *
      (↑(u⁻¹) : CliffordAlgebra Q) = 1 := by simp
  have hstar : star (u : CliffordAlgebra Q) =
      (↑(u⁻¹) : CliffordAlgebra Q) := by
    calc
      star (u : CliffordAlgebra Q) = star (u : CliffordAlgebra Q) * 1 :=
        (mul_one _).symm
      _ = star (u : CliffordAlgebra Q) *
          ((u : CliffordAlgebra Q) * (↑(u⁻¹) : CliffordAlgebra Q)) := by
            rw [huMulInv]
      _ = (star (u : CliffordAlgebra Q) * (u : CliffordAlgebra Q)) *
          (↑(u⁻¹) : CliffordAlgebra Q) := by rw [mul_assoc]
      _ = (↑(u⁻¹) : CliffordAlgebra Q) := by rw [hstarMul, one_mul]
  have hconj (v : V) :
      (u : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
          (↑(u⁻¹) : CliffordAlgebra Q) ∈
            LinearMap.range (CliffordAlgebra.ι Q) := by
    rw [← hstar]
    simpa [a, F, hu] using
      basis_conjugates_mem_range b a (star a) hx.conjugates v
  have hinvConj (v : V) :
      (↑(u⁻¹) : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
          (u : CliffordAlgebra Q) ∈ LinearMap.range (CliffordAlgebra.ι Q) := by
    rw [← hstar]
    simpa [a, F, hu] using
      basis_conjugates_mem_range b (star a) a hx.inverseConjugates v
  have hle : ConjAct.toConjAct u • LinearMap.range (CliffordAlgebra.ι Q) ≤
      LinearMap.range (CliffordAlgebra.ι Q) := by
    rw [Submodule.pointwise_smul_def, Submodule.map_le_iff_le_comap]
    rintro _ ⟨v, rfl⟩
    simpa [ConjAct.units_smul_def] using hconj v
  have hleInv : ConjAct.toConjAct u⁻¹ • LinearMap.range (CliffordAlgebra.ι Q) ≤
      LinearMap.range (CliffordAlgebra.ι Q) := by
    rw [Submodule.pointwise_smul_def, Submodule.map_le_iff_le_comap]
    rintro _ ⟨v, rfl⟩
    simpa [ConjAct.units_smul_def] using hinvConj v
  have hRange : ConjAct.toConjAct u • LinearMap.range (CliffordAlgebra.ι Q) =
      LinearMap.range (CliffordAlgebra.ι Q) := by
    apply le_antisymm hle
    have hs := smul_mono_right (ConjAct.toConjAct u) hleInv
    simpa only [map_inv, smul_inv_smul] using hs
  have huEven : (u : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q := by
    simpa [a, F, hu] using hx.even
  have huLipschitz : u ∈ lipschitzGroup Q :=
    hreverse huEven hRange
  have huPin : (u : CliffordAlgebra Q) ∈ pinGroup Q := by
    rw [pinGroup.units_mem_iff]
    exact ⟨huLipschitz, hstarMul, hmulStar⟩
  have huSpin : (u : CliffordAlgebra Q) ∈ spinGroup Q :=
    spinGroup.mem_iff.mpr ⟨huPin, huEven⟩
  let sx : spinGroup Q := ⟨u, huSpin⟩
  rw [MonoidHom.mem_range]
  refine ⟨sx, ?_⟩
  apply (cliffordSpinLinearPointMulEquiv e).injective
  rw [cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom]
  apply LinearEquiv.toLinearMap_injective
  rw [Units.toLinearMap_mulLeftLinearEquiv, hleft]
  change (Algebra.lmul k (CliffordAlgebra Q)) (spinGroup.toUnits sx :
    CliffordAlgebra Q) = (Algebra.lmul k (CliffordAlgebra Q)) a
  congr 1

omit [FiniteDimensional k V] in
private lemma mem_spinLeftRegularPointHom_range
    (hforward : ∀ (y : spinGroup Q) (v : V),
      (y : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
          star (y : CliffordAlgebra Q) ∈
        LinearMap.range (CliffordAlgebra.ι Q) ∧
      star (y : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
          (y : CliffordAlgebra Q) ∈
        LinearMap.range (CliffordAlgebra.ι Q))
    (hreverse : ∀ {u : (CliffordAlgebra Q)ˣ},
      (↑u : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q →
      ConjAct.toConjAct u • LinearMap.range (CliffordAlgebra.ι Q) =
        LinearMap.range (CliffordAlgebra.ι Q) →
      u ∈ lipschitzGroup Q)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (x : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    x ∈ (spinLeftRegularPointHom e).range ↔ SpinCarrierSpec b e x := by
  constructor
  · rintro ⟨y, rfl⟩
    exact spinLeftRegularPointHom_spec hforward b e y
  · exact spinCarrierSpec_mem_spinLeftRegularPointHom_range
      hreverse b e x

/-- The left-regular image of `spinGroup Q` is Zariski closed whenever Spin
conjugation preserves the embedded vector range and the converse normalizer
criterion recognizes generated Lipschitz units.  The proof is the finite
polynomial characterization encoded above. -/
public lemma spinLeftRegularPointHom_range_isZariskiClosed
    (hforward : ∀ (y : spinGroup Q) (v : V),
      (y : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
          star (y : CliffordAlgebra Q) ∈
        LinearMap.range (CliffordAlgebra.ι Q) ∧
      star (y : CliffordAlgebra Q) * CliffordAlgebra.ι Q v *
          (y : CliffordAlgebra Q) ∈
        LinearMap.range (CliffordAlgebra.ι Q))
    (hreverse : ∀ {u : (CliffordAlgebra Q)ˣ},
      (↑u : CliffordAlgebra Q) ∈ CliffordAlgebra.even Q →
      ConjAct.toConjAct u • LinearMap.range (CliffordAlgebra.ι Q) =
        LinearMap.range (CliffordAlgebra.ι Q) →
      u ∈ lipschitzGroup Q)
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    IsZariskiClosed (glVarietyOf k (CliffordAlgebra Q))
      ((spinLeftRegularPointHom e).range :
        Set (Variety.Point (glVarietyOf k (CliffordAlgebra Q)))) := by
  have hset : ((spinLeftRegularPointHom e).range :
      Set (Variety.Point (glVarietyOf k (CliffordAlgebra Q)))) =
      {x | SpinCarrierSpec b e x} := by
    ext x
    exact mem_spinLeftRegularPointHom_range hforward hreverse b e x
  rw [hset]
  exact spinCarrierSpec_isZariskiClosed b e

omit [FiniteDimensional k V] [Module.Finite k (CliffordAlgebra Q)] in
/-- The left-regular Spin representation is injective, since evaluation at
`1` recovers the underlying Clifford unit. -/
public lemma spinLeftRegularPointHom_injective
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    Function.Injective (spinLeftRegularPointHom e) := by
  intro x y hxy
  have hlin := congrArg (cliffordSpinLinearPointMulEquiv e) hxy
  rw [cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom,
    cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom] at hlin
  apply spinGroup.toUnits_injective
  apply Units.ext
  have hone := congrArg
    (fun f : CliffordAlgebra Q ≃ₗ[k] CliffordAlgebra Q => f 1) hlin
  simpa [Units.mulLeftLinearEquiv_apply] using hone

end PolynomialCharacterization

section Odd

variable [Invertible (2 : k)]

noncomputable local instance : Module.Finite k (CliffordAlgebra Q) :=
  Module.Finite.of_basis
    ((Module.finBasis k V).ExteriorAlgebra.map
      (CliffordAlgebra.equivExterior Q).symm)

private noncomputable def cliffordFinBasis :
    Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q) :=
  Module.finBasis k (CliffordAlgebra Q)

private lemma oddSpinLeftRegularPointHom_range_isZariskiClosed
    (hQ : Q.Nondegenerate) (hpos : 0 < Module.finrank k V)
    (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    IsZariskiClosed (glVarietyOf k (CliffordAlgebra Q))
      ((spinLeftRegularPointHom e).range :
        Set (Variety.Point (glVarietyOf k (CliffordAlgebra Q)))) := by
  refine spinLeftRegularPointHom_range_isZariskiClosed
    (Q := Q) (b := b) (e := e) ?_ ?_
  · intro x v
    constructor
    · have hx := spinGroup.conjAct_smul_ι_mem_range_ι
        (x := spinGroup.toUnits x) x.prop v
      have hstar : star (x : CliffordAlgebra Q) =
          (x⁻¹ : spinGroup Q) := rfl
      simpa [ConjAct.units_smul_def, hstar] using hx
    · have hx := spinGroup.conjAct_smul_ι_mem_range_ι
        (x := spinGroup.toUnits x⁻¹) (x⁻¹).prop v
      have hstar : star (x : CliffordAlgebra Q) =
          (x⁻¹ : spinGroup Q) := rfl
      simpa [ConjAct.units_smul_def, hstar] using hx
  · intro u huEven huNormalizer
    exact mem_lipschitzGroup_of_mem_even_of_conjAct_smul_range_ι_eq
      Q hQ hpos hodd u huEven huNormalizer

/-- A finite basis of the Clifford algebra obtained from its exterior-algebra
model. -/
public noncomputable def oddSpinCliffordBasis (Q : QuadraticForm k V) :
    Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q) :=
  cliffordFinBasis (Q := Q)

/-- The closed left-regular carrier of the genuine Clifford spin group. -/
public noncomputable def oddSpinClosedSubgroup
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (hpos : 0 < Module.finrank k V) (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    ClosedSubgroup (glVarietyOf k (CliffordAlgebra Q)) :=
  ClosedSubgroup.ofSubgroup (spinLeftRegularPointHom e).range
    (oddSpinLeftRegularPointHom_range_isZariskiClosed hQ hpos hodd b e)

/-- Exact membership in the closed spin carrier: its ambient linear map is
left multiplication by one and only one genuine `spinGroup Q` element. -/
public theorem oddSpinClosedSubgroup_carrier
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (hpos : 0 < Module.finrank k V) (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q))
    (g : Variety.Point (glVarietyOf k (CliffordAlgebra Q))) :
    g ∈ (oddSpinClosedSubgroup Q hQ hpos hodd b e).toSubgroup ↔
      ∃ x : spinGroup Q,
        LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)
            (glPointEquivOf k (CliffordAlgebra Q) e g) =
          (spinGroup.toUnits x).mulLeftLinearEquiv k (CliffordAlgebra Q) := by
  change g ∈ (spinLeftRegularPointHom e).range ↔ _
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom e x⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply (cliffordSpinLinearPointMulEquiv e).injective
    rw [cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom]
    exact hx.symm

/-- Rational points of the closed carrier, with their inherited product, are
the genuine Clifford spin group. -/
public noncomputable def oddSpinClosedSubgroupPoints
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (hpos : 0 < Module.finrank k V) (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let H := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := H.carrierAlgebraicGroup
    Variety.Point H.carrierVariety ≃* spinGroup Q := by
  let H := oddSpinClosedSubgroup Q hQ hpos hodd b e
  let pointEquiv : Variety.Point H.carrierVariety ≃* H.toSubgroup :=
    { toEquiv := H.pointEquiv
      map_mul' := fun _ _ => rfl }
  exact pointEquiv.trans
    (MonoidHom.ofInjective (spinLeftRegularPointHom_injective e)).symm

/-- The point equivalence is compatible with the chosen Clifford basis and
the ambient left-regular representation. -/
public theorem oddSpinClosedSubgroup_linear_points
    (Q : QuadraticForm k V) (hQ : Q.Nondegenerate)
    (hpos : 0 < Module.finrank k V) (hodd : Odd (Module.finrank k V))
    (b : Module.Basis (Fin (Module.finrank k V)) k V)
    (e : Module.Basis (Fin (Module.finrank k (CliffordAlgebra Q))) k
      (CliffordAlgebra Q)) :
    let H := oddSpinClosedSubgroup Q hQ hpos hodd b e
    letI := H.carrierAlgebraicGroup
    ∀ x,
      LinearMap.GeneralLinearGroup.generalLinearEquiv k (CliffordAlgebra Q)
          (glPointEquivOf k (CliffordAlgebra Q) e (H.inclusion.onPoints x)) =
        (spinGroup.toUnits
          (oddSpinClosedSubgroupPoints Q hQ hpos hodd b e x)).mulLeftLinearEquiv
            k (CliffordAlgebra Q) := by
  dsimp only
  intro x
  let H := oddSpinClosedSubgroup Q hQ hpos hodd b e
  let y : H.toSubgroup := H.pointEquiv x
  change cliffordSpinLinearPointMulEquiv e (H.inclusion.onPoints x) =
    (spinGroup.toUnits
      ((MonoidHom.ofInjective (spinLeftRegularPointHom_injective e)).symm
        y)).mulLeftLinearEquiv k (CliffordAlgebra Q)
  rw [← cliffordSpinLinearPointMulEquiv_spinLeftRegularPointHom]
  congr 1
  have hy := congrArg Subtype.val
    ((MonoidHom.ofInjective (spinLeftRegularPointHom_injective e)).apply_symm_apply y)
  exact hy.symm

end Odd

end Theory.AlgebraicGroup
