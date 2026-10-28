module

public import Theory.AlgebraicGroup.Instance.PGL2
public import Theory.AlgebraicGroup.Instance.SL
import all Theory.AlgebraicGroup.Instance.SL
public import Theory.AlgebraicGroup.Instance.PSL
import all Theory.AlgebraicGroup.Instance.PSL
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism
public import Theory.AlgebraicGroup.Variety.ProjectiveLine
public import Theory.CommutativeAlgebra.StrongZModTwoGrading
public import Mathlib.AlgebraicGeometry.Sites.Fpqc
public import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic

/-!
# Faithful flatness of the SL2-to-PGL2 projection

Over an algebraically closed field, the tensor representation defines the
standard central projection from `SL2` to the affine `PGL2` model.  This module
proves that its contravariant coordinate-ring map is faithfully flat and
exports the corresponding flat, surjective, quasi-compact, and effective
epimorphism interfaces for the associated affine schemes.  Effective
epimorphism is also exported after arbitrary base change, together with the
specific base change over geometric projective space `P1` needed to descend
the projective action.

The proof is characteristic-free and scheme-sensitive.  It presents the `SL2`
coordinate algebra as `k[a,b,c,d] / (a*d - b*c - 1)`, gives it the parity
`ZMod 2` grading, and identifies the pullback from `PGL2` with the even
subring.  The tensor coordinates supply every quadratic monomial, while
`a*d + b*(-c) = 1` makes the parity grading strong.  Faithful flatness then
follows from `StrongZModTwoGrading.gradeZeroSubtype_faithfullyFlat` and is
transported through the repository's coordinate-ring equivalences.  Point
surjectivity is used only to prove injectivity of the pullback, never to infer
flatness.

This is the coordinate proof of the standard central quotient
`SL2 -> SL2 / mu_2`.  In characteristic two, `mu_2` is nonreduced, so the
argument deliberately retains the full scheme structure rather than replacing
the kernel by its rational points.  The construction follows the tensor-image
models in `Instance.PSL` and `Instance.PGL2`; the final descent interface uses
Mathlib's fpqc effective-epimorphism theorem.
-/

open CategoryTheory DirectSum

namespace Theory.AlgebraicGroup

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

public noncomputable section

private abbrev C := ULift (Fin 2 × Fin 2)
private abbrev R (k : Type u) [CommSemiring k] := MvPolynomial C k

private def parityWeight : C -> ZMod 2 := fun _ => 1

private def sl2Relation (k : Type u) [Field k] : R k := slDetPoly 2 - 1

omit [IsAlgClosed k] in
private lemma sl2Relation_formula : sl2Relation (k := k) =
    MvPolynomial.X (ULift.up (0, 0)) * MvPolynomial.X (ULift.up (1, 1)) -
      MvPolynomial.X (ULift.up (0, 1)) * MvPolynomial.X (ULift.up (1, 0)) - 1 := by
  simp [sl2Relation, slDetPoly, slEntryMatrix, Matrix.det_fin_two]

omit [IsAlgClosed k] in
private lemma sl2Relation_irreducible : Irreducible (sl2Relation (k := k)) := by
  rw [sl2Relation_formula]
  let a : C := ULift.up (0, 0)
  let b : C := ULift.up (0, 1)
  let c : C := ULift.up (1, 0)
  let d : C := ULift.up (1, 1)
  have hd0 : MvPolynomial.X d ≠ (0 : R k) := MvPolynomial.X_ne_zero d
  have had : a ∉ (MvPolynomial.X d : R k).vars := by
    simp [a, d]
  have hag : a ∉
      (-MvPolynomial.X b * MvPolynomial.X c - 1 : R k).vars := by
    intro ha
    have ha' := MvPolynomial.vars_sub_subset
      (-MvPolynomial.X b * MvPolynomial.X c : R k) ha
    rw [Finset.mem_union] at ha'
    have ha' : a ∈
        (-MvPolynomial.X b * MvPolynomial.X c : R k).vars :=
      ha'.resolve_right (by simp)
    have ha'' := MvPolynomial.vars_mul
      (-MvPolynomial.X b : R k) (MvPolynomial.X c) ha'
    simp [a, b, c] at ha''
  have hrel : IsRelPrime (MvPolynomial.X d : R k)
      (-MvPolynomial.X b * MvPolynomial.X c - 1) := by
    apply (MvPolynomial.X_prime (i := d)).irreducible.isRelPrime_iff_not_dvd.mpr
    intro hdiv
    have hmap := congrArg
      (MvPolynomial.eval (fun _ : C => 0)) hdiv.choose_spec
    simp at hmap
  convert MvPolynomial.irreducible_mul_X_add
    (MvPolynomial.X d : R k)
    (-MvPolynomial.X b * MvPolynomial.X c - 1) a hd0 had hag hrel using 1
  all_goals simp [a, b, c, d]
  all_goals ring

omit [IsAlgClosed k] in
private lemma sl2Relation_span_isPrime :
    (Ideal.span ({sl2Relation k} : Set (R k))).IsPrime := by
  exact Ideal.isPrime_span_singleton_of_prime sl2Relation_irreducible.prime

private lemma sl2_vanishingIdeal :
    vanishingIdeal
        (Set.univ : Set (Variety.Point (slVariety k 2))) =
      Ideal.span ({sl2Relation k} : Set (R k)) := by
  ext p
  constructor
  · intro hp
    have hp' : p ∈ MvPolynomial.vanishingIdeal k
        (MvPolynomial.zeroLocus k
          (Ideal.span ({sl2Relation k} : Set (R k)))) := by
      intro x hx
      let y : Variety.Point (slVariety k 2) := ⟨x, by
        intro q hq
        change q ∈ ({slDetPoly 2 - 1} : Set (R k)) at hq
        rcases hq with rfl
        exact hx (sl2Relation k)
          (Ideal.subset_span (by rfl))⟩
      exact hp y (Set.mem_univ y)
    rw [MvPolynomial.vanishingIdeal_zeroLocus_eq_radical,
      sl2Relation_span_isPrime.radical] at hp'
    exact hp'
  · intro hp x _
    have hle : Ideal.span ({sl2Relation k} : Set (R k)) ≤
        RingHom.ker (MvPolynomial.eval x.val) := by
      apply Ideal.span_le.mpr
      intro q hq
      simp only [Set.mem_singleton_iff] at hq
      subst q
      change evalPolynomial x.val (slDetPoly 2 - 1) = 0
      exact x.isZero (slDetPoly 2 - 1) (by rfl)
    exact hle hp

omit [IsAlgClosed k] in
private lemma sl2Relation_homogeneous :
    sl2Relation k ∈
      MvPolynomial.weightedHomogeneousSubmodule k
        parityWeight 0 := by
  rw [sl2Relation_formula]
  apply MvPolynomial.IsWeightedHomogeneous.sub
  · apply MvPolynomial.IsWeightedHomogeneous.sub
    · rw [show (0 : ZMod 2) = 1 + 1 by decide]
      exact MvPolynomial.IsWeightedHomogeneous.mul
        (MvPolynomial.isWeightedHomogeneous_X
          _ parityWeight (ULift.up (0, 0)))
        (MvPolynomial.isWeightedHomogeneous_X
          _ parityWeight (ULift.up (1, 1)))
    · rw [show (0 : ZMod 2) = 1 + 1 by decide]
      exact MvPolynomial.IsWeightedHomogeneous.mul
        (MvPolynomial.isWeightedHomogeneous_X
          _ parityWeight (ULift.up (0, 1)))
        (MvPolynomial.isWeightedHomogeneous_X
          _ parityWeight (ULift.up (1, 0)))
  · exact MvPolynomial.isWeightedHomogeneous_one _ _

private abbrev sl2Ideal (k : Type u) [Field k] : Ideal (R k) :=
  Ideal.span ({sl2Relation k} : Set (R k))

private abbrev A (k : Type u) [Field k] := R k ⧸ sl2Ideal k

private def polynomialParity (k : Type u) [Field k] (z : ZMod 2) :
    Submodule k (R k) :=
  MvPolynomial.weightedHomogeneousSubmodule k parityWeight z

set_option linter.style.haveILetI false in
private lemma sl2Ideal_component_mem (k : Type u) [Field k] [IsAlgClosed k]
    {p : R k} (hp : p ∈ sl2Ideal k) (z : ZMod 2) :
    MvPolynomial.weightedHomogeneousComponent parityWeight z p ∈ sl2Ideal k := by
  letI := MvPolynomial.weightedDecomposition k parityWeight
  letI := MvPolynomial.weightedGradedAlgebra k parityWeight
  apply MvPolynomial.weightedHomogeneousComponent_mem_of_mem
    k parityWeight _ hp z
  apply Ideal.homogeneous_span
  intro q hq
  simp only [Set.mem_singleton_iff] at hq
  subst q
  exact ⟨0, sl2Relation_homogeneous⟩

private noncomputable def quotientParityComponent (z : ZMod 2) :
    A k →ₗ[k] A k where
  toFun q := Quotient.liftOn' q
    (fun p => Ideal.Quotient.mk (sl2Ideal k)
      (MvPolynomial.weightedHomogeneousComponent parityWeight z p)) (by
        intro p q hpq
        rw [Submodule.quotientRel_def] at hpq
        rw [Ideal.Quotient.mk_eq_mk_iff_sub_mem, ← map_sub]
        exact sl2Ideal_component_mem k hpq z)
  map_add' q r := by
    induction q using Quotient.inductionOn' with
    | _ p =>
      induction r using Quotient.inductionOn' with
      | _ q =>
        change Ideal.Quotient.mk (sl2Ideal k)
            (MvPolynomial.weightedHomogeneousComponent parityWeight z (p + q)) = _
        simp
  map_smul' c q := by
    induction q using Quotient.inductionOn' with
    | _ p =>
      change (Ideal.Quotient.mkₐ k (sl2Ideal k))
          (MvPolynomial.weightedHomogeneousComponent parityWeight z (c • p)) =
        c • (Ideal.Quotient.mkₐ k (sl2Ideal k))
          (MvPolynomial.weightedHomogeneousComponent parityWeight z p)
      simp

private def quotientParity (k : Type u) [Field k] [IsAlgClosed k] (z : ZMod 2) :
    Submodule k (A k) :=
  LinearMap.range (quotientParityComponent (k := k) z)

@[simp]
private lemma quotientParityComponent_mk (z : ZMod 2) (p : R k) :
    quotientParityComponent (k := k) z (Ideal.Quotient.mk (sl2Ideal k) p) =
      Ideal.Quotient.mk (sl2Ideal k)
        (MvPolynomial.weightedHomogeneousComponent parityWeight z p) := rfl

private lemma quotientParityComponent_comp (i z : ZMod 2) (q : A k) :
    quotientParityComponent (k := k) i
        (quotientParityComponent (k := k) z q) =
      if i = z then quotientParityComponent (k := k) z q else 0 := by
  induction q using Quotient.inductionOn' with
  | _ p =>
    change Ideal.Quotient.mk (sl2Ideal k)
        (MvPolynomial.weightedHomogeneousComponent parityWeight i
          (MvPolynomial.weightedHomogeneousComponent parityWeight z p)) =
      if i = z then Ideal.Quotient.mk (sl2Ideal k)
        (MvPolynomial.weightedHomogeneousComponent parityWeight z p) else 0
    rw [MvPolynomial.weightedHomogeneousComponent_of_mem
      (MvPolynomial.weightedHomogeneousComponent_mem parityWeight p z)]
    split_ifs <;> simp

private lemma quotientParityComponent_sum (q : A k) :
    quotientParityComponent (k := k) 0 q +
      quotientParityComponent (k := k) 1 q = q := by
  induction q using Quotient.inductionOn' with
  | _ p =>
    change Ideal.Quotient.mk (sl2Ideal k)
        (MvPolynomial.weightedHomogeneousComponent parityWeight 0 p) +
      Ideal.Quotient.mk (sl2Ideal k)
        (MvPolynomial.weightedHomogeneousComponent parityWeight 1 p) =
      Ideal.Quotient.mk (sl2Ideal k) p
    rw [← map_add]
    have huniv : (Finset.univ : Finset (ZMod 2)) = {0, 1} := by decide
    have hp := MvPolynomial.sum_weightedHomogeneousComponent
      (w := parityWeight) (φ := p)
    rw [finsum_eq_sum_of_fintype, huniv] at hp
    simpa using congrArg (Ideal.Quotient.mk (sl2Ideal k)) hp

private noncomputable def quotientParityInto (z : ZMod 2) :
    A k →ₗ[k] quotientParity k z where
  toFun q := ⟨quotientParityComponent (k := k) z q, ⟨q, rfl⟩⟩
  map_add' p q := by ext; simp
  map_smul' c q := by ext; simp

private noncomputable def quotientParityDecompose :
    A k →ₗ[k] ⨁ z : ZMod 2, quotientParity k z :=
  (DirectSum.lof k (ZMod 2) (fun z => quotientParity k z) 0).comp
      (quotientParityInto (k := k) 0) +
    (DirectSum.lof k (ZMod 2) (fun z => quotientParity k z) 1).comp
      (quotientParityInto (k := k) 1)

private lemma quotientParityDecompose_left :
    DirectSum.coeLinearMap (quotientParity k) ∘ₗ
        quotientParityDecompose (k := k) = LinearMap.id := by
  apply LinearMap.ext
  intro q
  change DirectSum.coeLinearMap (quotientParity k)
      (quotientParityDecompose (k := k) q) = q
  rw [quotientParityDecompose, LinearMap.add_apply, map_add,
    LinearMap.comp_apply, LinearMap.comp_apply,
    DirectSum.coeLinearMap_lof, DirectSum.coeLinearMap_lof]
  change quotientParityComponent (k := k) 0 q +
      quotientParityComponent (k := k) 1 q = q
  exact quotientParityComponent_sum q

private lemma quotientParityComponent_coe (z i : ZMod 2)
    (q : quotientParity k z) :
    quotientParityComponent (k := k) i q = if i = z then q else 0 := by
  rcases q.prop with ⟨a, ha⟩
  by_cases h : i = z
  · subst i
    simp only [if_pos]
    rw [← ha, quotientParityComponent_comp, if_pos rfl]
  · simp only [if_neg h, Submodule.coe_zero]
    rw [← ha, quotientParityComponent_comp, if_neg h]

private lemma quotientParityDecompose_right :
    quotientParityDecompose (k := k) ∘ₗ
        DirectSum.coeLinearMap (quotientParity k) = LinearMap.id := by
  ext z q i
  rcases StrongZModTwoGrading.zmod2_cases z with rfl | rfl <;>
    rcases StrongZModTwoGrading.zmod2_cases i with rfl | rfl <;>
    simp [quotientParityDecompose, quotientParityInto,
      quotientParityComponent_coe, DirectSum.lof_eq_of, DirectSum.of_apply]

private lemma quotientParity_mul_mem (i j : ZMod 2) {x y : A k}
    (hx : x ∈ quotientParity k i) (hy : y ∈ quotientParity k j) :
    x * y ∈ quotientParity k (i + j) := by
  rcases hx with ⟨x, rfl⟩
  rcases hy with ⟨y, rfl⟩
  induction x using Quotient.inductionOn' with
  | _ p =>
    induction y using Quotient.inductionOn' with
    | _ q =>
      refine ⟨Ideal.Quotient.mk (sl2Ideal k)
          (MvPolynomial.weightedHomogeneousComponent parityWeight i p *
            MvPolynomial.weightedHomogeneousComponent parityWeight j q), ?_⟩
      change Ideal.Quotient.mk (sl2Ideal k)
          (MvPolynomial.weightedHomogeneousComponent parityWeight (i + j)
            (MvPolynomial.weightedHomogeneousComponent parityWeight i p *
              MvPolynomial.weightedHomogeneousComponent parityWeight j q)) =
        Ideal.Quotient.mk (sl2Ideal k)
            (MvPolynomial.weightedHomogeneousComponent parityWeight i p) *
          Ideal.Quotient.mk (sl2Ideal k)
            (MvPolynomial.weightedHomogeneousComponent parityWeight j q)
      have hhom := MvPolynomial.IsWeightedHomogeneous.mul
        (MvPolynomial.weightedHomogeneousComponent_mem parityWeight p i)
        (MvPolynomial.weightedHomogeneousComponent_mem parityWeight q j)
      rw [MvPolynomial.weightedHomogeneousComponent_eq_self hhom]
      rfl

private noncomputable instance quotientParityGradedRing :
    GradedRing (quotientParity k) where
  one_mem := by
    refine ⟨Ideal.Quotient.mk (sl2Ideal k) 1, ?_⟩
    rw [quotientParityComponent_mk]
    change Ideal.Quotient.mk (sl2Ideal k)
        (MvPolynomial.weightedHomogeneousComponent parityWeight 0 1) = 1
    rw [MvPolynomial.weightedHomogeneousComponent_eq_self
      (MvPolynomial.isWeightedHomogeneous_one _ parityWeight)]
    exact map_one (Ideal.Quotient.mk (sl2Ideal k))
  mul_mem := fun i j _ _ hx hy => quotientParity_mul_mem i j hx hy
  toDecomposition := DirectSum.Decomposition.ofLinearMap (quotientParity k)
    (quotientParityDecompose (k := k)) quotientParityDecompose_left
      quotientParityDecompose_right

private def qX (i : C) : A k :=
  Ideal.Quotient.mk (sl2Ideal k) (MvPolynomial.X i)

private lemma qX_mem_one (i : C) : qX (k := k) i ∈ quotientParity k 1 := by
  refine ⟨qX (k := k) i, ?_⟩
  unfold qX
  rw [quotientParityComponent_mk,
    MvPolynomial.weightedHomogeneousComponent_eq_self]
  exact MvPolynomial.isWeightedHomogeneous_X k parityWeight i

private def strongX (i : Fin 2) : A k :=
  ![qX (k := k) (ULift.up (0, 0)), qX (k := k) (ULift.up (0, 1))] i

private def strongY (i : Fin 2) : A k :=
  ![qX (k := k) (ULift.up (1, 1)), -qX (k := k) (ULift.up (1, 0))] i

private lemma strongX_mem_one (i : Fin 2) :
    strongX (k := k) i ∈ quotientParity k 1 := by
  fin_cases i <;> simp [strongX, qX_mem_one]

private lemma strongY_mem_one (i : Fin 2) :
    strongY (k := k) i ∈ quotientParity k 1 := by
  fin_cases i
  · exact qX_mem_one _
  · exact (quotientParity k 1).neg_mem (qX_mem_one _)

omit [IsAlgClosed k] in
private lemma strong_sum :
    ∑ i, strongX (k := k) i * strongY (k := k) i = 1 := by
  rw [Fin.sum_univ_two]
  simp only [strongX, strongY, Matrix.cons_val_zero, Matrix.cons_val_one]
  simp only [qX, ← map_mul, ← map_neg, ← map_add]
  rw [← map_one (Ideal.Quotient.mk (sl2Ideal k)),
    Ideal.Quotient.eq]
  apply Ideal.subset_span
  simp only [Set.mem_singleton_iff]
  rw [sl2Relation_formula]
  ring

private theorem gradeZeroSubtype_faithfullyFlat :
    (SetLike.GradeZero.subring (quotientParity k)).subtype.FaithfullyFlat := by
  exact StrongZModTwoGrading.gradeZeroSubtype_faithfullyFlat
    (quotientParity k) (strongX (k := k)) (strongY (k := k))
      strongX_mem_one strongY_mem_one strong_sum

private noncomputable def sl2QuotientAlgEquiv :
    A k ≃ₐ[k] Variety.PolynomialFunction (slVariety k 2) :=
  (Ideal.quotientEquivAlgOfEq k sl2_vanishingIdeal.symm).trans
    (coordinateRingAlgEquivPolynomialFunction (slVariety k 2))

private noncomputable def sl2QuotientAlgEquivAt (n : ℕ) (h : n = 2) :
    A k ≃ₐ[k] Variety.PolynomialFunction (slVariety k n) := by
  subst n
  exact sl2QuotientAlgEquiv (k := k)

private noncomputable def sl2SourceQuotientAlgEquiv :
    A k ≃ₐ[k] Variety.PolynomialFunction
      (slVariety k (Module.finrank k (Fin 2 → k))) :=
  sl2QuotientAlgEquivAt (k := k) (Module.finrank k (Fin 2 → k)) (by simp)

private def sl2PolynomialAt (n : ℕ) (h : n = 2)
    (p : MvPolynomial (slVariety k n).Coordinates k) : R k := by
  subst n
  exact p

private lemma sl2PolynomialAt_C (n : ℕ) (h : n = 2) (r : k) :
    sl2PolynomialAt n h (MvPolynomial.C r) = MvPolynomial.C r := by
  subst n
  rfl

private noncomputable def pgl2PullbackToA :
    Variety.PolynomialFunction (pgl2Variety (k := k)) →+* A k := by
  exact (sl2SourceQuotientAlgEquiv (k := k)).symm.toRingHom.comp
    (pgl2Projection (k := k)).toVariety.pullbackRingHom

private lemma slTensorActionPolynomial_two_mem_zero
    (p : (slVariety k (2 * 2)).Coordinates) :
    slTensorActionPolynomial (k := k) 2 p ∈ polynomialParity k 0 := by
  rcases p with ⟨⟨p, q⟩⟩
  rcases hp : finProdFinEquiv.symm p with ⟨a, b⟩
  rcases hq : finProdFinEquiv.symm q with ⟨i, j⟩
  have hp' : p = finProdFinEquiv (a, b) := by
    simpa [hp] using (finProdFinEquiv.apply_symm_apply p).symm
  have hq' : q = finProdFinEquiv (i, j) := by
    simpa [hq] using (finProdFinEquiv.apply_symm_apply q).symm
  subst p
  subst q
  fin_cases a <;> fin_cases b <;> fin_cases i <;> fin_cases j <;>
    simp [slTensorActionPolynomial, slInvPoly, slEntryMatrix,
      Matrix.adjugate_fin_two] <;>
    change MvPolynomial.IsWeightedHomogeneous parityWeight _ 0 <;>
    rw [show (0 : ZMod 2) = 1 + 1 by decide] <;>
  all_goals
    exact MvPolynomial.IsWeightedHomogeneous.mul
      (MvPolynomial.isWeightedHomogeneous_X k parityWeight _)
      (MvPolynomial.isWeightedHomogeneous_X k parityWeight _)

private lemma tensorSubstitution_mem_zero
    (p : MvPolynomial (slVariety k (2 * 2)).Coordinates k) :
    MvPolynomial.bind₁ (slTensorActionPolynomial (k := k) 2) p ∈
      polynomialParity k 0 := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      rw [MvPolynomial.bind₁_C_right]
      exact MvPolynomial.isWeightedHomogeneous_C parityWeight a
  | add p q hp hq =>
      rw [map_add]
      exact (polynomialParity k 0).add_mem hp hq
  | mul_X p i hp =>
      rw [map_mul, MvPolynomial.bind₁_X_right]
      change MvPolynomial.IsWeightedHomogeneous parityWeight _ 0 at hp ⊢
      simpa using MvPolynomial.IsWeightedHomogeneous.mul hp
        (slTensorActionPolynomial_two_mem_zero i)

private lemma sl2QuotientAlgEquiv_symm_ofPolynomial (p : R k) :
    (sl2QuotientAlgEquiv (k := k)).symm
        (Variety.PolynomialFunction.ofPolynomial (slVariety k 2) p) =
      Ideal.Quotient.mk (sl2Ideal k) p := by
  apply (sl2QuotientAlgEquiv (k := k)).injective
  rw [(sl2QuotientAlgEquiv (k := k)).apply_symm_apply]
  change Variety.PolynomialFunction.ofPolynomial (slVariety k 2) p =
    coordinateRingAlgEquivPolynomialFunction (slVariety k 2)
      (Ideal.Quotient.mk
        (vanishingIdeal (Set.univ : Set (Variety.Point (slVariety k 2)))) p)
  rw [coordinateRingAlgEquivPolynomialFunction_mk]
  rfl

private lemma sl2QuotientAlgEquivAt_symm_ofPolynomial
    (n : ℕ) (h : n = 2)
    (p : MvPolynomial (slVariety k n).Coordinates k) :
    (sl2QuotientAlgEquivAt (k := k) n h).symm
        (Variety.PolynomialFunction.ofPolynomial (slVariety k n) p) =
      Ideal.Quotient.mk (sl2Ideal k) (sl2PolynomialAt n h p) := by
  subst n
  simpa [sl2QuotientAlgEquivAt, sl2PolynomialAt] using
    sl2QuotientAlgEquiv_symm_ofPolynomial (k := k) p

private lemma tensorSubstitutionAt_mem_zero
    (n : ℕ) (h : n = 2)
    (p : MvPolynomial (slVariety k (n * n)).Coordinates k) :
    sl2PolynomialAt n h
        (MvPolynomial.bind₁ (slTensorActionPolynomial (k := k) n) p) ∈
      polynomialParity k 0 := by
  subst n
  simpa [sl2PolynomialAt] using tensorSubstitution_mem_zero (k := k) p

private def coordinateAt (n : ℕ) (h : n = 2)
    (c : (slVariety k (2 * 2)).Coordinates) :
    (slVariety k (n * n)).Coordinates := by
  subst n
  exact c

private lemma slTensorActionPolynomial_coordinateAt
    (n : ℕ) (h : n = 2) (c : (slVariety k (2 * 2)).Coordinates) :
    sl2PolynomialAt n h
        (slTensorActionPolynomial (k := k) n (coordinateAt n h c)) =
      slTensorActionPolynomial (k := k) 2 c := by
  subst n
  rfl

private def finTwoFlip (i : Fin 2) : Fin 2 := ![1, 0] i

private def tensorCoordinateFor (u v : C) :
    (slVariety k (2 * 2)).Coordinates :=
  ULift.up
    (finProdFinEquiv (finTwoFlip u.down.1, v.down.1),
      finProdFinEquiv (finTwoFlip u.down.2, v.down.2))

private lemma tensorCoordinateFor_formula (u v : C) :
    slTensorActionPolynomial (k := k) 2 (tensorCoordinateFor (k := k) u v) =
      (if u.down.1 = u.down.2 then 1 else -1) *
        MvPolynomial.X u * MvPolynomial.X v := by
  rcases u with ⟨⟨ur, uc⟩⟩
  rcases v with ⟨⟨vr, vc⟩⟩
  fin_cases ur <;> fin_cases uc <;> fin_cases vr <;> fin_cases vc <;>
    simp [tensorCoordinateFor, finTwoFlip, slTensorActionPolynomial,
      slInvPoly, slEntryMatrix, Matrix.adjugate_fin_two]

private lemma pgl2Projection_pullback_ofPolynomial
    (p : MvPolynomial (pgl2Variety (k := k)).Coordinates k) :
    (pgl2Projection (k := k)).toVariety.pullbackRingHom
        (Variety.PolynomialFunction.ofPolynomial (pgl2Variety (k := k)) p) =
      Variety.PolynomialFunction.ofPolynomial
        (slVariety k (Module.finrank k (Fin 2 → k)))
        (MvPolynomial.bind₁
          (slTensorActionPolynomial (k := k)
            (Module.finrank k (Fin 2 → k))) p) := by
  apply Variety.PolynomialFunction.ext
  intro x
  change evalPolynomial ((pgl2Projection (k := k)).onPoints x).val p =
    evalPolynomial x.val (MvPolynomial.bind₁
      (slTensorActionPolynomial (k := k)
        (Module.finrank k (Fin 2 → k))) p)
  rw [evalPolynomial_bind₁]
  congr 1
  funext c
  rcases c with ⟨⟨cr, cc⟩⟩
  let c : (slVariety k
      (Module.finrank k (Fin 2 → k) * Module.finrank k (Fin 2 → k))).Coordinates :=
    ULift.up (cr, cc)
  change ((pgl2Projection (k := k)).onPoints x).val c =
    evalPolynomial x.val
      (slTensorActionPolynomial (Module.finrank k (Fin 2 → k)) c)
  have hinc := pgl2Projection_inclusion_apply (k := k) x
  have hc := congrArg
    (fun y : Variety.Point
        (slVariety k
          (Module.finrank k (Fin 2 → k) * Module.finrank k (Fin 2 → k))) =>
      y.val c) hinc
  change ((pgl2Projection (k := k)).onPoints x).val c =
    ((pgl2TensorMorphism (k := k)).onPoints x).val c at hc
  rw [hc]
  let n := Module.finrank k (Fin 2 → k)
  have ht := slTensorActionMorphism_onPoints (k := k) n x
  have htc := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin (n * n)) k =>
      A.1 c.down.1 c.down.2) ht
  change ((slTensorActionMorphism (k := k) n).onPoints x).val c =
    slTensorActionMatrix n (slPointEquiv n x) c.down.1 c.down.2 at htc
  calc
    ((pgl2TensorMorphism (k := k)).onPoints x).val c =
        slTensorActionMatrix n (slPointEquiv n x) c.down.1 c.down.2 := by
      simpa [n, pgl2TensorMorphism] using htc
    _ = evalPolynomial x.val (slTensorActionPolynomial n c) :=
      (slTensorActionPolynomial_eval (k := k) n x c).symm

private lemma pgl2PullbackToA_coordinate
    (h : Module.finrank k (Fin 2 → k) = 2)
    (c : (slVariety k (2 * 2)).Coordinates) :
    pgl2PullbackToA (k := k)
        (Variety.PolynomialFunction.ofPolynomial (pgl2Variety (k := k))
          (MvPolynomial.X (coordinateAt
            (Module.finrank k (Fin 2 → k)) h c))) =
      Ideal.Quotient.mk (sl2Ideal k)
        (slTensorActionPolynomial (k := k) 2 c) := by
  rw [pgl2PullbackToA, RingHom.comp_apply,
    pgl2Projection_pullback_ofPolynomial]
  let n := Module.finrank k (Fin 2 → k)
  change (sl2QuotientAlgEquivAt (k := k) n _).symm
      (Variety.PolynomialFunction.ofPolynomial (slVariety k n)
        (MvPolynomial.bind₁ (slTensorActionPolynomial (k := k) n)
          (MvPolynomial.X (coordinateAt n h c)))) = _
  rw [MvPolynomial.bind₁_X_right,
    sl2QuotientAlgEquivAt_symm_ofPolynomial,
    slTensorActionPolynomial_coordinateAt]

private lemma pgl2PullbackToA_C (r : k) :
    pgl2PullbackToA (k := k)
        (Variety.PolynomialFunction.ofPolynomial (pgl2Variety (k := k))
          (MvPolynomial.C r)) =
      Ideal.Quotient.mk (sl2Ideal k) (MvPolynomial.C r) := by
  rw [pgl2PullbackToA, RingHom.comp_apply,
    pgl2Projection_pullback_ofPolynomial]
  change (sl2QuotientAlgEquivAt (k := k)
      (Module.finrank k (Fin 2 → k)) _).symm
      (Variety.PolynomialFunction.ofPolynomial
        (slVariety k (Module.finrank k (Fin 2 → k)))
        (MvPolynomial.bind₁
          (slTensorActionPolynomial (k := k)
            (Module.finrank k (Fin 2 → k))) (MvPolynomial.C r))) = _
  rw [MvPolynomial.bind₁_C_right,
    sl2QuotientAlgEquivAt_symm_ofPolynomial,
    sl2PolynomialAt_C]

private lemma qX_mul_qX_mem_range (u v : C) :
    qX (k := k) u * qX (k := k) v ∈
      (pgl2PullbackToA (k := k)).range := by
  let h : Module.finrank k (Fin 2 → k) = 2 := by simp
  let g := Variety.PolynomialFunction.ofPolynomial (pgl2Variety (k := k))
    (MvPolynomial.X (coordinateAt
      (Module.finrank k (Fin 2 → k)) h (tensorCoordinateFor (k := k) u v)))
  by_cases huv : u.down.1 = u.down.2
  · refine ⟨g, ?_⟩
    rw [pgl2PullbackToA_coordinate, tensorCoordinateFor_formula, if_pos huv]
    simp only [one_mul, qX, ← map_mul]
  · refine ⟨-g, ?_⟩
    rw [map_neg, pgl2PullbackToA_coordinate,
      tensorCoordinateFor_formula, if_neg huv]
    simp only [qX, ← map_mul, ← map_neg]
    ring_nf

private lemma list_prod_qX_mem_range :
    ∀ l : List C, Even l.length →
      (l.map (qX (k := k))).prod ∈ (pgl2PullbackToA (k := k)).range := by
  intro l hl
  induction l using List.twoStepInduction with
  | nil => simp
  | singleton u => simp at hl
  | cons_cons u v l ih _ =>
      have hl' : Even l.length := by
        rcases hl with ⟨m, hm⟩
        use m - 1
        simp only [List.length_cons] at hm
        omega
      simpa [mul_assoc] using
        (pgl2PullbackToA (k := k)).range.mul_mem
          (qX_mul_qX_mem_range (k := k) u v) (ih hl')

omit [IsAlgClosed k] in
private lemma qX_toMultiset_prod (d : C →₀ ℕ) :
    (d.toMultiset.map (qX (k := k))).prod =
      Ideal.Quotient.mk (sl2Ideal k)
        (d.prod fun u n => MvPolynomial.X u ^ n) := by
  induction d using Finsupp.induction with
  | zero => simp
  | @single_add u n d hu hn ih =>
      rw [Finsupp.toMultiset_add, Multiset.map_add, Multiset.prod_add, ih,
        Finsupp.toMultiset_single, Multiset.map_nsmul,
        Multiset.map_singleton, Multiset.prod_nsmul, Multiset.prod_singleton,
        Finsupp.prod_add_index' (by intro; simp) (by intros; simp [pow_add]),
        Finsupp.prod_single_index (by simp)]
      simp only [qX, ← map_pow, ← map_mul]

private lemma parityWeight_eq_card (d : C →₀ ℕ) :
    Finsupp.weight parityWeight d = (d.toMultiset.card : ZMod 2) := by
  rw [Finsupp.weight_apply, Finsupp.card_toMultiset]
  simp [parityWeight]

private lemma monomial_mem_range (d : C →₀ ℕ) (r : k)
    (hd : Finsupp.weight parityWeight d = 0) :
    Ideal.Quotient.mk (sl2Ideal k) (MvPolynomial.monomial d r) ∈
      (pgl2PullbackToA (k := k)).range := by
  have hcard : Even d.toMultiset.card := by
    rw [← ZMod.natCast_eq_zero_iff_even, ← parityWeight_eq_card]
    exact hd
  have hprod := list_prod_qX_mem_range (k := k) d.toMultiset.toList (by
    simpa using hcard)
  rw [Multiset.prod_map_toList, qX_toMultiset_prod] at hprod
  rw [MvPolynomial.monomial_eq, map_mul]
  exact (pgl2PullbackToA (k := k)).range.mul_mem
    ⟨Variety.PolynomialFunction.ofPolynomial (pgl2Variety (k := k))
      (MvPolynomial.C r), pgl2PullbackToA_C r⟩ hprod

private lemma homogeneous_zero_mk_mem_range (p : R k)
    (hp : p ∈ polynomialParity k 0) :
    Ideal.Quotient.mk (sl2Ideal k) p ∈
      (pgl2PullbackToA (k := k)).range := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      rw [map_add]
      exact (pgl2PullbackToA (k := k)).range.add_mem ihp ihq
  | monomial d r hd => exact monomial_mem_range d r hd

private lemma quotientParity_zero_le_range :
    (SetLike.GradeZero.subring (quotientParity k) : Set (A k)) ⊆
      (pgl2PullbackToA (k := k)).range := by
  intro q hq
  rcases hq with ⟨a, rfl⟩
  induction a using Quotient.inductionOn' with
  | _ p =>
      change quotientParityComponent (k := k) 0
        (Ideal.Quotient.mk (sl2Ideal k) p) ∈
          (pgl2PullbackToA (k := k)).range
      rw [quotientParityComponent_mk]
      exact homogeneous_zero_mk_mem_range _
        (MvPolynomial.weightedHomogeneousComponent_mem parityWeight p 0)

private lemma pgl2Projection_surjective :
    Function.Surjective (pgl2Projection (k := k)).onPoints := by
  exact (pgl2TensorMorphism (k := k)).codRestrictImageClosedSubgroup_surjective
    (fun x => ⟨x, rfl⟩)

private lemma pgl2PullbackToA_injective :
    Function.Injective (pgl2PullbackToA (k := k)) := by
  intro f g hfg
  apply Variety.PolynomialFunction.ext
  intro y
  obtain ⟨x, rfl⟩ := pgl2Projection_surjective (k := k) y
  have hpull :
      (pgl2Projection (k := k)).toVariety.pullbackRingHom f =
        (pgl2Projection (k := k)).toVariety.pullbackRingHom g := by
    exact (sl2SourceQuotientAlgEquiv (k := k)).symm.injective hfg
  exact congrArg
    (fun h : Variety.PolynomialFunction
        (slVariety k (Module.finrank k (Fin 2 → k))) => h x) hpull

private lemma pgl2PullbackToA_mem_zero
    (f : Variety.PolynomialFunction (pgl2Variety (k := k))) :
    pgl2PullbackToA (k := k) f ∈ quotientParity k 0 := by
  rcases f.representedBy with ⟨p, hp⟩
  have hf : f = Variety.PolynomialFunction.ofPolynomial
      (pgl2Variety (k := k)) p := by
    apply Variety.PolynomialFunction.ext
    intro x
    exact hp x
  subst f
  rw [pgl2PullbackToA, RingHom.comp_apply,
    pgl2Projection_pullback_ofPolynomial]
  let n := Module.finrank k (Fin 2 → k)
  have h : n = 2 := by simp [n]
  change (sl2QuotientAlgEquivAt (k := k) n _).symm
    (Variety.PolynomialFunction.ofPolynomial (slVariety k n)
      (MvPolynomial.bind₁ (slTensorActionPolynomial (k := k) n) p)) ∈
        quotientParity k 0
  rw [sl2QuotientAlgEquivAt_symm_ofPolynomial]
  refine ⟨Ideal.Quotient.mk (sl2Ideal k)
      (sl2PolynomialAt n h
        (MvPolynomial.bind₁ (slTensorActionPolynomial (k := k) n) p)), ?_⟩
  rw [quotientParityComponent_mk,
    MvPolynomial.weightedHomogeneousComponent_eq_self
      (tensorSubstitutionAt_mem_zero n h p)]

private lemma pgl2PullbackToA_range :
    (pgl2PullbackToA (k := k)).range =
      SetLike.GradeZero.subring (quotientParity k) := by
  ext q
  constructor
  · rintro ⟨f, rfl⟩
    exact pgl2PullbackToA_mem_zero f
  · intro hq
    exact quotientParity_zero_le_range (k := k) hq

private noncomputable def pgl2EvenRingHom :
    Variety.PolynomialFunction (pgl2Variety (k := k)) →+*
      SetLike.GradeZero.subring (quotientParity k) :=
  (pgl2PullbackToA (k := k)).codRestrict _ pgl2PullbackToA_mem_zero

private lemma pgl2EvenRingHom_bijective :
    Function.Bijective (pgl2EvenRingHom (k := k)) := by
  constructor
  · intro f g hfg
    apply pgl2PullbackToA_injective (k := k)
    exact congrArg Subtype.val hfg
  · intro q
    have hq : (q : A k) ∈ (pgl2PullbackToA (k := k)).range := by
      rw [pgl2PullbackToA_range]
      exact q.property
    rcases hq with ⟨f, hf⟩
    refine ⟨f, Subtype.ext ?_⟩
    exact hf

private theorem pgl2PullbackToA_faithfullyFlat :
    (pgl2PullbackToA (k := k)).FaithfullyFlat := by
  let e := RingEquiv.ofBijective (pgl2EvenRingHom (k := k))
    (pgl2EvenRingHom_bijective (k := k))
  have he : e.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective e.bijective
  have hcomp := RingHom.FaithfullyFlat.stableUnderComposition
    e.toRingHom (SetLike.GradeZero.subring (quotientParity k)).subtype
      he (gradeZeroSubtype_faithfullyFlat (k := k))
  change (pgl2PullbackToA (k := k)).FaithfullyFlat at hcomp
  exact hcomp

/-- Pullback along the tensor-model projection `SL2 -> PGL2` is faithfully
flat on rings of polynomial functions. -/
theorem pgl2Projection_pullbackRingHom_faithfullyFlat :
    (pgl2Projection (k := k)).toVariety.pullbackRingHom.FaithfullyFlat := by
  let e := sl2SourceQuotientAlgEquiv (k := k)
  have he : e.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective e.bijective
  have hcomp := RingHom.FaithfullyFlat.stableUnderComposition
    (pgl2PullbackToA (k := k)) e.toRingHom
      (pgl2PullbackToA_faithfullyFlat (k := k)) he
  have heq : e.toRingHom.comp (pgl2PullbackToA (k := k)) =
      (pgl2Projection (k := k)).toVariety.pullbackRingHom := by
    apply RingHom.ext
    intro f
    change e (e.symm
      ((pgl2Projection (k := k)).toVariety.pullbackRingHom f)) = _
    exact e.apply_symm_apply _
  rw [← heq]
  exact hcomp

/-- The coordinate-ring map used by the affine geometric realization of the
projection is faithfully flat. -/
theorem pgl2Projection_ofAffinePullback_faithfullyFlat :
    (Variety.Geometric.ofAffinePullback
      (pgl2Projection (k := k)).toVariety).toRingHom.FaithfullyFlat := by
  let f := (pgl2Projection (k := k)).toVariety
  let eW := coordinateRingAlgEquivPolynomialFunction (pgl2Variety (k := k))
  let eV := coordinateRingAlgEquivPolynomialFunction
    (slVariety k (Module.finrank k (Fin 2 → k)))
  have hW : eW.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective eW.bijective
  have hf : f.pullbackAlgHom.toRingHom.FaithfullyFlat := by
    change f.pullbackRingHom.FaithfullyFlat
    exact pgl2Projection_pullbackRingHom_faithfullyFlat (k := k)
  have hcomp :
      (f.pullbackAlgHom.toRingHom.comp eW.toRingHom).FaithfullyFlat :=
    RingHom.FaithfullyFlat.stableUnderComposition
      eW.toRingHom f.pullbackAlgHom.toRingHom hW hf
  have hV : eV.symm.toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective eV.symm.bijective
  exact RingHom.FaithfullyFlat.stableUnderComposition
    (f.pullbackAlgHom.toRingHom.comp eW.toRingHom)
    eV.symm.toRingHom hcomp hV

namespace Variety.Geometric

/-- The affine geometric morphism induced by `pgl2Projection`. -/
noncomputable abbrev pgl2ProjectionGeometric :
    Morphism
      (ofAffine (slVariety k (Module.finrank k (Fin 2 → k))))
      (ofAffine (pgl2Variety (k := k))) :=
  ofAffine_morphism (pgl2Projection (k := k)).toVariety

/-- The affine geometric `SL2 -> PGL2` projection is flat and surjective. -/
theorem pgl2ProjectionGeometric_flat_and_surjective :
    AlgebraicGeometry.Flat (pgl2ProjectionGeometric (k := k)).hom ∧
      AlgebraicGeometry.Surjective (pgl2ProjectionGeometric (k := k)).hom := by
  change AlgebraicGeometry.Flat
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (ofAffinePullback (pgl2Projection (k := k)).toVariety).toRingHom)) ∧
    AlgebraicGeometry.Surjective
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (ofAffinePullback (pgl2Projection (k := k)).toVariety).toRingHom))
  exact (AlgebraicGeometry.flat_and_surjective_SpecMap_iff
    (CommRingCat.ofHom
      (ofAffinePullback (pgl2Projection (k := k)).toVariety).toRingHom)).mpr
    (pgl2Projection_ofAffinePullback_faithfullyFlat (k := k))

/-- Flatness instance for the geometric projection. -/
instance pgl2ProjectionGeometric_flat :
    AlgebraicGeometry.Flat (pgl2ProjectionGeometric (k := k)).hom :=
  (pgl2ProjectionGeometric_flat_and_surjective (k := k)).1

/-- Surjectivity instance for the geometric projection. -/
instance pgl2ProjectionGeometric_surjective :
    AlgebraicGeometry.Surjective (pgl2ProjectionGeometric (k := k)).hom :=
  (pgl2ProjectionGeometric_flat_and_surjective (k := k)).2

set_option linter.style.haveILetI false in
/-- Quasi-compactness of the geometric projection, obtained from the
quasi-compact structure maps of geometric varieties. -/
instance pgl2ProjectionGeometric_quasiCompact :
    AlgebraicGeometry.QuasiCompact (pgl2ProjectionGeometric (k := k)).hom := by
  haveI : AlgebraicGeometry.QuasiCompact
      ((pgl2ProjectionGeometric (k := k)).hom ≫
        (ofAffine (pgl2Variety (k := k))).structureMap) := by
    rw [(pgl2ProjectionGeometric (k := k)).commutes]
    infer_instance
  exact AlgebraicGeometry.QuasiCompact.of_comp
    (pgl2ProjectionGeometric (k := k)).hom
    (ofAffine (pgl2Variety (k := k))).structureMap

/-- The geometric projection is an fpqc effective epimorphism. -/
theorem pgl2ProjectionGeometric_effectiveEpi :
    CategoryTheory.EffectiveEpi (pgl2ProjectionGeometric (k := k)).hom := by
  infer_instance

/-- Every base change of the geometric projection remains flat and
surjective. -/
theorem pgl2ProjectionGeometric_baseChange_flat_and_surjective
    {X : AlgebraicGeometry.Scheme}
    (f : X ⟶ (ofAffine (pgl2Variety (k := k))).toScheme) :
    AlgebraicGeometry.Flat
        (CategoryTheory.Limits.pullback.fst f
          (pgl2ProjectionGeometric (k := k)).hom) ∧
      AlgebraicGeometry.Surjective
        (CategoryTheory.Limits.pullback.fst f
          (pgl2ProjectionGeometric (k := k)).hom) := by
  constructor <;> infer_instance

/-- Every base change of the geometric projection is an fpqc effective
epimorphism. -/
theorem pgl2ProjectionGeometric_baseChange_effectiveEpi
    {X : AlgebraicGeometry.Scheme}
    (f : X ⟶ (ofAffine (pgl2Variety (k := k))).toScheme) :
    CategoryTheory.EffectiveEpi
      (CategoryTheory.Limits.pullback.fst f
        (pgl2ProjectionGeometric (k := k)).hom) := by
  infer_instance

/-- The base-changed projection over `PGL2 x P1`, formed along the first
projection to `PGL2`. -/
noncomputable abbrev pgl2ProjectionProjectiveLineBaseChange :
    CategoryTheory.Limits.pullback
        (fst (ofAffine (pgl2Variety (k := k))) (projectiveLine k)).hom
        (pgl2ProjectionGeometric (k := k)).hom ⟶
      (prod (ofAffine (pgl2Variety (k := k))) (projectiveLine k)).toScheme :=
  CategoryTheory.Limits.pullback.fst
    (fst (ofAffine (pgl2Variety (k := k))) (projectiveLine k)).hom
    (pgl2ProjectionGeometric (k := k)).hom

/-- The base-changed projection over `PGL2 x P1` is flat and surjective. -/
theorem pgl2ProjectionProjectiveLineBaseChange_flat_and_surjective :
    AlgebraicGeometry.Flat
        (pgl2ProjectionProjectiveLineBaseChange (k := k)) ∧
      AlgebraicGeometry.Surjective
        (pgl2ProjectionProjectiveLineBaseChange (k := k)) := by
  exact pgl2ProjectionGeometric_baseChange_flat_and_surjective
    (fst (ofAffine (pgl2Variety (k := k))) (projectiveLine k)).hom

/-- The base-changed projection over `PGL2 x P1` is an effective
epimorphism, providing the descent interface for the projective action. -/
theorem pgl2ProjectionProjectiveLineBaseChange_effectiveEpi :
    CategoryTheory.EffectiveEpi
      (pgl2ProjectionProjectiveLineBaseChange (k := k)) := by
  exact pgl2ProjectionGeometric_baseChange_effectiveEpi
    (fst (ofAffine (pgl2Variety (k := k))) (projectiveLine k)).hom

end Variety.Geometric

end
end Theory.AlgebraicGroup
