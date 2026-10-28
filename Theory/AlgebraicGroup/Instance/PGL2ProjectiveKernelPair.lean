module

public import Theory.AlgebraicGroup.Instance.PGL2
public import Theory.AlgebraicGroup.Representations.Algebraic.Natural
public import Theory.AlgebraicGroup.Variety.ProjectiveLinearAction
public import Theory.AlgebraicGroup.Variety.ProjVeroneseExt
-- The bridge proof unfolds the internal polynomial-Proj base-change maps.
import all Theory.AlgebraicGroup.Variety.PolynomialProjBaseChange
-- The point bridge uses the coordinate action formula underlying the public action.
import all Theory.AlgebraicGroup.Variety.ProjectiveLinearAction

/-!
# Kernel-pair invariance of the `SL₂` projective action

This module restricts the genuine general-linear action on projective one-space to
`SL₂` and proves that its two base changes to the affine scheme-theoretic kernel
pair of `pgl2Projection : SL₂ ⟶ PGL₂` agree.  The exported equality
`sl2ProjectiveKernelPair_familyMap_eq` is the cocycle condition used to descend the
action through the faithfully flat projection to `PGL₂`.

On coordinate rings the kernel pair is
`k[SL₂] ⊗[k[PGL₂]] k[SL₂]`.  Equality of the two maps from `k[PGL₂]`
identifies the coefficients of the tensor representation `A ↦ (A⁻¹)ᵀ ⊗ A`.
The two-dimensional adjugate formula then identifies every quadratic product of
matrix entries on the two factors.  Hence the two homogeneous substitutions for
the projective action agree in degree two, and therefore in every even degree.
Even-degree extensionality for polynomial `Proj` turns this ring calculation into
an equality of scheme morphisms after product with projective space.

The module also identifies these coordinate families with the genuine regular
`SL₂` action.  It exports the two maps from the kernel-pair family source to
`SL₂ × P¹`; coefficient base change intertwines the general-linear and
special-linear homogeneous substitutions, and functoriality of `Proj.map`
identifies their composites with the two coordinate families.

The proof takes place in the full tensor-product coordinate ring and uses no
reducedness or rational-point kernel argument.  It is consequently valid in every
characteristic, including the nonreduced `μ₂` kernel in characteristic two.  The
geometric setup follows Borel, *Linear Algebraic Groups*, Section 7.2, with the
scheme-theoretic descent step made explicit.
-/

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped TensorProduct

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u v

variable {k : Type u} [Field k] [IsAlgClosed k]

private theorem finrankFinTwo : Module.finrank k (Fin 2 -> k) = 2 := by
  rw [Module.finrank_fin_fun k]

private noncomputable def affineCoordinate
    (V : Variety k) (c : V.Coordinates) : coordinateRing V :=
  (coordinateRingAlgEquivPolynomialFunction V).symm
    (Variety.PolynomialFunction.ofPolynomial V (MvPolynomial.X c))

@[simp] private theorem coordinatePointAlgHom_affineCoordinate
    (V : Variety k) (x : Variety.Point V) (c : V.Coordinates) :
    coordinatePointAlgHom V x (affineCoordinate V c) = x.val c := by
  simp [affineCoordinate, Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun, evalPolynomial]

private theorem coordinatePointAlgHom_ofAffinePullback
    {V W : Variety k} (f : V.Morphism W) (x : V.Point)
    (a : coordinateRing W) :
    coordinatePointAlgHom V x (ofAffinePullback f a) =
      coordinatePointAlgHom W (f.toFun x) a := by
  have h := coordinateRingPointAlgHomEquiv_morphism_apply f x
  exact (AlgHom.congr_fun h a).symm

private noncomputable abbrev rankTwo (k : Type u) [Field k] :=
  Module.finrank k (Fin 2 -> k)

private noncomputable abbrev SLRankTwo : Variety k := slVariety k (rankTwo k)

private noncomputable def slRankTwoToGL :
    AlgebraicGroup.Morphism (SLRankTwo (k := k))
      (glVariety (rankTwo k) : Variety k) :=
  specialLinearToGeneralLinearMorphism (k := k) (rankTwo k)

private noncomputable def slRankTwoEntry (i j : Fin (rankTwo k)) :
    coordinateRing (SLRankTwo (k := k)) :=
  ofAffinePullback (slRankTwoToGL (k := k)).toVariety
    (glEntry (rankTwo k) i j)

private noncomputable def slRankTwoInverseEntry (i j : Fin (rankTwo k)) :
    coordinateRing (SLRankTwo (k := k)) :=
  ofAffinePullback (slRankTwoToGL (k := k)).toVariety
    (glInverseEntry (rankTwo k) i j)

@[simp] private theorem coordinatePointAlgHom_slRankTwoEntry
    (x : Variety.Point (SLRankTwo (k := k)))
    (i j : Fin (rankTwo k)) :
    coordinatePointAlgHom (SLRankTwo (k := k)) x
        (slRankTwoEntry (k := k) i j) =
      (slPointEquiv (rankTwo k) x).1 i j := by
  rw [slRankTwoEntry, coordinatePointAlgHom_ofAffinePullback,
    coordinatePointAlgHom_glEntry]
  rfl

@[simp] private theorem coordinatePointAlgHom_slRankTwoInverseEntry
    (x : Variety.Point (SLRankTwo (k := k)))
    (i j : Fin (rankTwo k)) :
    coordinatePointAlgHom (SLRankTwo (k := k)) x
        (slRankTwoInverseEntry (k := k) i j) =
      Matrix.adjugate (slPointEquiv (rankTwo k) x).1 i j := by
  rw [slRankTwoInverseEntry, coordinatePointAlgHom_ofAffinePullback,
    coordinatePointAlgHom_glInverseEntry]
  have hmat :
      ((glPointEquiv (rankTwo k)
          ((slRankTwoToGL (k := k)).toVariety.toFun x) :
          GL (Fin (rankTwo k)) k) :
        Matrix (Fin (rankTwo k)) (Fin (rankTwo k)) k) =
      (slPointEquiv (rankTwo k) x).1 := by
    rfl
  rw [hmat, Matrix.nonsing_inv_apply
    (A := (slPointEquiv (rankTwo k) x).1)
    (by simpa using (slPointEquiv (rankTwo k) x).2)]
  simp

private noncomputable def pgl2TensorCoordinateRank
    (a b i j : Fin (rankTwo k)) : (pgl2Variety (k := k)).Coordinates :=
  ULift.up (finProdFinEquiv (a, b), finProdFinEquiv (i, j))

private noncomputable def pgl2TensorEntryRank
    (a b i j : Fin (rankTwo k)) : coordinateRing (pgl2Variety (k := k)) :=
  affineCoordinate (pgl2Variety (k := k))
    (pgl2TensorCoordinateRank (k := k) a b i j)

private theorem pgl2Projection_pullback_tensorEntryRank
    (a b i j : Fin (rankTwo k)) :
    ofAffinePullback (pgl2Projection (k := k)).toVariety
        (pgl2TensorEntryRank (k := k) a b i j) =
      slRankTwoInverseEntry (k := k) i a *
        slRankTwoEntry (k := k) b j := by
  apply (coordinateRingAlgEquivPolynomialFunction
    (SLRankTwo (k := k))).injective
  apply Variety.PolynomialFunction.ext
  intro x
  change coordinatePointAlgHom (SLRankTwo (k := k)) x
      (ofAffinePullback (pgl2Projection (k := k)).toVariety
        (pgl2TensorEntryRank (k := k) a b i j)) =
    coordinatePointAlgHom (SLRankTwo (k := k)) x
      (slRankTwoInverseEntry (k := k) i a *
        slRankTwoEntry (k := k) b j)
  rw [coordinatePointAlgHom_ofAffinePullback, pgl2TensorEntryRank,
    coordinatePointAlgHom_affineCoordinate, map_mul,
    coordinatePointAlgHom_slRankTwoInverseEntry,
    coordinatePointAlgHom_slRankTwoEntry]
  have hprojection := congrArg
    (fun y : Variety.Point
        (slVariety k (rankTwo k * rankTwo k)) ↦
      y.val (pgl2TensorCoordinateRank (k := k) a b i j))
    (pgl2Projection_inclusion_apply (k := k) x)
  rw [show Matrix.adjugate (slPointEquiv (rankTwo k) x).1 i a =
      ((slPointEquiv (rankTwo k) x)⁻¹).1 i a by
    rw [Matrix.SpecialLinearGroup.coe_inv]]
  rw [← slTensorActionMatrix_apply (rankTwo k)
    (slPointEquiv (rankTwo k) x) a b i j]
  have ht := congrArg
    (fun A : Matrix.SpecialLinearGroup (Fin (rankTwo k * rankTwo k)) k ↦
      A.1 (finProdFinEquiv (a, b)) (finProdFinEquiv (i, j)))
    (slTensorActionMorphism_onPoints (k := k) (rankTwo k) x)
  calc
    (pgl2Projection.toVariety.toFun x).val
          (pgl2TensorCoordinateRank (k := k) a b i j) =
        ((pgl2ClosedSubgroup (k := k)).inclusion.onPoints
          (pgl2Projection.onPoints x)).val
            (pgl2TensorCoordinateRank (k := k) a b i j) := rfl
    _ = (pgl2TensorMorphism.onPoints x).val
          (pgl2TensorCoordinateRank (k := k) a b i j) := hprojection
    _ = (slTensorActionHom (rankTwo k) (slPointEquiv (rankTwo k) x)).1
          (finProdFinEquiv (a, b)) (finProdFinEquiv (i, j)) := ht
    _ = slTensorActionMatrix (rankTwo k) (slPointEquiv (rankTwo k) x)
          (finProdFinEquiv (a, b)) (finProdFinEquiv (i, j)) := rfl

private theorem slRankTwoInverseEntry_mul_entry
    (i j : Fin (rankTwo k)) :
    ∑ l : Fin (rankTwo k), slRankTwoInverseEntry (k := k) i l *
        slRankTwoEntry (k := k) l j = if i = j then 1 else 0 := by
  change ∑ l : Fin (rankTwo k),
      ofAffinePullback (slRankTwoToGL (k := k)).toVariety
          (glInverseEntry (rankTwo k) i l) *
        ofAffinePullback (slRankTwoToGL (k := k)).toVariety
          (glEntry (rankTwo k) l j) = _
  have h := congrArg (ofAffinePullback (slRankTwoToGL (k := k)).toVariety)
    (glInverseEntry_mul_entry (k := k) (rankTwo k) i j)
  by_cases hij : i = j
  · simpa only [map_sum, map_mul, hij, if_true, map_one] using h
  · simpa only [map_sum, map_mul, hij, if_false, map_zero] using h

private noncomputable def slProjectiveSubstitution
    {R : Type v} [CommRing R]
    (phi : coordinateRing (SLRankTwo (k := k)) →+* R) :
    projectiveGrading R (Fin (rankTwo k)) →+*ᵍ
      projectiveGrading R (Fin (rankTwo k)) :=
  GradedRingHom.mk
    (MvPolynomial.eval₂Hom MvPolynomial.C (fun i ↦
      ∑ j : Fin (rankTwo k),
        MvPolynomial.C (phi (slRankTwoEntry (k := k) i j)) * MvPolynomial.X j))
    fun {d} p hp ↦ by
      have hvars (i : Fin (rankTwo k)) :
          (∑ j : Fin (rankTwo k),
            MvPolynomial.C (phi (slRankTwoEntry (k := k) i j)) * MvPolynomial.X j :
            MvPolynomial (Fin (rankTwo k)) R).IsHomogeneous 1 := by
        apply MvPolynomial.IsHomogeneous.sum
        intro j _
        exact MvPolynomial.isHomogeneous_C_mul_X _ j
      exact (MvPolynomial.mem_homogeneousSubmodule d _).mpr (by
        have heval := hp.eval₂ MvPolynomial.C
          (fun i ↦ ∑ j : Fin (rankTwo k),
            MvPolynomial.C (phi (slRankTwoEntry (k := k) i j)) * MvPolynomial.X j)
          (fun r ↦ MvPolynomial.isHomogeneous_C _ r) hvars
        change (MvPolynomial.eval₂ MvPolynomial.C
          (fun i ↦ ∑ j : Fin (rankTwo k),
            MvPolynomial.C (phi (slRankTwoEntry (k := k) i j)) * MvPolynomial.X j) p
          ).IsHomogeneous d
        simpa only [one_mul] using heval)

@[simp] private theorem slProjectiveSubstitution_X
    {R : Type v} [CommRing R]
    (phi : coordinateRing (SLRankTwo (k := k)) →+* R)
    (i : Fin (rankTwo k)) :
    slProjectiveSubstitution (k := k) phi (MvPolynomial.X i) =
      ∑ j : Fin (rankTwo k),
        MvPolynomial.C (phi (slRankTwoEntry (k := k) i j)) * MvPolynomial.X j := by
  simp [slProjectiveSubstitution]

private theorem slProjectiveSubstitution_irrelevant
    {R : Type v} [CommRing R]
    (phi : coordinateRing (SLRankTwo (k := k)) →+* R) :
    HomogeneousIdeal.irrelevant (projectiveGrading R (Fin (rankTwo k))) ≤
      (HomogeneousIdeal.irrelevant
        (projectiveGrading R (Fin (rankTwo k)))).map
          (slProjectiveSubstitution (k := k) phi) := by
  rw [← toIdeal_le_toIdeal_iff]
  refine (coordinate_irrelevant_le_span R (Fin (rankTwo k))).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  have hcomb :
      ∑ i : Fin (rankTwo k),
          MvPolynomial.C (phi (slRankTwoInverseEntry (k := k) j i)) *
            slProjectiveSubstitution (k := k) phi (MvPolynomial.X i) =
        MvPolynomial.X j := by
    simp_rw [slProjectiveSubstitution_X (k := k)]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← map_mul]
    simp_rw [← Finset.sum_mul]
    simp_rw [← map_sum]
    simp_rw [slRankTwoInverseEntry_mul_entry (k := k)]
    simp [apply_ite MvPolynomial.C, Finset.sum_ite_eq', mul_ite]
  rw [← hcomb]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _
    (Ideal.mem_map_of_mem (slProjectiveSubstitution (k := k) phi)
      (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
        (MvPolynomial.isHomogeneous_X _ i)))

private noncomputable abbrev PGL2Ring :=
  coordinateRing (pgl2Variety (k := k))

private noncomputable abbrev SLRankTwoRing :=
  coordinateRing (SLRankTwo (k := k))

public noncomputable instance pgl2ProjectionAlgebra :
    Algebra (coordinateRing (pgl2Variety (k := k)))
      (coordinateRing
        (slVariety k (Module.finrank k (Fin 2 -> k)))) :=
  (ofAffinePullback (pgl2Projection (k := k)).toVariety).toRingHom.toAlgebra

private noncomputable abbrev PGL2KernelPairRing :=
  SLRankTwoRing (k := k) ⊗[PGL2Ring (k := k)] SLRankTwoRing (k := k)

private noncomputable abbrev kernelPairLeft :
    SLRankTwoRing (k := k) →+* PGL2KernelPairRing (k := k) :=
  Algebra.TensorProduct.includeLeftRingHom

private noncomputable abbrev kernelPairRight :
    SLRankTwoRing (k := k) →+* PGL2KernelPairRing (k := k) :=
  Algebra.TensorProduct.includeRight.toRingHom

private theorem kernelPair_tensorEntry_eq
    (a b i j : Fin (rankTwo k)) :
    kernelPairLeft (k := k)
        (slRankTwoInverseEntry (k := k) i a * slRankTwoEntry (k := k) b j) =
      kernelPairRight (k := k)
        (slRankTwoInverseEntry (k := k) i a * slRankTwoEntry (k := k) b j) := by
  rw [← pgl2Projection_pullback_tensorEntryRank (k := k)]
  exact DFunLike.congr_fun
    Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap
      (pgl2TensorEntryRank (k := k) a b i j)

private noncomputable def rankTwoEquiv : Fin (rankTwo k) ≃ Fin 2 :=
  finCongr (finrankFinTwo (k := k))

private theorem slRankTwoInverseEntry_eq (i j : Fin (rankTwo k)) :
    slRankTwoInverseEntry (k := k) i j =
      if rankTwoEquiv (k := k) i = 0 ∧ rankTwoEquiv (k := k) j = 0 then
        slRankTwoEntry (k := k)
          ((rankTwoEquiv (k := k)).symm 1) ((rankTwoEquiv (k := k)).symm 1)
      else if rankTwoEquiv (k := k) i = 0 ∧ rankTwoEquiv (k := k) j = 1 then
        -slRankTwoEntry (k := k)
          ((rankTwoEquiv (k := k)).symm 0) ((rankTwoEquiv (k := k)).symm 1)
      else if rankTwoEquiv (k := k) i = 1 ∧ rankTwoEquiv (k := k) j = 0 then
        -slRankTwoEntry (k := k)
          ((rankTwoEquiv (k := k)).symm 1) ((rankTwoEquiv (k := k)).symm 0)
      else slRankTwoEntry (k := k)
          ((rankTwoEquiv (k := k)).symm 0) ((rankTwoEquiv (k := k)).symm 0) := by
  apply (coordinateRingAlgEquivPolynomialFunction (SLRankTwo (k := k))).injective
  apply Variety.PolynomialFunction.ext
  intro x
  change coordinatePointAlgHom (SLRankTwo (k := k)) x
      (slRankTwoInverseEntry (k := k) i j) = _
  rw [coordinatePointAlgHom_slRankTwoInverseEntry]
  let A := (slPointEquiv (rankTwo k) x).1
  obtain ⟨i₂, rfl⟩ := (rankTwoEquiv (k := k)).symm.surjective i
  obtain ⟨j₂, rfl⟩ := (rankTwoEquiv (k := k)).symm.surjective j
  fin_cases i₂ <;> fin_cases j₂
  · simp only [Equiv.apply_symm_apply, Fin.zero_eta, Fin.mk_one, Fin.mk.injEq,
      Fin.isValue, and_self,
      Nat.reduceEqDiff, if_true]
    change A.adjugate ((rankTwoEquiv (k := k)).symm 0)
        ((rankTwoEquiv (k := k)).symm 0) =
      coordinatePointAlgHom (SLRankTwo (k := k)) x
        (slRankTwoEntry (k := k) ((rankTwoEquiv (k := k)).symm 1)
          ((rankTwoEquiv (k := k)).symm 1))
    rw [coordinatePointAlgHom_slRankTwoEntry]
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k ↦ M 0 0)
      (Matrix.adjugate_reindex (rankTwoEquiv (k := k)) A)
    rw [Matrix.adjugate_fin_two] at h
    simpa [A, Matrix.reindex_apply] using h.symm
  · simp only [Equiv.apply_symm_apply, Fin.zero_eta, Fin.mk_one, Fin.mk.injEq,
      Fin.isValue, zero_ne_one,
      and_false, if_false, and_self, Nat.reduceEqDiff, if_true]
    simp only [true_and, one_ne_zero, if_false]
    change A.adjugate ((rankTwoEquiv (k := k)).symm 0)
        ((rankTwoEquiv (k := k)).symm 1) =
      coordinatePointAlgHom (SLRankTwo (k := k)) x
        (-slRankTwoEntry (k := k) ((rankTwoEquiv (k := k)).symm 0)
          ((rankTwoEquiv (k := k)).symm 1))
    rw [map_neg, coordinatePointAlgHom_slRankTwoEntry]
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k ↦ M 0 1)
      (Matrix.adjugate_reindex (rankTwoEquiv (k := k)) A)
    rw [Matrix.adjugate_fin_two] at h
    simpa [A, Matrix.reindex_apply] using h.symm
  · simp only [Equiv.apply_symm_apply, Fin.zero_eta, Fin.mk_one, Fin.mk.injEq,
      Fin.isValue, one_ne_zero,
      false_and, if_false, and_self, Nat.reduceEqDiff, if_true]
    change A.adjugate ((rankTwoEquiv (k := k)).symm 1)
        ((rankTwoEquiv (k := k)).symm 0) =
      coordinatePointAlgHom (SLRankTwo (k := k)) x
        (-slRankTwoEntry (k := k) ((rankTwoEquiv (k := k)).symm 1)
          ((rankTwoEquiv (k := k)).symm 0))
    rw [map_neg, coordinatePointAlgHom_slRankTwoEntry]
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k ↦ M 1 0)
      (Matrix.adjugate_reindex (rankTwoEquiv (k := k)) A)
    rw [Matrix.adjugate_fin_two] at h
    simpa [A, Matrix.reindex_apply] using h.symm
  · simp only [Equiv.apply_symm_apply, Fin.zero_eta, Fin.mk_one, Fin.mk.injEq,
      Fin.isValue, one_ne_zero,
      false_and, if_false, and_self, Nat.reduceEqDiff, if_true]
    simp only [true_and, false_and, and_false, one_ne_zero, zero_ne_one, if_false,
      if_true]
    change A.adjugate ((rankTwoEquiv (k := k)).symm 1)
        ((rankTwoEquiv (k := k)).symm 1) =
      coordinatePointAlgHom (SLRankTwo (k := k)) x
        (slRankTwoEntry (k := k) ((rankTwoEquiv (k := k)).symm 0)
          ((rankTwoEquiv (k := k)).symm 0))
    rw [coordinatePointAlgHom_slRankTwoEntry]
    have h := congrArg (fun M : Matrix (Fin 2) (Fin 2) k ↦ M 1 1)
      (Matrix.adjugate_reindex (rankTwoEquiv (k := k)) A)
    rw [Matrix.adjugate_fin_two] at h
    simpa [A, Matrix.reindex_apply] using h.symm

private theorem kernelPair_entry_mul_entry_eq
    (a b i j : Fin (rankTwo k)) :
    kernelPairLeft (k := k)
        (slRankTwoEntry (k := k) a b * slRankTwoEntry (k := k) i j) =
      kernelPairRight (k := k)
        (slRankTwoEntry (k := k) a b * slRankTwoEntry (k := k) i j) := by
  have neg_mul' (x y : SLRankTwoRing (k := k)) : (-x) * y = -(x * y) := by
    apply (coordinateRingAlgEquivPolynomialFunction (SLRankTwo (k := k))).injective
    apply Variety.PolynomialFunction.ext
    intro z
    change coordinatePointAlgHom (SLRankTwo (k := k)) z ((-x) * y) =
      coordinatePointAlgHom (SLRankTwo (k := k)) z (-(x * y))
    rw [map_mul, map_neg, map_neg, map_mul, neg_mul]
  let e := rankTwoEquiv (k := k)
  obtain ⟨a₂, rfl⟩ := e.symm.surjective a
  obtain ⟨b₂, rfl⟩ := e.symm.surjective b
  fin_cases a₂ <;> fin_cases b₂
  · simpa [slRankTwoInverseEntry_eq, e] using
      kernelPair_tensorEntry_eq (k := k) (e.symm 1) i (e.symm 1) j
  · have h := kernelPair_tensorEntry_eq (k := k) (e.symm 1) i (e.symm 0) j
    rw [slRankTwoInverseEntry_eq, show e (e.symm 0) = 0 by simp,
      show e (e.symm 1) = 1 by simp] at h
    simp only [Fin.isValue, zero_ne_one, one_ne_zero, and_false, false_and,
      if_false, and_self, if_true] at h
    change kernelPairLeft (k := k)
        ((-slRankTwoEntry (k := k) (e.symm 0) (e.symm 1)) *
          slRankTwoEntry (k := k) i j) =
      kernelPairRight (k := k)
        ((-slRankTwoEntry (k := k) (e.symm 0) (e.symm 1)) *
          slRankTwoEntry (k := k) i j) at h
    have hL : kernelPairLeft (k := k)
        ((-slRankTwoEntry (k := k) (e.symm 0) (e.symm 1)) *
          slRankTwoEntry (k := k) i j) =
      -(kernelPairLeft (k := k)
        (slRankTwoEntry (k := k) (e.symm 0) (e.symm 1) *
          slRankTwoEntry (k := k) i j)) := by
      calc
        _ = kernelPairLeft (k := k)
            (-(slRankTwoEntry (k := k) (e.symm 0) (e.symm 1) *
              slRankTwoEntry (k := k) i j)) :=
          congrArg (kernelPairLeft (k := k)) (neg_mul' _ _)
        _ = _ := map_neg (kernelPairLeft (k := k)) _
    have hR : kernelPairRight (k := k)
        ((-slRankTwoEntry (k := k) (e.symm 0) (e.symm 1)) *
          slRankTwoEntry (k := k) i j) =
      -(kernelPairRight (k := k)
        (slRankTwoEntry (k := k) (e.symm 0) (e.symm 1) *
          slRankTwoEntry (k := k) i j)) := by
      calc
        _ = kernelPairRight (k := k)
            (-(slRankTwoEntry (k := k) (e.symm 0) (e.symm 1) *
              slRankTwoEntry (k := k) i j)) :=
          congrArg (kernelPairRight (k := k)) (neg_mul' _ _)
        _ = _ := map_neg (kernelPairRight (k := k)) _
    rw [hL, hR] at h
    apply neg_injective
    simpa [e] using h
  · have h := kernelPair_tensorEntry_eq (k := k) (e.symm 0) i (e.symm 1) j
    rw [slRankTwoInverseEntry_eq, show e (e.symm 1) = 1 by simp,
      show e (e.symm 0) = 0 by simp] at h
    simp only [Fin.isValue, one_ne_zero, false_and, if_false, and_self,
      if_true] at h
    change kernelPairLeft (k := k)
        ((-slRankTwoEntry (k := k) (e.symm 1) (e.symm 0)) *
          slRankTwoEntry (k := k) i j) =
      kernelPairRight (k := k)
        ((-slRankTwoEntry (k := k) (e.symm 1) (e.symm 0)) *
          slRankTwoEntry (k := k) i j) at h
    have hL : kernelPairLeft (k := k)
        ((-slRankTwoEntry (k := k) (e.symm 1) (e.symm 0)) *
          slRankTwoEntry (k := k) i j) =
      -(kernelPairLeft (k := k)
        (slRankTwoEntry (k := k) (e.symm 1) (e.symm 0) *
          slRankTwoEntry (k := k) i j)) := by
      calc
        _ = kernelPairLeft (k := k)
            (-(slRankTwoEntry (k := k) (e.symm 1) (e.symm 0) *
              slRankTwoEntry (k := k) i j)) :=
          congrArg (kernelPairLeft (k := k)) (neg_mul' _ _)
        _ = _ := map_neg (kernelPairLeft (k := k)) _
    have hR : kernelPairRight (k := k)
        ((-slRankTwoEntry (k := k) (e.symm 1) (e.symm 0)) *
          slRankTwoEntry (k := k) i j) =
      -(kernelPairRight (k := k)
        (slRankTwoEntry (k := k) (e.symm 1) (e.symm 0) *
          slRankTwoEntry (k := k) i j)) := by
      calc
        _ = kernelPairRight (k := k)
            (-(slRankTwoEntry (k := k) (e.symm 1) (e.symm 0) *
              slRankTwoEntry (k := k) i j)) :=
          congrArg (kernelPairRight (k := k)) (neg_mul' _ _)
        _ = _ := map_neg (kernelPairRight (k := k)) _
    rw [hL, hR] at h
    apply neg_injective
    simpa [e] using h
  · simpa [slRankTwoInverseEntry_eq, e] using
      kernelPair_tensorEntry_eq (k := k) (e.symm 0) i (e.symm 0) j

@[simp] private theorem slProjectiveSubstitution_C
    {R : Type v} [CommRing R]
    (phi : coordinateRing (SLRankTwo (k := k)) →+* R) (r : R) :
    slProjectiveSubstitution (k := k) phi (MvPolynomial.C r) =
      MvPolynomial.C r := by
  simp [slProjectiveSubstitution]

private theorem kernelPair_substitution_X_mul_X_eq
    (a b : Fin (rankTwo k)) :
    slProjectiveSubstitution (k := k) (R := PGL2KernelPairRing (k := k))
        (kernelPairLeft (k := k))
        (MvPolynomial.X a * MvPolynomial.X b) =
      slProjectiveSubstitution (k := k) (R := PGL2KernelPairRing (k := k))
        (kernelPairRight (k := k))
        (MvPolynomial.X a * MvPolynomial.X b) := by
  rw [map_mul, map_mul]
  simp_rw [slProjectiveSubstitution_X]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  have hcoeff := kernelPair_entry_mul_entry_eq (k := k) a i b j
  calc
    (MvPolynomial.C (kernelPairLeft (k := k) (slRankTwoEntry (k := k) a i)) *
          MvPolynomial.X i) *
        (MvPolynomial.C (kernelPairLeft (k := k) (slRankTwoEntry (k := k) b j)) *
          MvPolynomial.X j) =
      (MvPolynomial.C (kernelPairLeft (k := k) (slRankTwoEntry (k := k) a i)) *
        MvPolynomial.C (kernelPairLeft (k := k) (slRankTwoEntry (k := k) b j))) *
          (MvPolynomial.X i * MvPolynomial.X j) := mul_mul_mul_comm _ _ _ _
    _ = (MvPolynomial.C (kernelPairRight (k := k) (slRankTwoEntry (k := k) a i)) *
        MvPolynomial.C (kernelPairRight (k := k) (slRankTwoEntry (k := k) b j))) *
          (MvPolynomial.X i * MvPolynomial.X j) := by
      congr 1
      simpa only [map_mul, MvPolynomial.C_mul] using congrArg MvPolynomial.C hcoeff
    _ = (MvPolynomial.C (kernelPairRight (k := k) (slRankTwoEntry (k := k) a i)) *
          MvPolynomial.X i) *
        (MvPolynomial.C (kernelPairRight (k := k) (slRankTwoEntry (k := k) b j)) *
          MvPolynomial.X j) := (mul_mul_mul_comm _ _ _ _).symm

set_option maxHeartbeats 2000000 in
private theorem kernelPair_substitution_degree_two_eq
    (p : MvPolynomial (Fin (rankTwo k)) (PGL2KernelPairRing (k := k)))
    (hp : p ∈ projectiveGrading (PGL2KernelPairRing (k := k))
      (Fin (rankTwo k)) 2) :
    slProjectiveSubstitution (k := k) (R := PGL2KernelPairRing (k := k))
        (kernelPairLeft (k := k)) p =
      slProjectiveSubstitution (k := k) (R := PGL2KernelPairRing (k := k))
        (kernelPairRight (k := k)) p := by
  let f := slProjectiveSubstitution (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairLeft (k := k))
  let g := slProjectiveSubstitution (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairRight (k := k))
  change f p = g p
  have fC (r : PGL2KernelPairRing (k := k)) :
      f (MvPolynomial.C r) = MvPolynomial.C r := by
    simpa only [f] using
      (slProjectiveSubstitution_C (k := k) (kernelPairLeft (k := k)) r)
  have gC (r : PGL2KernelPairRing (k := k)) :
      g (MvPolynomial.C r) = MvPolynomial.C r := by
    simpa only [g] using
      (slProjectiveSubstitution_C (k := k) (kernelPairRight (k := k)) r)
  let H₁ := MvPolynomial.homogeneousSubmodule
    (Fin (rankTwo k)) (PGL2KernelPairRing (k := k)) 1
  have hp' : p ∈ H₁ * H₁ := by
    change p ∈ MvPolynomial.homogeneousSubmodule
      (Fin (rankTwo k)) (PGL2KernelPairRing (k := k)) 2 at hp
    have hpow : H₁ ^ 2 = MvPolynomial.homogeneousSubmodule
        (Fin (rankTwo k)) (PGL2KernelPairRing (k := k)) 2 := by
      simpa only [H₁] using
        MvPolynomial.homogeneousSubmodule_one_pow
          (PGL2KernelPairRing (k := k)) 2
    rw [← hpow] at hp
    simpa only [pow_two] using hp
  refine Submodule.mul_induction_on hp' ?_ ?_
  · intro x hx y hy
    change x ∈ MvPolynomial.homogeneousSubmodule
      (Fin (rankTwo k)) (PGL2KernelPairRing (k := k)) 1 at hx
    change y ∈ MvPolynomial.homogeneousSubmodule
      (Fin (rankTwo k)) (PGL2KernelPairRing (k := k)) 1 at hy
    rw [MvPolynomial.homogeneousSubmodule_one_eq_span_X] at hx hy
    induction hx, hy using Submodule.span_induction₂ with
    | mem_mem x y hx hy =>
        obtain ⟨i, rfl⟩ := hx
        obtain ⟨j, rfl⟩ := hy
        exact kernelPair_substitution_X_mul_X_eq (k := k) i j
    | zero_left => simp
    | zero_right => simp
    | add_left x y z _ _ _ hx hy =>
        simpa only [add_mul, map_add] using congrArg₂ (· + ·) hx hy
    | add_right x y z _ _ _ hx hy =>
        simpa only [mul_add, map_add] using congrArg₂ (· + ·) hx hy
    | smul_left r x y _ _ hxy =>
        simp only [MvPolynomial.smul_eq_C_mul, map_mul, fC, gC]
        have hxy' : f x * f y = g x * g y := by
          simpa only [map_mul] using hxy
        calc
          MvPolynomial.C r * f x * f y =
              MvPolynomial.C r * (f x * f y) := by ac_rfl
          _ = MvPolynomial.C r * (g x * g y) := congrArg _ hxy'
          _ = _ := by ac_rfl
    | smul_right r x y _ _ hxy =>
        simp only [MvPolynomial.smul_eq_C_mul, map_mul, fC, gC]
        have hxy' : f x * f y = g x * g y := by
          simpa only [map_mul] using hxy
        calc
          f x * (MvPolynomial.C r * f y) =
              MvPolynomial.C r * (f x * f y) := by ac_rfl
          _ = MvPolynomial.C r * (g x * g y) := congrArg _ hxy'
          _ = _ := by ac_rfl
  · intro x y hx hy
    simpa only [map_add] using congrArg₂ (· + ·) hx hy

set_option maxHeartbeats 2000000 in
private theorem kernelPair_substitution_even_eq
    (d : ℕ)
    (p : MvPolynomial (Fin (rankTwo k)) (PGL2KernelPairRing (k := k)))
    (hp : p ∈ projectiveGrading (PGL2KernelPairRing (k := k))
      (Fin (rankTwo k)) (2 * d)) :
    slProjectiveSubstitution (k := k) (R := PGL2KernelPairRing (k := k))
        (kernelPairLeft (k := k)) p =
      slProjectiveSubstitution (k := k) (R := PGL2KernelPairRing (k := k))
        (kernelPairRight (k := k)) p := by
  let f := slProjectiveSubstitution (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairLeft (k := k))
  let g := slProjectiveSubstitution (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairRight (k := k))
  let H₂ := MvPolynomial.homogeneousSubmodule
    (Fin (rankTwo k)) (PGL2KernelPairRing (k := k)) 2
  change f p = g p
  have hpower : ∀ (n : ℕ)
      (q : MvPolynomial (Fin (rankTwo k)) (PGL2KernelPairRing (k := k))),
      q ∈ H₂ ^ n → f q = g q := by
    intro n
    induction n with
    | zero =>
        intro q hq
        rw [Submodule.pow_zero] at hq
        obtain ⟨r, hr⟩ := Submodule.mem_one.mp hq
        rw [← hr]
        change f (MvPolynomial.C r) = g (MvPolynomial.C r)
        simpa only [f, g] using
          (slProjectiveSubstitution_C (k := k)
            (kernelPairLeft (k := k)) r).trans
              (slProjectiveSubstitution_C (k := k)
                (kernelPairRight (k := k)) r).symm
    | succ n ih =>
        intro q hq
        rw [pow_succ] at hq
        refine Submodule.mul_induction_on hq ?_ ?_
        · intro x hx y hy
          rw [map_mul, map_mul, ih x hx]
          exact congrArg (fun z ↦ g x * z)
            (kernelPair_substitution_degree_two_eq (k := k) y hy)
        · intro x y hx hy
          simpa only [map_add] using congrArg₂ (· + ·) hx hy
  apply hpower d p
  change p ∈ MvPolynomial.homogeneousSubmodule
    (Fin (rankTwo k)) (PGL2KernelPairRing (k := k)) (2 * d) at hp
  have h₂ : (MvPolynomial.homogeneousSubmodule
      (Fin (rankTwo k)) (PGL2KernelPairRing (k := k)) 1) ^ 2 = H₂ := by
    simpa only [H₂] using MvPolynomial.homogeneousSubmodule_one_pow
      (PGL2KernelPairRing (k := k)) 2
  have hpow : H₂ ^ d = MvPolynomial.homogeneousSubmodule
      (Fin (rankTwo k)) (PGL2KernelPairRing (k := k)) (2 * d) := by
    rw [← h₂, ← pow_mul]
    exact MvPolynomial.homogeneousSubmodule_one_pow
      (PGL2KernelPairRing (k := k)) (2 * d)
  rwa [hpow]

public noncomputable abbrev sl2ProjectiveKernelPairRing :=
  coordinateRing (slVariety k (Module.finrank k (Fin 2 -> k))) ⊗[
      coordinateRing (pgl2Variety (k := k))]
    coordinateRing (slVariety k (Module.finrank k (Fin 2 -> k)))

/-- The genuine projective-linear action restricted from `GL₂` to `SL₂`. -/
public noncomputable abbrev sl2ProjectiveMorphicAction :=
  projectiveLinearMorphicActionPullback (k := k) (Fin 2 -> k)
    (specialLinearToGeneralLinearMorphism (k := k)
      (Module.finrank k (Fin 2 -> k)))

/-- The restricted action with the coordinate projective target made
definitionally explicit. -/
public noncomputable abbrev sl2ProjectiveCoordinateMorphicAction :
    MorphicAction
      (slVariety k (Module.finrank k (Fin 2 -> k)))
      (projectiveSpaceByCoordinates k
        (Fin (Module.finrank k (Fin 2 -> k)))) :=
  sl2ProjectiveMorphicAction (k := k)

/-- In coordinate projective space, the restricted regular `SL2` action is
Mathlib's action through the canonical map from `SL` to `PGL`. -/
public theorem sl2ProjectiveMorphicAction_projectiveSpaceByCoordinatesPointEquiv
    (s : Variety.Point
      (slVariety k (Module.finrank k (Fin 2 -> k))))
    (x : Point (projectiveSpaceByCoordinates k
      (Fin (Module.finrank k (Fin 2 -> k))))) :
    projectiveSpaceByCoordinatesPointEquiv
        ((sl2ProjectiveCoordinateMorphicAction (k := k)).toMulAction.smul s x) =
      Matrix.SpecialLinearGroup.toPGL
          (slPointEquiv (Module.finrank k (Fin 2 -> k)) s) •
        projectiveSpaceByCoordinatesPointEquiv x := by
  unfold sl2ProjectiveCoordinateMorphicAction sl2ProjectiveMorphicAction
    projectiveLinearMorphicActionPullback
  change projectiveSpaceByCoordinatesPointEquiv
      ((projectiveLinearMorphicActionByCoordinates
        (k := k) (Module.finrank k (Fin 2 -> k))).toMulAction.smul
          ((specialLinearToGeneralLinearMorphism
            (Module.finrank k (Fin 2 -> k))).onPoints s) x) = _
  letI := glCoordinatePointMulAction (k := k)
    (Module.finrank k (Fin 2 -> k))
  induction hq : projectiveSpaceByCoordinatesPointEquiv x using Projectivization.ind with
  | h v hv =>
    have hx : x = projectivePointOfVector v hv := by
      apply projectiveSpaceByCoordinatesPointEquiv.injective
      rw [hq, projectiveSpaceByCoordinatesPointEquiv_projectivePointOfVector]
    subst x
    change projectiveSpaceByCoordinatesPointEquiv
        (letI : MulAction
            (Variety.Point (glVariety (Module.finrank k (Fin 2 -> k)) : Variety k))
            (Point (projectiveSpaceByCoordinates k
              (Fin (Module.finrank k (Fin 2 -> k))))) :=
          glCoordinatePointMulAction (k := k)
            (Module.finrank k (Fin 2 -> k))
        (specialLinearToGeneralLinearMorphism
            (Module.finrank k (Fin 2 -> k))).onPoints s •
          projectivePointOfVector v hv) = _
    rw [glCoordinatePointMulAction_projectivePointOfVector,
      projectiveSpaceByCoordinatesPointEquiv_projectivePointOfVector]
    change Projectivization.mk k _ _ =
      Matrix.ProjGenLinGroup.mk
          (Matrix.SpecialLinearGroup.toGL
            (slPointEquiv (Module.finrank k (Fin 2 -> k)) s)) •
        Projectivization.mk k v hv
    rw [Projectivization.PGL.mk_smul_mk]
    rfl

private noncomputable def kernelPairProjectiveFamilyMap
    (f : projectiveGrading (sl2ProjectiveKernelPairRing (k := k)) (Fin (rankTwo k)) →+*ᵍ
      projectiveGrading (sl2ProjectiveKernelPairRing (k := k)) (Fin (rankTwo k)))
    (hf : HomogeneousIdeal.irrelevant
        (projectiveGrading (sl2ProjectiveKernelPairRing (k := k)) (Fin (rankTwo k))) ≤
      (HomogeneousIdeal.irrelevant
        (projectiveGrading (sl2ProjectiveKernelPairRing (k := k)) (Fin (rankTwo k)))).map f) :
    pullback (projectiveSpaceByCoordinates k (Fin (rankTwo k))).structureMap
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (sl2ProjectiveKernelPairRing (k := k))))) ⟶
      (projectiveSpaceByCoordinates k (Fin (rankTwo k))).toScheme :=
  (polynomialProjBaseChangeIso k (sl2ProjectiveKernelPairRing (k := k))
      (Fin (rankTwo k))).inv ≫
    Proj.map f hf ≫
      polynomialProjMap (k := k) (R := sl2ProjectiveKernelPairRing (k := k))
        (Fin (rankTwo k))

private noncomputable def kernelPairProjectiveFamilyPullbackLift :
    pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
        (projectiveSpaceByCoordinates k (Fin (rankTwo k))).structureMap ⟶
      pullback (projectiveSpaceByCoordinates k (Fin (rankTwo k))).structureMap
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (sl2ProjectiveKernelPairRing (k := k))))) :=
  pullback.lift
    (pullback.snd
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
      (projectiveSpaceByCoordinates k (Fin (rankTwo k))).structureMap)
    (pullback.fst
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
      (projectiveSpaceByCoordinates k (Fin (rankTwo k))).structureMap)
    pullback.condition.symm

/-- The two base-changed `SL₂` projective-action families on the affine
scheme-theoretic kernel pair of `pgl2Projection`, together with their equality. -/
public structure SL2ProjectiveKernelPairFamily where
  left :
    pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
        (projectiveSpaceByCoordinates k
          (Fin (Module.finrank k (Fin 2 -> k)))).structureMap ⟶
      (projectiveSpaceByCoordinates k
        (Fin (Module.finrank k (Fin 2 -> k)))).toScheme
  right :
    pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
        (projectiveSpaceByCoordinates k
          (Fin (Module.finrank k (Fin 2 -> k)))).structureMap ⟶
      (projectiveSpaceByCoordinates k
        (Fin (Module.finrank k (Fin 2 -> k)))).toScheme
  equal : left = right

set_option maxHeartbeats 2000000 in
/-- The scheme-level kernel-pair certificate for the restriction of the
genuine general-linear projective action to `SL₂`. -/
public noncomputable def sl2ProjectiveKernelPairFamily :
    SL2ProjectiveKernelPairFamily (k := k) := by
  let f := slProjectiveSubstitution (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairLeft (k := k))
  let g := slProjectiveSubstitution (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairRight (k := k))
  let hf := slProjectiveSubstitution_irrelevant (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairLeft (k := k))
  let hg := slProjectiveSubstitution_irrelevant (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairRight (k := k))
  have hproj : Proj.map f hf = Proj.map g hg := by
    apply projMap_eq_of_even
    intro d p hp
    exact kernelPair_substitution_even_eq (k := k) d p hp
  exact {
    left := kernelPairProjectiveFamilyPullbackLift (k := k) ≫
      kernelPairProjectiveFamilyMap (k := k) f hf
    right := kernelPairProjectiveFamilyPullbackLift (k := k) ≫
      kernelPairProjectiveFamilyMap (k := k) g hg
    equal := by
      unfold kernelPairProjectiveFamilyMap
      rw [hproj] }

/-- The first coordinate family on the `SL₂` kernel pair. -/
public noncomputable abbrev sl2ProjectiveKernelPairLeftFamilyMap :=
  (sl2ProjectiveKernelPairFamily (k := k)).left

/-- The second coordinate family on the `SL₂` kernel pair. -/
public noncomputable abbrev sl2ProjectiveKernelPairRightFamilyMap :=
  (sl2ProjectiveKernelPairFamily (k := k)).right

/-- The two scheme morphisms obtained by pulling the `SL₂` projective action
back to the kernel pair of `pgl2Projection`, after product with projective
space, are equal. -/
public theorem sl2ProjectiveKernelPair_familyMap_eq :
    sl2ProjectiveKernelPairLeftFamilyMap (k := k) =
      sl2ProjectiveKernelPairRightFamilyMap (k := k) :=
  (sl2ProjectiveKernelPairFamily (k := k)).equal

private noncomputable abbrev K := sl2ProjectiveKernelPairRing (k := k)

private noncomputable abbrev S :=
  coordinateRing (SLRankTwo (k := k))

private noncomputable abbrev G :=
  coordinateRing (glVariety (rankTwo k) : Variety k)

private noncomputable abbrev P :=
  projectiveSpaceByCoordinates k (Fin (rankTwo k))

private noncomputable abbrev D :=
  pullback (Spec.map (CommRingCat.ofHom (algebraMap k (K (k := k)))))
    (P (k := k)).structureMap

private noncomputable abbrev toKernelPairRingHom
    {A : Type u} [CommRing A] (phi : A →+* K (k := k)) :=
  @CommRingCat.ofHom _ _ (inferInstance)
    Algebra.TensorProduct.instCommRing phi

private noncomputable abbrev kernelPairLeftToSL :
    Spec (CommRingCat.of (K (k := k))) ⟶
      (ofAffine (SLRankTwo (k := k))).toScheme :=
  Spec.map (toKernelPairRingHom (k := k) (kernelPairLeft (k := k)))

private noncomputable abbrev kernelPairRightToSL :
    Spec (CommRingCat.of (K (k := k))) ⟶
      (ofAffine (SLRankTwo (k := k))).toScheme :=
  Spec.map (toKernelPairRingHom (k := k) (kernelPairRight (k := k)))

private theorem kernelPairLeftToSL_structure :
    kernelPairLeftToSL (k := k) ≫
        (ofAffine (SLRankTwo (k := k))).structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap k (K (k := k)))) := by
  unfold kernelPairLeftToSL ofAffine K sl2ProjectiveKernelPairRing
  rw [← Spec.map_comp]
  congr 1

private theorem kernelPairRightToSL_structure :
    kernelPairRightToSL (k := k) ≫
        (ofAffine (SLRankTwo (k := k))).structureMap =
      Spec.map (CommRingCat.ofHom (algebraMap k (K (k := k)))) := by
  unfold kernelPairRightToSL ofAffine K sl2ProjectiveKernelPairRing
  rw [← Spec.map_comp]
  congr 1
  ext r
  simp [kernelPairRight]

/-- The first kernel-pair projection, together with the unchanged projective
coordinate, as a morphism to `SL₂ × P¹`. -/
public noncomputable def sl2ProjectiveKernelPairLeftSource :
    pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
        (projectiveSpaceByCoordinates k
          (Fin (Module.finrank k (Fin 2 -> k)))).structureMap ⟶
      (prod
        (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
        (projectiveSpaceByCoordinates k
          (Fin (Module.finrank k (Fin 2 -> k))))).toScheme :=
  pullback.lift
    (pullback.fst _ _ ≫ kernelPairLeftToSL (k := k))
    (pullback.snd _ _) (by
      simp only [Category.assoc, kernelPairLeftToSL_structure]
      exact pullback.condition)

/-- The second kernel-pair projection, together with the unchanged projective
coordinate, as a morphism to `SL₂ × P¹`. -/
public noncomputable def sl2ProjectiveKernelPairRightSource :
    pullback
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (sl2ProjectiveKernelPairRing (k := k)))))
        (projectiveSpaceByCoordinates k
          (Fin (Module.finrank k (Fin 2 -> k)))).structureMap ⟶
      (prod
        (ofAffine (slVariety k (Module.finrank k (Fin 2 -> k))))
        (projectiveSpaceByCoordinates k
          (Fin (Module.finrank k (Fin 2 -> k))))).toScheme :=
  pullback.lift
    (pullback.fst _ _ ≫ kernelPairRightToSL (k := k))
    (pullback.snd _ _) (by
      simp only [Category.assoc, kernelPairRightToSL_structure]
      exact pullback.condition)

private theorem sl2ProjectiveKernelPairLeftSource_fst :
    sl2ProjectiveKernelPairLeftSource (k := k) ≫
        (fst (ofAffine (SLRankTwo (k := k))) (P (k := k))).hom =
      pullback.fst _ _ ≫ kernelPairLeftToSL (k := k) := by
  unfold sl2ProjectiveKernelPairLeftSource fst prod
  exact pullback.lift_fst _ _ _

private theorem sl2ProjectiveKernelPairLeftSource_snd :
    sl2ProjectiveKernelPairLeftSource (k := k) ≫
        (snd (ofAffine (SLRankTwo (k := k))) (P (k := k))).hom =
      pullback.snd _ _ := by
  unfold sl2ProjectiveKernelPairLeftSource snd prod
  exact pullback.lift_snd _ _ _

private theorem sl2ProjectiveKernelPairRightSource_fst :
    sl2ProjectiveKernelPairRightSource (k := k) ≫
        (fst (ofAffine (SLRankTwo (k := k))) (P (k := k))).hom =
      pullback.fst _ _ ≫ kernelPairRightToSL (k := k) := by
  unfold sl2ProjectiveKernelPairRightSource fst prod
  exact pullback.lift_fst _ _ _

private theorem sl2ProjectiveKernelPairRightSource_snd :
    sl2ProjectiveKernelPairRightSource (k := k) ≫
        (snd (ofAffine (SLRankTwo (k := k))) (P (k := k))).hom =
      pullback.snd _ _ := by
  unfold sl2ProjectiveKernelPairRightSource snd prod
  exact pullback.lift_snd _ _ _

private noncomputable abbrev glPullback
    (phi : S (k := k) →+* K (k := k)) : G (k := k) →+* K (k := k) :=
  phi.comp (ofAffinePullback
    (slRankTwoToGL (k := k)).toVariety).toRingHom

private noncomputable abbrev glPullbackHom
    (phi : S (k := k) →+* K (k := k)) :=
  CommRingCat.ofHom
      (ofAffinePullback (slRankTwoToGL (k := k)).toVariety).toRingHom ≫
    toKernelPairRingHom (k := k) phi

private theorem glPullbackHom_eq
    (phi : S (k := k) →+* K (k := k)) :
    glPullbackHom (k := k) phi =
      toKernelPairRingHom (k := k) (glPullback (k := k) phi) := by
  rfl

private theorem left_glPullback_base :
    polynomialProjMapOfRingHom (Fin (rankTwo k))
        (glPullback (k := k) (kernelPairLeft (k := k))) ≫
      polynomialProjMap (k := k) (R := G (k := k)) (Fin (rankTwo k)) =
    polynomialProjMap (k := k) (R := K (k := k)) (Fin (rankTwo k)) := by
  rw [polynomialProjMap_eq_mapOfRingHom]
  rw [← polynomialProjMapOfRingHom_comp]
  rw [polynomialProjMap_eq_mapOfRingHom]
  congr 1
  ext r
  change kernelPairLeft (k := k)
    (ofAffinePullback (slRankTwoToGL (k := k)).toVariety
      (algebraMap k (G (k := k)) r)) = _
  rw [ofAffinePullback_algebraMap]
  rfl

private theorem right_glPullback_base :
    polynomialProjMapOfRingHom (Fin (rankTwo k))
        (glPullback (k := k) (kernelPairRight (k := k))) ≫
      polynomialProjMap (k := k) (R := G (k := k)) (Fin (rankTwo k)) =
    polynomialProjMap (k := k) (R := K (k := k)) (Fin (rankTwo k)) := by
  rw [polynomialProjMap_eq_mapOfRingHom]
  rw [← polynomialProjMapOfRingHom_comp]
  rw [polynomialProjMap_eq_mapOfRingHom]
  congr 1
  ext r
  change kernelPairRight (k := k)
    (ofAffinePullback (slRankTwoToGL (k := k)).toVariety
      (algebraMap k (G (k := k)) r)) = _
  rw [ofAffinePullback_algebraMap]
  simp [kernelPairRight, K, sl2ProjectiveKernelPairRing]

private theorem slProjectiveSubstitution_natural
    (phi : S (k := k) →+* K (k := k)) :
    (polynomialCoefficientMap (B := K (k := k)) (Fin (rankTwo k))
      (glPullback (k := k) phi)).comp
        (glProjectiveSubstitution (k := k) (rankTwo k)) =
      (slProjectiveSubstitution (k := k) phi).comp
        (polynomialCoefficientMap (B := K (k := k)) (Fin (rankTwo k))
          (glPullback (k := k) phi)) := by
  apply GradedRingHom.ext
  intro p
  have h :
      ((polynomialCoefficientMap (B := K (k := k)) (Fin (rankTwo k))
          (glPullback (k := k) phi)).comp
        (glProjectiveSubstitution (k := k) (rankTwo k))).toRingHom =
      ((slProjectiveSubstitution (k := k) phi).comp
        (polynomialCoefficientMap (B := K (k := k)) (Fin (rankTwo k))
          (glPullback (k := k) phi))).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [slProjectiveSubstitution_C, glProjectiveSubstitution]
    · intro i
      simp only [GradedRingHom.coe_toRingHom, GradedRingHom.coe_comp,
        Function.comp_apply, glProjectiveSubstitution_X,
        slProjectiveSubstitution_X, map_sum, map_mul,
        polynomialCoefficientMap_C, polynomialCoefficientMap_X]
      rfl
  exact DFunLike.congr_fun h p

private noncomputable def coefficientBaseChange
    (psi : G (k := k) →+* K (k := k)) :
    D (k := k) ⟶
      pullback (P (k := k)).structureMap
        (Spec.map (CommRingCat.ofHom (algebraMap k (G (k := k))))) :=
  kernelPairProjectiveFamilyPullbackLift (k := k) ≫
    (polynomialProjBaseChangeIso k (K (k := k))
      (Fin (rankTwo k))).inv ≫
    polynomialProjMapOfRingHom (Fin (rankTwo k)) psi ≫
    (polynomialProjBaseChangeIso k (G (k := k))
      (Fin (rankTwo k))).hom

private theorem coefficientBaseChange_fst
    (psi : G (k := k) →+* K (k := k))
    (hbase : polynomialProjMapOfRingHom (Fin (rankTwo k)) psi ≫
        polynomialProjMap (k := k) (R := G (k := k)) (Fin (rankTwo k)) =
      polynomialProjMap (k := k) (R := K (k := k)) (Fin (rankTwo k))) :
    coefficientBaseChange (k := k) psi ≫ pullback.fst _ _ =
      pullback.snd _ _ := by
  unfold coefficientBaseChange
  simp only [Category.assoc]
  rw [polynomialProjBaseChangeIso_hom_fst]
  erw [hbase]
  rw [← polynomialProjBaseChangeIso_hom_fst]
  simp only [Iso.inv_hom_id_assoc]
  unfold kernelPairProjectiveFamilyPullbackLift
  exact pullback.lift_fst _ _ _

private theorem coefficientBaseChange_snd
    (psi : G (k := k) →+* K (k := k)) :
    coefficientBaseChange (k := k) psi ≫ pullback.snd _ _ =
      pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom psi) := by
  unfold coefficientBaseChange
  simp only [Category.assoc]
  rw [polynomialProjBaseChangeIso_hom_snd]
  rw [← Category.assoc, polynomialProjMapOfRingHom_structureMap]
  rw [← polynomialProjBaseChangeIso_hom_snd k (K (k := k))]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  unfold kernelPairProjectiveFamilyPullbackLift
  rw [← Category.assoc, pullback.lift_snd]

private theorem coefficientBaseChange_familyMap
    (psi : G (k := k) →+* K (k := k))
    (fK : projectiveGrading (K (k := k)) (Fin (rankTwo k)) →+*ᵍ
      projectiveGrading (K (k := k)) (Fin (rankTwo k)))
    (hfK : HomogeneousIdeal.irrelevant
        (projectiveGrading (K (k := k)) (Fin (rankTwo k))) ≤
      (HomogeneousIdeal.irrelevant
        (projectiveGrading (K (k := k)) (Fin (rankTwo k)))).map fK)
    (hbase : polynomialProjMapOfRingHom (Fin (rankTwo k)) psi ≫
        polynomialProjMap (k := k) (R := G (k := k)) (Fin (rankTwo k)) =
      polynomialProjMap (k := k) (R := K (k := k)) (Fin (rankTwo k)))
    (hnat : (polynomialCoefficientMap (B := K (k := k)) (Fin (rankTwo k))
        psi).comp (glProjectiveSubstitution (k := k) (rankTwo k)) =
      fK.comp (polynomialCoefficientMap (B := K (k := k))
        (Fin (rankTwo k)) psi)) :
    coefficientBaseChange (k := k) psi ≫
        polynomialProjFamilyMap k (G (k := k)) (Fin (rankTwo k))
          (glProjectiveSubstitution (k := k) (rankTwo k))
          (glProjectiveSubstitution_irrelevant (k := k) (rankTwo k)) =
      kernelPairProjectiveFamilyPullbackLift (k := k) ≫
        kernelPairProjectiveFamilyMap (k := k) fK hfK := by
  have hproj :
      polynomialProjMapOfRingHom (Fin (rankTwo k)) psi ≫
          Proj.map (glProjectiveSubstitution (k := k) (rankTwo k))
            (glProjectiveSubstitution_irrelevant (k := k) (rankTwo k)) =
        Proj.map fK hfK ≫
          polynomialProjMapOfRingHom (Fin (rankTwo k)) psi := by
    unfold polynomialProjMapOfRingHom
    rw [← Proj.map_comp, ← Proj.map_comp]
    congr 1
  have hfamily :
      polynomialProjMapOfRingHom (Fin (rankTwo k)) psi ≫
          Proj.map (glProjectiveSubstitution (k := k) (rankTwo k))
            (glProjectiveSubstitution_irrelevant (k := k) (rankTwo k)) ≫
          polynomialProjMap (k := k) (R := G (k := k)) (Fin (rankTwo k)) =
        Proj.map fK hfK ≫
          polynomialProjMap (k := k) (R := K (k := k)) (Fin (rankTwo k)) := by
    calc
      _ = (Proj.map fK hfK ≫ polynomialProjMapOfRingHom
            (Fin (rankTwo k)) psi) ≫
          polynomialProjMap (k := k) (R := G (k := k))
            (Fin (rankTwo k)) := by
        simpa only [Category.assoc] using congrArg
          (fun q ↦ q ≫ polynomialProjMap (k := k) (R := G (k := k))
            (Fin (rankTwo k))) hproj
      _ = Proj.map fK hfK ≫
          (polynomialProjMapOfRingHom (Fin (rankTwo k)) psi ≫
            polynomialProjMap (k := k) (R := G (k := k))
              (Fin (rankTwo k))) := Category.assoc _ _ _
      _ = _ := by rw [hbase]
  unfold coefficientBaseChange polynomialProjFamilyMap
  unfold kernelPairProjectiveFamilyMap
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  change kernelPairProjectiveFamilyPullbackLift (k := k) ≫
      (polynomialProjBaseChangeIso k (K (k := k)) (Fin (rankTwo k))).inv ≫
        (polynomialProjMapOfRingHom (Fin (rankTwo k)) psi ≫
          Proj.map (glProjectiveSubstitution (k := k) (rankTwo k))
            (glProjectiveSubstitution_irrelevant (k := k) (rankTwo k)) ≫
          polynomialProjMap (k := k) (R := G (k := k))
            (Fin (rankTwo k))) =
    kernelPairProjectiveFamilyPullbackLift (k := k) ≫
      (polynomialProjBaseChangeIso k (K (k := k)) (Fin (rankTwo k))).inv ≫
        (Proj.map fK hfK ≫
          polynomialProjMap (k := k) (R := K (k := k)) (Fin (rankTwo k)))
  simpa only [Category.assoc] using congrArg
    (fun q ↦ kernelPairProjectiveFamilyPullbackLift (k := k) ≫
      (polynomialProjBaseChangeIso k (K (k := k))
        (Fin (rankTwo k))).inv ≫ q) hfamily

private noncomputable def actionPullbackPair :
    Morphism (prod (ofAffine (SLRankTwo (k := k))) (P (k := k)))
      (prod (ofAffine (glVariety (rankTwo k) : Variety k)) (P (k := k))) :=
  Morphism.pair
    (Morphism.comp (fst (ofAffine (SLRankTwo (k := k))) (P (k := k)))
      (ofAffine_morphism (slRankTwoToGL (k := k)).toVariety))
    (snd (ofAffine (SLRankTwo (k := k))) (P (k := k)))

set_option maxHeartbeats 2000000 in
private theorem source_actionPullback
    (phi : S (k := k) →+* K (k := k))
    (source : D (k := k) ⟶
      (prod (ofAffine (SLRankTwo (k := k))) (P (k := k))).toScheme)
    (hfst : source ≫
        (fst (ofAffine (SLRankTwo (k := k))) (P (k := k))).hom =
      pullback.fst _ _ ≫
        Spec.map (toKernelPairRingHom (k := k) phi))
    (hsnd : source ≫
        (snd (ofAffine (SLRankTwo (k := k))) (P (k := k))).hom =
      pullback.snd _ _)
    (hbase : polynomialProjMapOfRingHom (Fin (rankTwo k))
          (glPullback (k := k) phi) ≫
        polynomialProjMap (k := k) (R := G (k := k)) (Fin (rankTwo k)) =
      polynomialProjMap (k := k) (R := K (k := k)) (Fin (rankTwo k))) :
    source ≫ (actionPullbackPair (k := k)).hom ≫
        glProjectiveFamilyPullbackLift (k := k) (rankTwo k) =
      coefficientBaseChange (k := k) (glPullback (k := k) phi) := by
  have hpairFst :
      (actionPullbackPair (k := k)).hom ≫
          (fst (ofAffine (glVariety (rankTwo k) : Variety k))
            (P (k := k))).hom =
        (fst (ofAffine (SLRankTwo (k := k))) (P (k := k))).hom ≫
          Spec.map (CommRingCat.ofHom
            (ofAffinePullback
              (slRankTwoToGL (k := k)).toVariety).toRingHom) := by
    unfold actionPullbackPair Morphism.pair Morphism.comp
    unfold ofAffine_morphism fst prod
    exact pullback.lift_fst _ _ _
  have hpairSnd :
      (actionPullbackPair (k := k)).hom ≫
          (snd (ofAffine (glVariety (rankTwo k) : Variety k))
            (P (k := k))).hom =
        (snd (ofAffine (SLRankTwo (k := k))) (P (k := k))).hom := by
    unfold actionPullbackPair Morphism.pair snd prod
    exact pullback.lift_snd _ _ _
  have hglFst :
      glProjectiveFamilyPullbackLift (k := k) (rankTwo k) ≫
          pullback.fst _ _ =
        (snd (ofAffine (glVariety (rankTwo k) : Variety k))
          (P (k := k))).hom := by
    unfold glProjectiveFamilyPullbackLift
    exact pullback.lift_fst _ _ _
  have hglSnd :
      glProjectiveFamilyPullbackLift (k := k) (rankTwo k) ≫
          pullback.snd _ _ =
        (fst (ofAffine (glVariety (rankTwo k) : Variety k))
          (P (k := k))).hom := by
    unfold glProjectiveFamilyPullbackLift
    exact pullback.lift_snd _ _ _
  have hsourceFst :
      source ≫
          (fst (ofAffine (SLRankTwo (k := k))) (P (k := k))).hom ≫
          Spec.map (CommRingCat.ofHom
            (ofAffinePullback
              (slRankTwoToGL (k := k)).toVariety).toRingHom) =
        pullback.fst _ _ ≫
          Spec.map (glPullbackHom (k := k) phi) := by
    have hspec :
        Spec.map (toKernelPairRingHom (k := k) phi) ≫
            Spec.map (CommRingCat.ofHom
              (ofAffinePullback
                (slRankTwoToGL (k := k)).toVariety).toRingHom) =
          Spec.map (glPullbackHom (k := k) phi) := by
      rw [← Spec.map_comp]
    calc
      _ = (source ≫
            (fst (ofAffine (SLRankTwo (k := k))) (P (k := k))).hom) ≫
          Spec.map (CommRingCat.ofHom
            (ofAffinePullback
              (slRankTwoToGL (k := k)).toVariety).toRingHom) :=
        (Category.assoc _ _ _).symm
      _ = (pullback.fst _ _ ≫
            Spec.map (toKernelPairRingHom (k := k) phi)) ≫
          Spec.map (CommRingCat.ofHom
            (ofAffinePullback
              (slRankTwoToGL (k := k)).toVariety).toRingHom) := by
        exact congrArg
          (fun q ↦ q ≫ Spec.map (CommRingCat.ofHom
            (ofAffinePullback
              (slRankTwoToGL (k := k)).toVariety).toRingHom)) hfst
      _ = pullback.fst _ _ ≫
          (Spec.map (toKernelPairRingHom (k := k) phi) ≫
            Spec.map (CommRingCat.ofHom
              (ofAffinePullback
                (slRankTwoToGL (k := k)).toVariety).toRingHom)) :=
        Category.assoc _ _ _
      _ = _ := by rw [hspec]
  apply pullback.hom_ext
  · calc
      (source ≫ (actionPullbackPair (k := k)).hom ≫
          glProjectiveFamilyPullbackLift (k := k) (rankTwo k)) ≫
          pullback.fst _ _ =
        source ≫ (actionPullbackPair (k := k)).hom ≫
          (glProjectiveFamilyPullbackLift (k := k) (rankTwo k) ≫
            pullback.fst _ _) := by simp only [Category.assoc]
      _ = source ≫ (actionPullbackPair (k := k)).hom ≫
          (snd (ofAffine (glVariety (rankTwo k) : Variety k))
            (P (k := k))).hom := by rw [hglFst]
      _ = source ≫
          (snd (ofAffine (SLRankTwo (k := k))) (P (k := k))).hom := by
        simpa only [Category.assoc] using
          congrArg (fun q ↦ source ≫ q) hpairSnd
      _ = pullback.snd _ _ := hsnd
      _ = coefficientBaseChange (k := k) (glPullback (k := k) phi) ≫
          pullback.fst _ _ :=
        (coefficientBaseChange_fst (k := k) _ hbase).symm
  · calc
      (source ≫ (actionPullbackPair (k := k)).hom ≫
          glProjectiveFamilyPullbackLift (k := k) (rankTwo k)) ≫
          pullback.snd _ _ =
        pullback.fst _ _ ≫
          Spec.map (glPullbackHom (k := k) phi) := by
        simp only [Category.assoc]
        erw [hglSnd]
        erw [hpairFst]
        exact hsourceFst
      _ = coefficientBaseChange (k := k) (glPullback (k := k) phi) ≫
          pullback.snd _ _ := by
        simpa only [glPullbackHom_eq] using
          (coefficientBaseChange_snd (k := k)
            (glPullback (k := k) phi)).symm

private theorem sl2ProjectiveKernelPairLeftSource_actionPullback :
    sl2ProjectiveKernelPairLeftSource (k := k) ≫
        (actionPullbackPair (k := k)).hom ≫
        glProjectiveFamilyPullbackLift (k := k) (rankTwo k) =
      coefficientBaseChange (k := k)
        (glPullback (k := k) (kernelPairLeft (k := k))) := by
  exact source_actionPullback (k := k) (kernelPairLeft (k := k))
    (sl2ProjectiveKernelPairLeftSource (k := k))
    (sl2ProjectiveKernelPairLeftSource_fst (k := k))
    (sl2ProjectiveKernelPairLeftSource_snd (k := k))
    (left_glPullback_base (k := k))

private theorem sl2ProjectiveKernelPairRightSource_actionPullback :
    sl2ProjectiveKernelPairRightSource (k := k) ≫
        (actionPullbackPair (k := k)).hom ≫
        glProjectiveFamilyPullbackLift (k := k) (rankTwo k) =
      coefficientBaseChange (k := k)
        (glPullback (k := k) (kernelPairRight (k := k))) := by
  exact source_actionPullback (k := k) (kernelPairRight (k := k))
    (sl2ProjectiveKernelPairRightSource (k := k))
    (sl2ProjectiveKernelPairRightSource_fst (k := k))
    (sl2ProjectiveKernelPairRightSource_snd (k := k))
    (right_glPullback_base (k := k))

set_option maxHeartbeats 2000000 in
private theorem sl2ProjectiveKernelPairLeftSource_action :
    sl2ProjectiveKernelPairLeftSource (k := k) ≫
        (sl2ProjectiveMorphicAction (k := k)).actionMorphism.hom =
      sl2ProjectiveKernelPairLeftFamilyMap (k := k) := by
  let f := slProjectiveSubstitution (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairLeft (k := k))
  let hf := slProjectiveSubstitution_irrelevant (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairLeft (k := k))
  unfold sl2ProjectiveMorphicAction projectiveLinearMorphicActionPullback
  unfold projectiveLinearMorphicAction
  unfold projectiveLinearMorphicActionByCoordinates
  unfold glProjectiveActionMorphism
  unfold sl2ProjectiveKernelPairLeftFamilyMap
  change sl2ProjectiveKernelPairLeftSource (k := k) ≫
      (actionPullbackPair (k := k)).hom ≫
      glProjectiveFamilyPullbackLift (k := k) (rankTwo k) ≫
        polynomialProjFamilyMap k (G (k := k)) (Fin (rankTwo k))
          (glProjectiveSubstitution (k := k) (rankTwo k))
          (glProjectiveSubstitution_irrelevant (k := k) (rankTwo k)) =
    kernelPairProjectiveFamilyPullbackLift (k := k) ≫
      kernelPairProjectiveFamilyMap (k := k) f hf
  calc
    _ = (sl2ProjectiveKernelPairLeftSource (k := k) ≫
          (actionPullbackPair (k := k)).hom ≫
          glProjectiveFamilyPullbackLift (k := k) (rankTwo k)) ≫
        polynomialProjFamilyMap k (G (k := k)) (Fin (rankTwo k))
          (glProjectiveSubstitution (k := k) (rankTwo k))
          (glProjectiveSubstitution_irrelevant (k := k) (rankTwo k)) := by
      simp only [Category.assoc]
    _ = _ := by
      rw [sl2ProjectiveKernelPairLeftSource_actionPullback]
      exact coefficientBaseChange_familyMap (k := k)
        (glPullback (k := k) (kernelPairLeft (k := k)))
        f hf (left_glPullback_base (k := k)) (by
          simpa only [f] using
            slProjectiveSubstitution_natural (k := k)
              (kernelPairLeft (k := k)))

set_option maxHeartbeats 2000000 in
private theorem sl2ProjectiveKernelPairRightSource_action :
    sl2ProjectiveKernelPairRightSource (k := k) ≫
        (sl2ProjectiveMorphicAction (k := k)).actionMorphism.hom =
      sl2ProjectiveKernelPairRightFamilyMap (k := k) := by
  let f := slProjectiveSubstitution (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairRight (k := k))
  let hf := slProjectiveSubstitution_irrelevant (k := k)
    (R := PGL2KernelPairRing (k := k)) (kernelPairRight (k := k))
  unfold sl2ProjectiveMorphicAction projectiveLinearMorphicActionPullback
  unfold projectiveLinearMorphicAction
  unfold projectiveLinearMorphicActionByCoordinates
  unfold glProjectiveActionMorphism
  unfold sl2ProjectiveKernelPairRightFamilyMap
  change sl2ProjectiveKernelPairRightSource (k := k) ≫
      (actionPullbackPair (k := k)).hom ≫
      glProjectiveFamilyPullbackLift (k := k) (rankTwo k) ≫
        polynomialProjFamilyMap k (G (k := k)) (Fin (rankTwo k))
          (glProjectiveSubstitution (k := k) (rankTwo k))
          (glProjectiveSubstitution_irrelevant (k := k) (rankTwo k)) =
    kernelPairProjectiveFamilyPullbackLift (k := k) ≫
      kernelPairProjectiveFamilyMap (k := k) f hf
  calc
    _ = (sl2ProjectiveKernelPairRightSource (k := k) ≫
          (actionPullbackPair (k := k)).hom ≫
          glProjectiveFamilyPullbackLift (k := k) (rankTwo k)) ≫
        polynomialProjFamilyMap k (G (k := k)) (Fin (rankTwo k))
          (glProjectiveSubstitution (k := k) (rankTwo k))
          (glProjectiveSubstitution_irrelevant (k := k) (rankTwo k)) := by
      simp only [Category.assoc]
    _ = _ := by
      rw [sl2ProjectiveKernelPairRightSource_actionPullback]
      exact coefficientBaseChange_familyMap (k := k)
        (glPullback (k := k) (kernelPairRight (k := k)))
        f hf (right_glPullback_base (k := k)) (by
          simpa only [f] using
            slProjectiveSubstitution_natural (k := k)
              (kernelPairRight (k := k)))

/-- The characteristic-free scheme-level comparison between the genuine
regular `SL₂` action and the two independently constructed coordinate
families on its `PGL₂` kernel pair. -/
public structure SL2ProjectiveKernelPairActionBridge : Prop where
  left :
    sl2ProjectiveKernelPairLeftSource (k := k) ≫
        (sl2ProjectiveMorphicAction (k := k)).actionMorphism.hom =
      sl2ProjectiveKernelPairLeftFamilyMap (k := k)
  right :
    sl2ProjectiveKernelPairRightSource (k := k) ≫
        (sl2ProjectiveMorphicAction (k := k)).actionMorphism.hom =
      sl2ProjectiveKernelPairRightFamilyMap (k := k)

/-- The genuine regular `SL₂` projective action pulls back along the two
kernel-pair projections to the corresponding coordinate families. -/
public theorem sl2ProjectiveKernelPairActionBridge :
    SL2ProjectiveKernelPairActionBridge (k := k) where
  left := sl2ProjectiveKernelPairLeftSource_action (k := k)
  right := sl2ProjectiveKernelPairRightSource_action (k := k)

end Theory.AlgebraicGroup.Variety.Geometric
