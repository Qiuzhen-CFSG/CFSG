module

public import Mathlib.LinearAlgebra.Projectivization.Action
public import Theory.AlgebraicGroup.Instance.GL
public import Theory.AlgebraicGroup.Morphism.Basic
public import Theory.AlgebraicGroup.Variety.AffineGeometricMorphism
public import Theory.AlgebraicGroup.Variety.MorphicAction
public import Theory.AlgebraicGroup.Variety.PolynomialProjBaseChange
public import Theory.AlgebraicGroup.Variety.ProjectivePoint

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option warn.classDefReducibility false
set_option linter.style.haveILetI false

/-!
# Projective linear actions on geometric projective space

This module realizes the standard action of `GL` on projective space as a genuine regular
`MorphicAction`.  Homogeneous coordinate substitution is constructed on `Proj`, with the
irrelevant ideal controlled by the inverse matrix, and specialization identifies its rational
points with Mathlib's `Projectivization` action.  A basis then transports this coordinate model
to any finite-dimensional vector space, while the point equivalence supplies the bridge used by
Pluecker stabilizers.

The action pulls back along every algebraic-group morphism into `GL`, and its orbit morphism at a
nonzero vector is exposed together with an on-points projectivization formula.  The construction
uses the `Proj` and homogeneous-coordinate APIs rather than certificate fields.  Its geometric
input follows Borovoi, *Linear Algebraic Groups*, Chapter AG 7.2 and Chapter 2, Theorem 6.8.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

public noncomputable def glEntry (n : ℕ) (i j : Fin n) :
    Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k) :=
  (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction
    (glVariety n : Variety k)).symm
      (Variety.PolynomialFunction.ofPolynomial (glVariety n : Variety k)
        (MvPolynomial.X (Sum.inl (i, j))))

@[simp]
public theorem coordinatePointAlgHom_glEntry (n : ℕ)
    (g : Variety.Point (glVariety n : Variety k)) (i j : Fin n) :
    Theory.AlgebraicGroup.coordinatePointAlgHom (glVariety n : Variety k) g
        (glEntry n i j) = glMatrixOfPoint n g i j := by
  simp [glEntry, glMatrixOfPoint, Variety.PolynomialFunction.ofPolynomial,
    Variety.PolynomialFunction.toFun, Theory.AlgebraicGroup.evalPolynomial]

public noncomputable def glInverseEntry (n : ℕ) (i j : Fin n) :
    Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k) :=
  (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction
    (glVariety n : Variety k)).symm
      (Variety.PolynomialFunction.ofPolynomial (glVariety n : Variety k)
        (glInvPolynomial (k := k) n
          (Sum.inl (i, j) : (glVariety n : Variety k).Coordinates)))

@[simp]
public theorem coordinatePointAlgHom_glInverseEntry (n : ℕ)
    (g : Variety.Point (glVariety n : Variety k)) (i j : Fin n) :
    Theory.AlgebraicGroup.coordinatePointAlgHom (glVariety n : Variety k) g
        (glInverseEntry n i j) =
      (((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)⁻¹) i j := by
  rw [Theory.AlgebraicGroup.coordinatePointAlgHom_apply]
  simp only [glInverseEntry, AlgEquiv.apply_symm_apply,
    Variety.PolynomialFunction.ofPolynomial, Variety.PolynomialFunction.toFun]
  calc
    Theory.AlgebraicGroup.evalPolynomial g.val
        (glInvPolynomial (k := k) n
          (Sum.inl (i, j) : (glVariety n : Variety k).Coordinates)) =
        (g⁻¹).val
          (Sum.inl (i, j) : (glVariety n : Variety k).Coordinates) :=
      (AlgebraicGroup.inv_regular (V := (glVariety n : Variety k))
        (Sum.inl (i, j) : (glVariety n : Variety k).Coordinates) g).symm
    _ = (((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)⁻¹) i j := by
      change glMatrixOfPoint n (g⁻¹) i j = _
      have h := congrArg
        (fun A : GL (Fin n) k ↦ (A : Matrix (Fin n) (Fin n) k) i j)
        ((translationGLPointMulEquiv (k := k) n).map_inv g)
      have htrans : translationGLPointMulEquiv (k := k) n g = glPointEquiv n g := rfl
      have htrans_inv : translationGLPointMulEquiv (k := k) n (g⁻¹) =
          glPointEquiv n (g⁻¹) := rfl
      rw [htrans] at h
      rw [htrans_inv] at h
      have hmat :
          ((glPointEquiv n (g⁻¹) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
            glMatrixOfPoint n (g⁻¹) := by
        dsimp [glPointEquiv]
      have hmat_g :
          ((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
            glMatrixOfPoint n g := by
        dsimp [glPointEquiv]
      rw [hmat] at h
      rw [Matrix.GeneralLinearGroup.coe_inv, hmat_g] at h
      exact h

public theorem glInverseEntry_mul_entry (n : ℕ) (i j : Fin n) :
    ∑ l : Fin n, glInverseEntry (k := k) n i l * glEntry (k := k) n l j =
      if i = j then 1 else 0 := by
  apply (Theory.AlgebraicGroup.coordinateRingAlgEquivPolynomialFunction
    (glVariety n : Variety k)).injective
  apply Variety.PolynomialFunction.ext
  intro g
  change Theory.AlgebraicGroup.coordinatePointAlgHom
      (glVariety n : Variety k) g
        (∑ l : Fin n, glInverseEntry (k := k) n i l * glEntry (k := k) n l j) =
    Theory.AlgebraicGroup.coordinatePointAlgHom
      (glVariety n : Variety k) g (if i = j then 1 else 0)
  simp only [map_mul, coordinatePointAlgHom_glInverseEntry,
    coordinatePointAlgHom_glEntry, map_sum]
  rw [← Matrix.mul_apply]
  have hunit : IsUnit
      ((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (glPointEquiv n g).isUnit
  change
    ((((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)⁻¹ *
      ((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) i j) = _
  rw [Matrix.nonsing_inv_mul _ hunit]
  by_cases h : i = j
  · subst j
    rw [Theory.AlgebraicGroup.coordinatePointAlgHom_apply]
    simp [Variety.PolynomialFunction.toFun]
  · simp [Matrix.one_apply, h]

public noncomputable def glProjectiveSubstitution (n : ℕ) :
    projectiveGrading (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k)) (Fin n) →+*ᵍ
      projectiveGrading (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k)) (Fin n) :=
    GradedRingHom.mk
    (MvPolynomial.eval₂Hom
      (MvPolynomial.C : Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k) →+*
        MvPolynomial (Fin n)
          (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k)))
      (fun i ↦
        ∑ j : Fin n, MvPolynomial.C (glEntry n i j) * MvPolynomial.X j))
      fun {d} p hp ↦ by
        have hvars (i : Fin n) :
            (∑ j : Fin n, MvPolynomial.C (glEntry n i j) * MvPolynomial.X j :
              MvPolynomial (Fin n)
                (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))).IsHomogeneous 1 := by
          apply MvPolynomial.IsHomogeneous.sum
          intro j _
          exact MvPolynomial.isHomogeneous_C_mul_X (glEntry n i j) j
        exact (MvPolynomial.mem_homogeneousSubmodule d _).mpr (by
          have heval := hp.eval₂
            (MvPolynomial.C : Theory.AlgebraicGroup.coordinateRing
              (glVariety n : Variety k) →+*
                MvPolynomial (Fin n)
                  (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k)))
            (fun i ↦
              ∑ j : Fin n, MvPolynomial.C (glEntry n i j) * MvPolynomial.X j)
            (fun r ↦ MvPolynomial.isHomogeneous_C _ r) hvars
          change (MvPolynomial.eval₂
            (MvPolynomial.C : Theory.AlgebraicGroup.coordinateRing
              (glVariety n : Variety k) →+*
                MvPolynomial (Fin n)
                  (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k)))
            (fun i ↦
              ∑ j : Fin n, MvPolynomial.C (glEntry n i j) * MvPolynomial.X j) p).IsHomogeneous d
          simpa only [one_mul] using heval)

@[simp]
public theorem glProjectiveSubstitution_X (n : ℕ) (i : Fin n) :
    glProjectiveSubstitution (k := k) n (MvPolynomial.X i) =
      ∑ j : Fin n, MvPolynomial.C (glEntry n i j) * MvPolynomial.X j := by
  simp [glProjectiveSubstitution]

public theorem coordinate_irrelevant_le_span
    (A : Type u) [CommRing A] (sigma : Type) :
    (HomogeneousIdeal.irrelevant (projectiveGrading A sigma)).toIdeal ≤
      Ideal.span (Set.range (MvPolynomial.X : sigma → MvPolynomial sigma A)) := by
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro d hd p hp
  change p ∈ Ideal.span (Set.range (MvPolynomial.X : sigma → MvPolynomial sigma A))
  rw [show Set.range (MvPolynomial.X : sigma → MvPolynomial sigma A) =
    MvPolynomial.X '' (Set.univ : Set sigma) by simp]
  rw [MvPolynomial.mem_ideal_span_X_image]
  intro m hm
  have hdegree :=
    ((MvPolynomial.mem_homogeneousSubmodule d p).mp hp).degree_eq_sum_deg_support hm
  have hsupp : m.support.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty.mp h, Finset.sum_empty] at hdegree
    omega
  obtain ⟨i, hi⟩ := hsupp
  exact ⟨i, Set.mem_univ i, Finsupp.mem_support_iff.mp hi⟩

public theorem glProjectiveSubstitution_irrelevant (n : ℕ) :
    HomogeneousIdeal.irrelevant
        (projectiveGrading (Theory.AlgebraicGroup.coordinateRing
          (glVariety n : Variety k)) (Fin n)) ≤
      (HomogeneousIdeal.irrelevant
        (projectiveGrading (Theory.AlgebraicGroup.coordinateRing
          (glVariety n : Variety k)) (Fin n))).map
        (glProjectiveSubstitution (k := k) n) := by
  rw [← toIdeal_le_toIdeal_iff]
  refine (coordinate_irrelevant_le_span
    (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k)) (Fin n)).trans ?_
  rw [Ideal.span_le]
  rintro _ ⟨j, rfl⟩
  have hcomb :
      ∑ i : Fin n, MvPolynomial.C (glInverseEntry (k := k) n j i) *
          glProjectiveSubstitution (k := k) n (MvPolynomial.X i) =
        MvPolynomial.X j := by
    simp_rw [glProjectiveSubstitution_X (k := k)]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [← mul_assoc, ← map_mul]
    simp_rw [← Finset.sum_mul]
    simp_rw [← map_sum]
    simp_rw [glInverseEntry_mul_entry (k := k)]
    simp [apply_ite MvPolynomial.C, Finset.sum_ite_eq', mul_ite]
  rw [← hcomb]
  apply Ideal.sum_mem
  intro i _
  exact Ideal.mul_mem_left _ _
    (Ideal.mem_map_of_mem (glProjectiveSubstitution (k := k) n)
      (HomogeneousIdeal.mem_irrelevant_of_mem _ one_pos
        (MvPolynomial.isHomogeneous_X _ i)))

public theorem glProjectiveSubstitution_overBase (n : ℕ) :
    Proj.map (glProjectiveSubstitution (k := k) n)
        (glProjectiveSubstitution_irrelevant (k := k) n) ≫
      polynomialProjStructureMap
        (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k)) (Fin n) =
    polynomialProjStructureMap
      (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k)) (Fin n) := by
  exact polynomialProjMap_preserves_structureMap _ _
    (glProjectiveSubstitution (k := k) n)
    (glProjectiveSubstitution_irrelevant (k := k) n)
    (by intro r; simp [glProjectiveSubstitution])

private noncomputable def glProjectivePointMulAction (E : Type u)
    [AddCommGroup E] [Module k E] [FiniteDimensional k E] :
    MulAction (Variety.Point (glVarietyOf k E))
      (Point (projectiveSpace k E)) := by
  let rho : Variety.Point (glVarietyOf k E) →*
      LinearMap.GeneralLinearGroup k (Fin (Module.finrank k E) → k) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (translationGLPointMulEquiv (k := k) (Module.finrank k E)).toMonoidHom
  letI : MulAction (Variety.Point (glVarietyOf k E))
      (Projectivization k (Fin (Module.finrank k E) → k)) :=
    MulAction.compHom _ rho
  exact (projectiveSpaceByCoordinatesPointEquiv (k := k)
    (sigma := Fin (Module.finrank k E))).mulAction _

private theorem glMatrix_mulVec_ne_zero (n : ℕ)
    (g : Variety.Point (glVariety n : Variety k))
    (v : Fin n → k) (hv : v ≠ 0) :
    (((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) ≠ 0 := by
  intro hz
  have hunit : IsUnit
      ((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (glPointEquiv n g).isUnit
  have hinv :
      ((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)⁻¹ *
        ((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = 1 :=
    Matrix.nonsing_inv_mul _ hunit
  have hzero := congrArg
    (fun w : Fin n → k ↦
      (((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)⁻¹).mulVec w) hz
  rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec, Matrix.mulVec_zero] at hzero
  exact hv hzero

private theorem projectivePoint_comp_projMap
    {sigma : Type} [Finite sigma] (v w : sigma → k)
    (hv : v ≠ 0) (hw : w ≠ 0)
    (f : projectiveGrading k sigma →+*ᵍ projectiveGrading k sigma)
    (hf : HomogeneousIdeal.irrelevant (projectiveGrading k sigma) ≤
      (HomogeneousIdeal.irrelevant (projectiveGrading k sigma)).map f)
    (hbase : Proj.map f hf ≫
      (projectiveSpaceByCoordinates k sigma).structureMap =
      (projectiveSpaceByCoordinates k sigma).structureMap)
    (heval : ∀ p : MvPolynomial sigma k,
      MvPolynomial.eval₂Hom (RingHom.id k) v (f p) =
        MvPolynomial.eval₂Hom (RingHom.id k) w p) :
    (projectivePointOfVector v hv).1 ≫ Proj.map f hf =
      (projectivePointOfVector w hw).1 := by
  letI : LocallyOfFiniteType
      (Proj.toSpecZero (projectiveGrading k sigma) ≫
        Spec.map (CommRingCat.ofHom
          (algebraMap k (projectiveGrading k sigma 0)))) :=
    (projectiveSpaceByCoordinates k sigma).finiteType
  refine @ext_of_apply_closedPoint_eq
    (X := Proj (projectiveGrading k sigma)) (K := k)
    (f := (projectivePointOfVector v hv).1 ≫ Proj.map f hf)
    (g := (projectivePointOfVector w hw).1)
    _ _ (Proj.toSpecZero _ ≫ Spec.map _) (projectiveSpaceByCoordinates k sigma).finiteType ?_ ?_ ?_
  · calc
      ((projectivePointOfVector v hv).1 ≫ Proj.map f hf) ≫
          (projectiveSpaceByCoordinates k sigma).structureMap =
        (projectivePointOfVector v hv).1 ≫
          (Proj.map f hf ≫ (projectiveSpaceByCoordinates k sigma).structureMap) := by
            exact Category.assoc _ _ _
      _ = (projectivePointOfVector v hv).1 ≫
          (projectiveSpaceByCoordinates k sigma).structureMap := by
            exact congrArg (fun q ↦ (projectivePointOfVector v hv).1 ≫ q) hbase
      _ = 𝟙 _ := by
        simpa only [projectiveSpaceByCoordinates_toScheme] using
          (projectivePointOfVector v hv).property
  · exact (projectivePointOfVector w hw).property
  · apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext'
    intro d p hp
    change f p ∈
        ((projectivePointOfVector v hv).1 (IsLocalRing.closedPoint k)).asHomogeneousIdeal ↔
      p ∈ ((projectivePointOfVector w hw).1 (IsLocalRing.closedPoint k)).asHomogeneousIdeal
    calc
      f p ∈ ((projectivePointOfVector v hv).1 (IsLocalRing.closedPoint k)).asHomogeneousIdeal ↔
          MvPolynomial.eval₂Hom (RingHom.id k) v (f p) = 0 :=
        projectivePointOfVector_mem_iff _ _ (f.map_mem hp)
      _ ↔ MvPolynomial.eval₂Hom (RingHom.id k) w p = 0 := by rw [heval p]
      _ ↔ p ∈ ((projectivePointOfVector w hw).1 (IsLocalRing.closedPoint k)).asHomogeneousIdeal :=
        (projectivePointOfVector_mem_iff _ _ hp).symm

private theorem specialized_projective_vector_map
    (n : ℕ) (g : Variety.Point (glVariety n : Variety k))
    (v : Fin n → k) (hv : v ≠ 0) :
    (projectivePointOfVector v hv).1 ≫
        Proj.map
          (((polynomialCoefficientMap (Fin n)
              (Theory.AlgebraicGroup.coordinatePointAlgHom
                (glVariety n : Variety k) g).toRingHom).comp
            (glProjectiveSubstitution (k := k) n)).comp
            (polynomialCoefficientMap (Fin n)
              (algebraMap k (Theory.AlgebraicGroup.coordinateRing
                (glVariety n : Variety k)))))
          (polynomialProjSpecializedMap_irrelevant k
            (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
            (Fin n)
            (Theory.AlgebraicGroup.coordinatePointAlgHom
              (glVariety n : Variety k) g)
            (glProjectiveSubstitution (k := k) n)
            (glProjectiveSubstitution_irrelevant (k := k) n)) =
      (projectivePointOfVector
        (((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v)
        (glMatrix_mulVec_ne_zero (k := k) n g v hv)).1 := by
  let f := (((polynomialCoefficientMap (Fin n)
      (Theory.AlgebraicGroup.coordinatePointAlgHom
        (glVariety n : Variety k) g).toRingHom).comp
    (glProjectiveSubstitution (k := k) n)).comp
    (polynomialCoefficientMap (Fin n)
      (algebraMap k (Theory.AlgebraicGroup.coordinateRing
        (glVariety n : Variety k)))))
  have heval_hom :
      (MvPolynomial.eval₂Hom (RingHom.id k) v).comp f.toRingHom =
        MvPolynomial.eval₂Hom (RingHom.id k)
          (((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [f, glProjectiveSubstitution, polynomialCoefficientMap_C]
    · intro i
      simp [f, glProjectiveSubstitution, polynomialCoefficientMap_C,
        Matrix.mulVec, dotProduct]
      apply Finset.sum_congr rfl
      intro x hx
      change Theory.AlgebraicGroup.coordinatePointAlgHom
          (glVariety n : Variety k) g (glEntry n i x) * v x = _
      rw [coordinatePointAlgHom_glEntry]
      have hmat :
          ((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) =
            glMatrixOfPoint n g := by
        dsimp [glPointEquiv]
      rw [hmat]
  let hf := polynomialProjSpecializedMap_irrelevant k
    (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
    (Fin n)
    (Theory.AlgebraicGroup.coordinatePointAlgHom
      (glVariety n : Variety k) g)
    (glProjectiveSubstitution (k := k) n)
    (glProjectiveSubstitution_irrelevant (k := k) n)
  have hbase_specialized := polynomialProjSpecializedMap_overBase k
    (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
    (Fin n)
    (Theory.AlgebraicGroup.coordinatePointAlgHom
      (glVariety n : Variety k) g)
    (glProjectiveSubstitution (k := k) n)
    (glProjectiveSubstitution_irrelevant (k := k) n)
    (glProjectiveSubstitution_overBase (k := k) n)
  have hbase :
      Proj.map f hf ≫ (projectiveSpaceByCoordinates k (Fin n)).structureMap =
        (projectiveSpaceByCoordinates k (Fin n)).structureMap := by
    rw [show Proj.map f hf =
        polynomialProjSpecializedMap k
          (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
          (Fin n)
          (Theory.AlgebraicGroup.coordinatePointAlgHom
            (glVariety n : Variety k) g)
          (glProjectiveSubstitution (k := k) n)
          (glProjectiveSubstitution_irrelevant (k := k) n) by
      apply (polynomialProjSpecializedMap_eq_projMap k
        (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
        (Fin n)
        (Theory.AlgebraicGroup.coordinatePointAlgHom
          (glVariety n : Variety k) g)
        (glProjectiveSubstitution (k := k) n)
        (glProjectiveSubstitution_irrelevant (k := k) n)).symm]
    exact hbase_specialized
  have heval : ∀ p : MvPolynomial (Fin n) k,
      MvPolynomial.eval₂Hom (RingHom.id k) v (f p) =
        MvPolynomial.eval₂Hom (RingHom.id k)
          (((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) p := by
    intro p
    exact congrArg (fun h ↦ h p) heval_hom
  simpa only [f, hf] using
    (projectivePoint_comp_projMap (k := k)
      (v := v)
      (w := (((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v))
      (hv := hv)
      (hw := glMatrix_mulVec_ne_zero (k := k) n g v hv)
      (f := f) (hf := hf) (hbase := hbase) (heval := heval))

public noncomputable def glProjectiveFamilyPullbackLift (n : ℕ) :
    (prod (ofAffine (glVariety n : Variety k))
      (projectiveSpaceByCoordinates k (Fin n))).toScheme ⟶
      pullback (projectiveSpaceByCoordinates k (Fin n)).structureMap
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (Theory.AlgebraicGroup.coordinateRing
            (glVariety n : Variety k))))) :=
  pullback.lift
    (snd (ofAffine (glVariety n : Variety k))
      (projectiveSpaceByCoordinates k (Fin n))).hom
    (fst (ofAffine (glVariety n : Variety k))
      (projectiveSpaceByCoordinates k (Fin n))).hom (by
      change (snd (ofAffine (glVariety n : Variety k))
          (projectiveSpaceByCoordinates k (Fin n))).hom ≫
          (projectiveSpaceByCoordinates k (Fin n)).structureMap =
        (fst (ofAffine (glVariety n : Variety k))
          (projectiveSpaceByCoordinates k (Fin n))).hom ≫ Spec.map
            (CommRingCat.ofHom (algebraMap k
              (Theory.AlgebraicGroup.coordinateRing
                (glVariety n : Variety k))))
      rw [(snd (ofAffine (glVariety n : Variety k))
        (projectiveSpaceByCoordinates k (Fin n))).commutes]
      exact (fst (ofAffine (glVariety n : Variety k))
        (projectiveSpaceByCoordinates k (Fin n))).commutes.symm)

public noncomputable def glProjectiveActionMorphism (n : ℕ) :
    Morphism (prod (ofAffine (glVariety n : Variety k))
      (projectiveSpaceByCoordinates k (Fin n)))
      (projectiveSpaceByCoordinates k (Fin n)) := by
  let f := glProjectiveSubstitution (k := k) n
  let hf := glProjectiveSubstitution_irrelevant (k := k) n
  let q := glProjectiveFamilyPullbackLift (k := k) n
  let hmap := q ≫ polynomialProjFamilyMap k
    (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
    (Fin n) f hf
  refine { hom := hmap, commutes := ?_ }
  rw [Category.assoc, polynomialProjFamilyMap_overBase k
    (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
    (Fin n) f hf (glProjectiveSubstitution_overBase (k := k) n)]
  have hq : q ≫ pullback.snd (projectiveSpaceByCoordinates k (Fin n)).structureMap
      (Spec.map (CommRingCat.ofHom
        (algebraMap k (Theory.AlgebraicGroup.coordinateRing
          (glVariety n : Variety k))))) =
      (fst (ofAffine (glVariety n : Variety k))
        (projectiveSpaceByCoordinates k (Fin n))).hom := by
    unfold q glProjectiveFamilyPullbackLift
    exact pullback.lift_snd _ _ _
  rw [← Category.assoc, hq]
  exact (fst (ofAffine (glVariety n : Variety k))
    (projectiveSpaceByCoordinates k (Fin n))).commutes

private theorem glProjectiveFamilyPullbackLift_prodPoint (n : ℕ)
    (g : Variety.Point (glVariety n : Variety k))
    (x : Point (projectiveSpaceByCoordinates k (Fin n))) :
    (prodPoint ((affinePointEquiv (glVariety n : Variety k)).symm g) x).1 ≫
        glProjectiveFamilyPullbackLift (k := k) n =
      x.1 ≫ polynomialProjSpecializationLift k
        (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
        (Fin n)
        (Theory.AlgebraicGroup.coordinatePointAlgHom
          (glVariety n : Variety k) g) := by
  apply pullback.hom_ext
  · have hq : glProjectiveFamilyPullbackLift (k := k) n ≫
        pullback.fst (projectiveSpaceByCoordinates k (Fin n)).structureMap
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (Theory.AlgebraicGroup.coordinateRing
              (glVariety n : Variety k))))) =
        (snd (ofAffine (glVariety n : Variety k))
          (projectiveSpaceByCoordinates k (Fin n))).hom := by
      unfold glProjectiveFamilyPullbackLift
      exact pullback.lift_fst _ _ _
    have hp : (prodPoint ((affinePointEquiv (glVariety n : Variety k)).symm g) x).1 ≫
        (snd (ofAffine (glVariety n : Variety k))
          (projectiveSpaceByCoordinates k (Fin n))).hom = x.1 := by
      exact congrArg Subtype.val (snd_prodPoint
        ((affinePointEquiv (glVariety n : Variety k)).symm g) x)
    rw [Category.assoc, hq]
    rw [hp]
    change x.1 = x.1 ≫
      polynomialProjSpecializationLift k
        (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
        (Fin n)
        (Theory.AlgebraicGroup.coordinatePointAlgHom
          (glVariety n : Variety k) g) ≫
      pullback.fst (projectiveSpaceByCoordinates k (Fin n)).structureMap
        (Spec.map (CommRingCat.ofHom
          (algebraMap k (Theory.AlgebraicGroup.coordinateRing
            (glVariety n : Variety k)))))
    have hx := congrArg (fun f ↦ x.1 ≫ f)
      (polynomialProjSpecializationLift_fst k
        (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
        (Fin n)
        (Theory.AlgebraicGroup.coordinatePointAlgHom
          (glVariety n : Variety k) g))
    exact (Category.comp_id x.1).symm.trans hx.symm
  · have hq : glProjectiveFamilyPullbackLift (k := k) n ≫
        pullback.snd (projectiveSpaceByCoordinates k (Fin n)).structureMap
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (Theory.AlgebraicGroup.coordinateRing
              (glVariety n : Variety k))))) =
        (fst (ofAffine (glVariety n : Variety k))
          (projectiveSpaceByCoordinates k (Fin n))).hom := by
      unfold glProjectiveFamilyPullbackLift
      exact pullback.lift_snd _ _ _
    have hp : (prodPoint ((affinePointEquiv (glVariety n : Variety k)).symm g) x).1 ≫
        (fst (ofAffine (glVariety n : Variety k))
          (projectiveSpaceByCoordinates k (Fin n))).hom =
        ((affinePointEquiv (glVariety n : Variety k)).symm g).1 := by
      exact congrArg Subtype.val (fst_prodPoint
        ((affinePointEquiv (glVariety n : Variety k)).symm g) x)
    rw [Category.assoc, hq]
    change (prodPoint ((affinePointEquiv (glVariety n : Variety k)).symm g) x).1 ≫
      (fst (ofAffine (glVariety n : Variety k))
        (projectiveSpaceByCoordinates k (Fin n))).hom = _
    rw [hp]
    change ((affinePointEquiv (glVariety n : Variety k)).symm g).1 =
      x.1 ≫ polynomialProjSpecializationLift k
        (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
        (Fin n)
        (Theory.AlgebraicGroup.coordinatePointAlgHom
          (glVariety n : Variety k) g) ≫
        pullback.snd (projectiveSpaceByCoordinates k (Fin n)).structureMap
          (Spec.map (CommRingCat.ofHom
            (algebraMap k (Theory.AlgebraicGroup.coordinateRing
              (glVariety n : Variety k)))))
    have hpoint : ((affinePointEquiv (glVariety n : Variety k)).symm g).1 =
        Spec.map (CommRingCat.ofHom
          (Theory.AlgebraicGroup.coordinatePointAlgHom
            (glVariety n : Variety k) g).toRingHom) := by
      change Spec.map (CommRingCat.ofHom
          (Theory.AlgebraicGroup.coordinatePointAlgHom
            (glVariety n : Variety k) g).toRingHom) = _
      rfl
    have hx := congrArg (fun f ↦ x.1 ≫ f)
      (polynomialProjSpecializationLift_snd k
        (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
        (Fin n)
        (Theory.AlgebraicGroup.coordinatePointAlgHom
          (glVariety n : Variety k) g))
    have hbase : Spec.map (CommRingCat.ofHom
          (Theory.AlgebraicGroup.coordinatePointAlgHom
            (glVariety n : Variety k) g).toRingHom) =
        x.1 ≫ polynomialProjStructureMap k (Fin n) ≫
          Spec.map (CommRingCat.ofHom
            (Theory.AlgebraicGroup.coordinatePointAlgHom
              (glVariety n : Variety k) g).toRingHom) := by
      have hsm : polynomialProjStructureMap k (Fin n) =
          (projectiveSpaceByCoordinates k (Fin n)).structureMap := by
        exact polynomialProjStructureMap_eq_projectiveSpaceByCoordinates k (Fin n)
      have hxprop : x.1 ≫ polynomialProjStructureMap k (Fin n) = 𝟙 _ := by
        rw [hsm]
        exact x.property
      calc
        Spec.map (CommRingCat.ofHom
            (Theory.AlgebraicGroup.coordinatePointAlgHom
              (glVariety n : Variety k) g).toRingHom) =
            𝟙 (Spec (CommRingCat.of k)) ≫
              Spec.map (CommRingCat.ofHom
                (Theory.AlgebraicGroup.coordinatePointAlgHom
                  (glVariety n : Variety k) g).toRingHom) :=
              (Category.id_comp _).symm
        _ = (x.1 ≫ polynomialProjStructureMap k (Fin n)) ≫
              Spec.map (CommRingCat.ofHom
                (Theory.AlgebraicGroup.coordinatePointAlgHom
                  (glVariety n : Variety k) g).toRingHom) := by
              rw [hxprop]
        _ = x.1 ≫ polynomialProjStructureMap k (Fin n) ≫
              Spec.map (CommRingCat.ofHom
                (Theory.AlgebraicGroup.coordinatePointAlgHom
                  (glVariety n : Variety k) g).toRingHom) :=
              Category.assoc _ _ _
    exact hpoint.trans (hbase.trans hx.symm)

public noncomputable def glCoordinatePointMulAction (n : ℕ) :
    MulAction (Variety.Point (glVariety n : Variety k))
      (Point (projectiveSpaceByCoordinates k (Fin n))) := by
  let rho : Variety.Point (glVariety n : Variety k) →*
      LinearMap.GeneralLinearGroup k (Fin n → k) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (translationGLPointMulEquiv (k := k) n).toMonoidHom
  letI : MulAction (Variety.Point (glVariety n : Variety k))
      (Projectivization k (Fin n → k)) := MulAction.compHom _ rho
  exact Equiv.mulAction (Variety.Point (glVariety n : Variety k))
    (projectiveSpaceByCoordinatesPointEquiv (k := k)
      (sigma := Fin n))

private theorem glCoordinatePointMulAction_projectivePointOfVector (n : ℕ)
    (g : Variety.Point (glVariety n : Variety k)) (v : Fin n → k) (hv : v ≠ 0) :
    letI := glCoordinatePointMulAction (k := k) n
    g • (projectivePointOfVector v hv) =
      projectivePointOfVector
        (((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v)
        (glMatrix_mulVec_ne_zero (k := k) n g v hv) := by
  let rho : Variety.Point (glVariety n : Variety k) →*
      LinearMap.GeneralLinearGroup k (Fin n → k) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (translationGLPointMulEquiv (k := k) n).toMonoidHom
  letI : MulAction (Variety.Point (glVariety n : Variety k))
      (Projectivization k (Fin n → k)) := MulAction.compHom _ rho
  apply (projectiveSpaceByCoordinatesPointEquiv (k := k)
    (sigma := Fin n)).injective
  change (projectiveSpaceByCoordinatesPointEquiv (k := k) (sigma := Fin n))
      ((projectiveSpaceByCoordinatesPointEquiv (k := k) (sigma := Fin n)).symm
        (g • (projectiveSpaceByCoordinatesPointEquiv (k := k) (sigma := Fin n))
          (projectivePointOfVector v hv))) = _
  have hsmul := congrArg
    (projectiveSpaceByCoordinatesPointEquiv (k := k) (sigma := Fin n))
    (Equiv.smul_def
      (e := projectiveSpaceByCoordinatesPointEquiv (k := k) (sigma := Fin n)) g
      (projectivePointOfVector v hv))
  simp only [Equiv.apply_symm_apply] at hsmul
  rw [Equiv.apply_symm_apply]
  rw [projectiveSpaceByCoordinatesPointEquiv_projectivePointOfVector]
  change rho g • Projectivization.mk k v hv = _
  rw [Projectivization.smul_mk]
  rw [projectiveSpaceByCoordinatesPointEquiv_projectivePointOfVector]
  change Projectivization.mk k
      (((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v) _ = _
  rfl

public theorem glProjectiveActionMorphism_apply (n : ℕ)
    (g : Variety.Point (glVariety n : Variety k))
    (x : Point (projectiveSpaceByCoordinates k (Fin n))) :
    glProjectiveActionMorphism (k := k) n
        (prodPoint ((affinePointEquiv (glVariety n : Variety k)).symm g) x) =
      letI := glCoordinatePointMulAction (k := k) n
      g • x := by
  letI := glCoordinatePointMulAction (k := k) n
  let rho : Variety.Point (glVariety n : Variety k) →*
      LinearMap.GeneralLinearGroup k (Fin n → k) :=
    Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp
      (translationGLPointMulEquiv (k := k) n).toMonoidHom
  letI : MulAction (Variety.Point (glVariety n : Variety k))
      (Projectivization k (Fin n → k)) := MulAction.compHom _ rho
  apply (projectiveSpaceByCoordinatesPointEquiv (k := k)
    (sigma := Fin n)).injective
  induction hq : (projectiveSpaceByCoordinatesPointEquiv (k := k)
      (sigma := Fin n)) x using Projectivization.ind with
  | h v hv =>
    have hx : x = projectivePointOfVector v hv := by
      apply (projectiveSpaceByCoordinatesPointEquiv (k := k)
        (sigma := Fin n)).injective
      rw [hq, projectiveSpaceByCoordinatesPointEquiv_projectivePointOfVector]
    subst x
    rw [glCoordinatePointMulAction_projectivePointOfVector (k := k) n g v hv]
    rw [projectiveSpaceByCoordinatesPointEquiv_projectivePointOfVector]
    have hpoint :
        glProjectiveActionMorphism (k := k) n
            (prodPoint ((affinePointEquiv (glVariety n : Variety k)).symm g)
              (projectivePointOfVector v hv)) =
          projectivePointOfVector
            (((glPointEquiv n g : GL (Fin n) k) : Matrix (Fin n) (Fin n) k).mulVec v)
            (glMatrix_mulVec_ne_zero (k := k) n g v hv) := by
      apply Subtype.ext
      change (prodPoint ((affinePointEquiv (glVariety n : Variety k)).symm g)
          (projectivePointOfVector v hv)).1 ≫
        glProjectiveFamilyPullbackLift (k := k) n ≫
        polynomialProjFamilyMap k
          (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
          (Fin n) (glProjectiveSubstitution (k := k) n)
          (glProjectiveSubstitution_irrelevant (k := k) n) = _
      rw [← Category.assoc, glProjectiveFamilyPullbackLift_prodPoint]
      have hspec := polynomialProjFamilyMap_specialization_point k
        (Theory.AlgebraicGroup.coordinateRing (glVariety n : Variety k))
        (Fin n)
        (Theory.AlgebraicGroup.coordinatePointAlgHom
          (glVariety n : Variety k) g)
        (glProjectiveSubstitution (k := k) n)
        (glProjectiveSubstitution_irrelevant (k := k) n)
        (projectivePointOfVector v hv).1
      rw [polynomialProjSpecializedMap_eq_projMap] at hspec
      exact (Category.assoc _ _ _).trans (hspec.trans
        (specialized_projective_vector_map (k := k) n g v hv))
    rw [hpoint]
    exact projectiveSpaceByCoordinatesPointEquiv_projectivePointOfVector _ _

public noncomputable def projectiveLinearMorphicActionByCoordinates (n : ℕ) :
    MorphicAction (glVariety n : Variety k)
      (projectiveSpaceByCoordinates k (Fin n)) := by
  letI := glCoordinatePointMulAction (k := k) n
  refine { toMulAction := inferInstance, actionMorphism :=
    glProjectiveActionMorphism (k := k) n, actionMorphism_apply := ?_ }
  exact glProjectiveActionMorphism_apply (k := k) n

public noncomputable def projectiveLinearMorphicAction
    (E : Type u) [AddCommGroup E] [Module k E] [FiniteDimensional k E] :
    MorphicAction (glVarietyOf k E) (projectiveSpace k E) :=
  projectiveLinearMorphicActionByCoordinates (k := k) (Module.finrank k E)

private theorem glPointEquivOf_apply_vector_coordinates
    {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (g : Variety.Point (glVarietyOf k E)) (v : E) :
    b.equivFun.symm
        (((glPointEquiv (Module.finrank k E) g : GL (Fin (Module.finrank k E)) k) :
          Matrix (Fin (Module.finrank k E)) (Fin (Module.finrank k E)) k).mulVec
            (b.equivFun v)) =
      (glPointEquivOf k E b g).1 v := by
  rfl

public theorem projectiveLinearMorphicAction_projectiveSpacePointEquivOf_projectivePointOfVector
    {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (g : Variety.Point (glVarietyOf k E)) (v : E) (hv : v ≠ 0) :
    projectiveSpacePointEquivOf b
        ((projectiveLinearMorphicAction (k := k) E).toMulAction.smul g
          (projectivePointOfVector (b.equivFun v)
            (b.equivFun.map_ne_zero_iff.mpr hv))) =
      Projectivization.map (glPointEquivOf k E b g).1
      (glPointEquivOf k E b g).toLinearEquiv.injective
        (Projectivization.mk k v hv) := by
  have hcoord := glCoordinatePointMulAction_projectivePointOfVector (k := k)
    (Module.finrank k E) g (b.equivFun v)
    (b.equivFun.map_ne_zero_iff.mpr hv)
  have hrew : (projectiveLinearMorphicAction (k := k) E).toMulAction.smul g
      (projectivePointOfVector (b.equivFun v)
        (b.equivFun.map_ne_zero_iff.mpr hv)) =
      projectivePointOfVector
        (((glPointEquiv (Module.finrank k E) g :
          GL (Fin (Module.finrank k E)) k) :
          Matrix (Fin (Module.finrank k E)) (Fin (Module.finrank k E)) k).mulVec
            (b.equivFun v))
        (glMatrix_mulVec_ne_zero (k := k) (Module.finrank k E) g
          (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv)) := hcoord
  rw [hrew]
  change Projectivization.map b.equivFun.symm.toLinearMap b.equivFun.symm.injective
      (projectiveSpaceByCoordinatesPointEquiv (k := k)
        (sigma := Fin (Module.finrank k E))
        (projectivePointOfVector
          (((glPointEquiv (Module.finrank k E) g :
            GL (Fin (Module.finrank k E)) k) :
            Matrix (Fin (Module.finrank k E)) (Fin (Module.finrank k E)) k).mulVec
              (b.equivFun v)) _)) = _
  rw [projectiveSpaceByCoordinatesPointEquiv_projectivePointOfVector]
  change Projectivization.mk k _ _ =
    Projectivization.mk k ((glPointEquivOf k E b g).1 v) _
  rw [Projectivization.mk_eq_mk_iff']
  refine ⟨1, ?_⟩
  simp only [one_smul]
  exact glPointEquivOf_apply_vector_coordinates (k := k) b g v

public theorem projectiveLinearMorphicAction_projectiveSpacePointEquivOf
    {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (g : Variety.Point (glVarietyOf k E))
    (x : Point (projectiveSpace k E)) :
    projectiveSpacePointEquivOf b
        ((projectiveLinearMorphicAction (k := k) E).toMulAction.smul g x) =
      Projectivization.map (glPointEquivOf k E b g).1
        (glPointEquivOf k E b g).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b x) := by
  induction hq : projectiveSpacePointEquivOf b x using Projectivization.ind with
  | h v hv =>
    have hx : x = projectivePointOfVector (b.equivFun v)
        (b.equivFun.map_ne_zero_iff.mpr hv) := by
      apply (projectiveSpacePointEquivOf b).injective
      rw [hq, projectiveSpacePointEquivOf_projectivePointOfVector]
    subst x
    exact projectiveLinearMorphicAction_projectiveSpacePointEquivOf_projectivePointOfVector
      (k := k) b g v hv

public noncomputable def projectiveLinearMorphicActionPullback
    {G : Variety k} [AlgebraicGroup G]
    (E : Type u) [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (φ : Theory.AlgebraicGroup.Morphism G (glVarietyOf k E)) :
    MorphicAction G (projectiveSpace k E) := by
  let A := projectiveLinearMorphicAction (k := k) E
  letI : MulAction (Variety.Point (glVarietyOf k E))
      (Point (projectiveSpace k E)) := A.toMulAction
  let rho : Variety.Point G →*
      Variety.Point (glVarietyOf k E) := φ.onPoints
  letI : MulAction (Variety.Point G) (Point (projectiveSpace k E)) :=
    MulAction.compHom _ rho
  let p : Morphism (prod (ofAffine G) (projectiveSpace k E))
      (prod (ofAffine (glVarietyOf k E)) (projectiveSpace k E)) :=
    Morphism.pair
      (Morphism.comp (fst (ofAffine G) (projectiveSpace k E))
        (ofAffine_morphism φ.toVariety))
      (snd (ofAffine G) (projectiveSpace k E))
  refine MorphicAction.mk inferInstance (Morphism.comp p A.actionMorphism) ?_
  intro g x
  have hfst :
      Morphism.comp (fst (ofAffine G) (projectiveSpace k E))
          (ofAffine_morphism φ.toVariety)
          (prodPoint ((affinePointEquiv G).symm g) x) =
        (affinePointEquiv (glVarietyOf k E)).symm (φ.onPoints g) := by
    apply (affinePointEquiv (glVarietyOf k E)).injective
    rw [Morphism.comp_apply_point]
    rw [fst_prodPoint]
    rw [affinePointEquiv_ofAffine_morphism]
    simp only [Equiv.apply_symm_apply]
    change φ.toVariety.toFun g = φ.toVariety.toFun g
    rfl
  have hsnd :
      (snd (ofAffine G) (projectiveSpace k E))
          (prodPoint ((affinePointEquiv G).symm g) x) = x := by
    rw [snd_prodPoint]
  rw [Morphism.comp_apply_point, Morphism.pair_apply, hfst, hsnd]
  exact A.actionMorphism_apply (φ.onPoints g) x

public theorem projectiveLinearMorphicActionPullback_projectiveSpacePointEquivOf
    {G : Variety k} [AlgebraicGroup G]
    {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (φ : Theory.AlgebraicGroup.Morphism G (glVarietyOf k E))
    (g : Variety.Point G) (x : Point (projectiveSpace k E)) :
    projectiveSpacePointEquivOf b
        ((projectiveLinearMorphicActionPullback (k := k) E φ).toMulAction.smul g x) =
      Projectivization.map (glPointEquivOf k E b (φ.onPoints g)).1
        (glPointEquivOf k E b (φ.onPoints g)).toLinearEquiv.injective
        (projectiveSpacePointEquivOf b x) := by
  let A := projectiveLinearMorphicAction (k := k) E
  letI : MulAction (Variety.Point (glVarietyOf k E))
      (Point (projectiveSpace k E)) := A.toMulAction
  let rho : Variety.Point G →*
      Variety.Point (glVarietyOf k E) := φ.onPoints
  letI : MulAction (Variety.Point G) (Point (projectiveSpace k E)) :=
    MulAction.compHom _ rho
  change projectiveSpacePointEquivOf b
      (A.toMulAction.smul (φ.onPoints g) x) = _
  exact projectiveLinearMorphicAction_projectiveSpacePointEquivOf
    (k := k) b (φ.onPoints g) x

public noncomputable def projectiveLinearOrbitMorphism
    {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (v : E) (hv : v ≠ 0) :
    Morphism (ofAffine (glVarietyOf k E)) (projectiveSpace k E) :=
  (projectiveLinearMorphicAction (k := k) E).orbitMorphismAt
    (projectivePointOfVector (b.equivFun v)
      (b.equivFun.map_ne_zero_iff.mpr hv))

public theorem projectiveLinearOrbitMorphism_apply
    {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (v : E) (hv : v ≠ 0) (g : Variety.Point (glVarietyOf k E)) :
    projectiveLinearOrbitMorphism (k := k) b v hv
        ((affinePointEquiv (glVarietyOf k E)).symm g) =
      (projectiveLinearMorphicAction (k := k) E).toMulAction.smul g
        (projectivePointOfVector (b.equivFun v)
          (b.equivFun.map_ne_zero_iff.mpr hv)) := by
  exact MorphicAction.orbitMorphismAt_apply _ _ _

public theorem projectiveLinearOrbitMorphism_projectiveSpacePointEquivOf_apply
    {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (b : Module.Basis (Fin (Module.finrank k E)) k E)
    (v : E) (hv : v ≠ 0) (g : Variety.Point (glVarietyOf k E)) :
    projectiveSpacePointEquivOf b
        (projectiveLinearOrbitMorphism (k := k) b v hv
          ((affinePointEquiv (glVarietyOf k E)).symm g)) =
      Projectivization.map (glPointEquivOf k E b g).1
        (glPointEquivOf k E b g).toLinearEquiv.injective
        (Projectivization.mk k v hv) := by
  rw [projectiveLinearOrbitMorphism_apply]
  exact projectiveLinearMorphicAction_projectiveSpacePointEquivOf_projectivePointOfVector
    (k := k) b g v hv

end Theory.AlgebraicGroup.Variety.Geometric
