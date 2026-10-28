module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Theory.AlgebraicGroup.Variety.ProjectivePoint

/-!
# The scheme-backed projective line and its affine charts

This module specializes the geometric projective-space construction to the standard projective
line `Proj k[X₀, X₁]`.  It identifies each degree-one basic open with the affine line
`Spec k[T]`, where `T` is the ratio of the other homogeneous coordinate by the coordinate that is
invertible on the chart.  The two basic opens cover projective space; consequently scheme maps
out of the projective line can be compared chartwise, and their overlap is the principal open
`D(T)`.  These are the chart and gluing interfaces needed to construct global regular actions.

The ring calculation is explicit.  Dehomogenization sends the selected coordinate to `1` and the
other coordinate to `T`; in the reverse direction, `T` is sent to the degree-zero localization
element `X_j / X_i`.  Homogeneity makes dehomogenization injective on this localization, giving
the required ring equivalence.  The carrier itself, reducedness, properness, projectivity, and
completeness come from `Variety.ProjectiveSpace` and Mathlib's projective-spectrum theory.

Although the algebraic-group development uses this construction over algebraically closed
fields, the carrier and chart calculation are valid over every field.  The construction follows
the standard Proj affine cover (Hartshorne, *Algebraic Geometry*, Chapter II, Sections 2 and 5);
over an algebraically closed field its rational points are the usual one-dimensional subspaces of
`k^2`, by the homogeneous-coordinate classification in `Variety.ProjectivePoint`.  No affine
structure is asserted for the projective line itself.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k]

/-- The standard total-degree grading on `k[X₀, X₁]`. -/
abbrev p1Grading := projectiveGrading k (Fin 2)

theorem coordinate_mem_p1Grading (i : Fin 2) :
    MvPolynomial.X i ∈ p1Grading (k := k) 1 :=
  MvPolynomial.isHomogeneous_X k i

/-- The other homogeneous coordinate of a projective-line chart. -/
def other : Fin 2 → Fin 2
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 0

@[simp] theorem other_zero : other 0 = 1 := rfl
@[simp] theorem other_one : other 1 = 0 := rfl

theorem other_ne (i : Fin 2) : other i ≠ i := by
  fin_cases i <;> decide

/-- The affine coordinate `X_(other i) / X_i` in the `i`th homogeneous localization. -/
def chartRatio (i : Fin 2) :
    HomogeneousLocalization.Away (p1Grading (k := k)) (MvPolynomial.X i) :=
  HomogeneousLocalization.Away.mk (p1Grading (k := k))
    (coordinate_mem_p1Grading (k := k) i) 1 (MvPolynomial.X (other i))
    (coordinate_mem_p1Grading (k := k) (other i))

/-- Dehomogenization on the `i`th chart: `X_i` is sent to `1` and the other coordinate to `T`. -/
def dehomogenize (i : Fin 2) : MvPolynomial (Fin 2) k →ₐ[k] Polynomial k :=
  MvPolynomial.aeval fun j => if j = i then 1 else Polynomial.X

@[simp] theorem dehomogenize_X_self (i : Fin 2) :
    dehomogenize (k := k) i (MvPolynomial.X i) = 1 := by
  simp [dehomogenize]

@[simp] theorem dehomogenize_X_other (i : Fin 2) :
    dehomogenize (k := k) i (MvPolynomial.X (other i)) = Polynomial.X := by
  simp [dehomogenize, other_ne]

set_option maxHeartbeats 800000 in
/-- Dehomogenization extended to the degree-zero homogeneous localization. -/
def chartToPolynomial (i : Fin 2) :
    HomogeneousLocalization.Away (p1Grading (k := k)) (MvPolynomial.X i) →+* Polynomial k := by
  let f : MvPolynomial (Fin 2) k →+* Polynomial k := (dehomogenize (k := k) i).toRingHom
  let g : Localization.Away (MvPolynomial.X i) →+* Polynomial k :=
    Localization.awayLift f (MvPolynomial.X i) (by
      rw [show f (MvPolynomial.X i) = 1 from dehomogenize_X_self (k := k) i]
      exact isUnit_one)
  let h : HomogeneousLocalization.Away
      (p1Grading (k := k)) (MvPolynomial.X i) →+*
      Localization.Away (MvPolynomial.X i) :=
    { toFun := HomogeneousLocalization.val
      map_one' := HomogeneousLocalization.val_one
      map_mul' := HomogeneousLocalization.val_mul
      map_zero' := HomogeneousLocalization.val_zero
      map_add' := HomogeneousLocalization.val_add }
  exact g.comp h

/-- The scalar map into the degree-zero homogeneous localization of the `i`th chart. -/
def scalarToChart (i : Fin 2) :
    k →+* HomogeneousLocalization.Away (p1Grading (k := k)) (MvPolynomial.X i) :=
  (HomogeneousLocalization.fromZeroRingHom
    (p1Grading (k := k)) (Submonoid.powers (MvPolynomial.X i))).comp
      (algebraMap k (p1Grading (k := k) 0))

/-- The reverse chart-coordinate map, sending `T` to `X_(other i) / X_i`. -/
def polynomialToChart (i : Fin 2) :
    Polynomial k →+* HomogeneousLocalization.Away
      (p1Grading (k := k)) (MvPolynomial.X i) :=
  Polynomial.eval₂RingHom (scalarToChart (k := k) i) (chartRatio (k := k) i)

@[simp] theorem chartToPolynomial_ratio (i : Fin 2) :
    chartToPolynomial (k := k) i (chartRatio (k := k) i) = Polynomial.X := by
  rw [show chartToPolynomial (k := k) i (chartRatio (k := k) i) =
      dehomogenize (k := k) i (MvPolynomial.X (other i)) * 1 ^ 1 by
    apply Localization.awayLift_mk
    simp]
  simp

set_option maxHeartbeats 800000 in
@[simp] theorem chartToPolynomial_scalar (i : Fin 2) (r : k) :
    chartToPolynomial (k := k) i (scalarToChart (k := k) i r) = Polynomial.C r := by
  rw [show scalarToChart (k := k) i r =
      HomogeneousLocalization.Away.mk (p1Grading (k := k))
        (MvPolynomial.isHomogeneous_X k i) 0 (MvPolynomial.C r)
        (by simp) by
      apply HomogeneousLocalization.val_injective (Submonoid.powers (MvPolynomial.X i))
      change Localization.mk (MvPolynomial.C r)
          (1 : Submonoid.powers (MvPolynomial.X i)) =
        Localization.mk (MvPolynomial.C r)
          (⟨MvPolynomial.X i ^ 0, ⟨0, rfl⟩⟩ : Submonoid.powers (MvPolynomial.X i))
      rfl]
  rw [show chartToPolynomial (k := k) i
        (HomogeneousLocalization.Away.mk (p1Grading (k := k))
          (MvPolynomial.isHomogeneous_X k i) 0 (MvPolynomial.C r)
          (by simp)) =
      dehomogenize (k := k) i (MvPolynomial.C r) * 1 ^ 0 by
    apply Localization.awayLift_mk
    simp]
  simp [dehomogenize]

theorem chartToPolynomial_comp_polynomialToChart (i : Fin 2) :
    (chartToPolynomial (k := k) i).comp (polynomialToChart (k := k) i) = RingHom.id _ := by
  apply Polynomial.ringHom_ext
  · intro r
    simp [polynomialToChart]
  · simp [polynomialToChart]

private def otherEquiv : Fin 2 ≃ Fin 2 where
  toFun := other
  invFun := other
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

private theorem dehomogenize_eq_zero_iff_of_isHomogeneous
    (i : Fin 2) (n : ℕ) (p : MvPolynomial (Fin 2) k) (hp : p.IsHomogeneous n) :
    dehomogenize (k := k) i p = 0 ↔ p = 0 := by
  constructor
  · intro h
    fin_cases i
    · let q := MvPolynomial.renameEquiv k (otherEquiv) p
      have hq : q.IsHomogeneous n := hp.rename_isHomogeneous
      have hqeval : MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial k)] q = 0 := by
        change MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial k)]
          (MvPolynomial.rename otherEquiv p) = 0
        rw [MvPolynomial.aeval_rename]
        convert h using 1
        have hmaps : MvPolynomial.aeval (![Polynomial.X, (1 : Polynomial k)] ∘ otherEquiv) =
            dehomogenize (k := k) 0 := by
          apply MvPolynomial.algHom_ext
          intro j
          fin_cases j <;> simp [dehomogenize, otherEquiv, other]
        exact DFunLike.congr_fun hmaps p
      have hzero : q = 0 := by
        simpa [hqeval] using
          (Polynomial.homogenize_eq_of_isHomogeneous hq hqeval).symm
      apply (MvPolynomial.renameEquiv k otherEquiv).injective
      simpa [q] using hzero
    · have heval : MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial k)] p = 0 := by
        convert h using 1
        have hmaps : MvPolynomial.aeval ![Polynomial.X, (1 : Polynomial k)] =
            dehomogenize (k := k) 1 := by
          apply MvPolynomial.algHom_ext
          intro j
          fin_cases j <;> simp [dehomogenize]
        exact DFunLike.congr_fun hmaps p
      simpa [heval] using
        (Polynomial.homogenize_eq_of_isHomogeneous hp heval).symm
  · rintro rfl
    simp

theorem chartToPolynomial_injective (i : Fin 2) :
    Function.Injective (chartToPolynomial (k := k) i) := by
  rw [RingHom.injective_iff_ker_eq_bot]
  ext x
  constructor
  · intro hx
    rw [RingHom.mem_ker] at hx
    obtain ⟨n, p, hp, rfl⟩ :=
      HomogeneousLocalization.Away.mk_surjective (p1Grading (k := k))
        (MvPolynomial.isHomogeneous_X k i) x
    rw [show chartToPolynomial (k := k) i
          (HomogeneousLocalization.Away.mk (p1Grading (k := k))
            (MvPolynomial.isHomogeneous_X k i) n p hp) =
        dehomogenize (k := k) i p * 1 ^ n by
      apply Localization.awayLift_mk
      simp] at hx
    simp only [one_pow, mul_one] at hx
    have hp' : p.IsHomogeneous n := by simpa using hp
    have hp0 : p = 0 :=
      (dehomogenize_eq_zero_iff_of_isHomogeneous (k := k) i n p hp').mp hx
    subst p
    exact HomogeneousLocalization.mk_eq_zero_of_num _ rfl
  · intro hx
    rw [Ideal.mem_bot] at hx
    subst x
    exact RingHom.mem_ker.mpr (map_zero _)

/-- The coordinate-ring equivalence between the `i`th standard chart and `k[T]`. -/
def chartCoordinateRingEquiv (i : Fin 2) :
    HomogeneousLocalization.Away (p1Grading (k := k)) (MvPolynomial.X i) ≃+*
      Polynomial k :=
  RingEquiv.ofBijective (chartToPolynomial (k := k) i) ⟨
    chartToPolynomial_injective (k := k) i,
    fun p => ⟨polynomialToChart (k := k) i p, by
      exact DFunLike.congr_fun
        (chartToPolynomial_comp_polynomialToChart (k := k) i) p⟩⟩

@[simp] theorem chartCoordinateRingEquiv_apply (i : Fin 2)
    (x : HomogeneousLocalization.Away (p1Grading (k := k)) (MvPolynomial.X i)) :
    chartCoordinateRingEquiv (k := k) i x = chartToPolynomial (k := k) i x :=
  rfl

@[simp] theorem chartCoordinateRingEquiv_symm_apply (i : Fin 2) (p : Polynomial k) :
    (chartCoordinateRingEquiv (k := k) i).symm p = polynomialToChart (k := k) i p := by
  apply (chartCoordinateRingEquiv (k := k) i).injective
  rw [RingEquiv.apply_symm_apply, chartCoordinateRingEquiv_apply]
  exact (DFunLike.congr_fun
    (chartToPolynomial_comp_polynomialToChart (k := k) i) p).symm

/-- The standard `Proj k[X₀,X₁]` carrier of the projective line. -/
abbrev projectiveLine (k : Type u) [Field k] : Geometric k :=
  projectiveSpaceByCoordinates k (Fin 2)

/-- Rational points of the projective line are nonzero pairs of homogeneous coordinates modulo
nonzero scalar multiplication. -/
noncomputable def projectiveLinePointEquiv [IsAlgClosed k] :
    Point (projectiveLine k) ≃ Projectivization k (Fin 2 → k) :=
  projectiveSpaceByCoordinatesPointEquiv (k := k) (sigma := Fin 2)

@[simp]
theorem projectiveLinePointEquiv_symm_mk [IsAlgClosed k]
    (v : Fin 2 → k) (hv : v ≠ 0) :
    (projectiveLinePointEquiv (k := k)).symm (Projectivization.mk k v hv) =
      projectivePointOfVector v hv :=
  projectiveSpaceByCoordinatesPointEquiv_symm_mk v hv

@[simp]
theorem projectiveLinePointEquiv_projectivePointOfVector [IsAlgClosed k]
    (v : Fin 2 → k) (hv : v ≠ 0) :
    projectiveLinePointEquiv (projectivePointOfVector v hv) =
      Projectivization.mk k v hv :=
  projectiveSpaceByCoordinatesPointEquiv_projectivePointOfVector v hv

/-- The standard chart on which the `i`th homogeneous coordinate is nonzero. -/
abbrev projectiveLineChartOpen (k : Type u) [Field k] (i : Fin 2) :
    (projectiveLine k).toScheme.Opens :=
  Proj.basicOpen (p1Grading (k := k)) (MvPolynomial.X i)

/-- The scheme underlying the `i`th projective-line chart. -/
abbrev projectiveLineChartScheme (k : Type u) [Field k] (i : Fin 2) : Scheme :=
  (projectiveLineChartOpen k i).toScheme

/-- The affine-line carrier `Spec k[T]`. -/
def polynomialAffineLine (k : Type u) [Field k] : Geometric k where
  toScheme := Spec (.of (Polynomial k))
  structureMap := Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
  finiteType := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  quasiCompact := by infer_instance
  separated := by infer_instance
  reduced := by infer_instance

/-- Each standard projective-line chart is canonically isomorphic to `Spec k[T]`; the coordinate
`T` is the ratio of the other homogeneous coordinate by the nonvanishing one. -/
def projectiveLineChartIsoAffineLine (i : Fin 2) :
    projectiveLineChartScheme k i ≅ (polynomialAffineLine k).toScheme :=
  Proj.basicOpenIsoSpec (p1Grading (k := k)) (MvPolynomial.X i)
      (coordinate_mem_p1Grading (k := k) i) Nat.zero_lt_one ≪≫
    Scheme.Spec.mapIso
      ((chartCoordinateRingEquiv (k := k) i).symm.toCommRingCatIso.op)

@[simp] theorem projectiveLineChartSpecIso_inv (i : Fin 2) :
    (Scheme.Spec.mapIso
      ((chartCoordinateRingEquiv (k := k) i).symm.toCommRingCatIso.op)).inv =
        Spec.map (CommRingCat.ofHom (chartToPolynomial (k := k) i)) := by
  rfl

/-- The standard affine chart inclusion into the projective line. -/
def projectiveLineChartInclusion (i : Fin 2) :
    Morphism (polynomialAffineLine k) (projectiveLine k) where
  hom := (Scheme.Spec.mapIso
      ((chartCoordinateRingEquiv (k := k) i).symm.toCommRingCatIso.op)).inv ≫
    Proj.awayι (p1Grading (k := k)) (MvPolynomial.X i)
      (coordinate_mem_p1Grading (k := k) i) Nat.zero_lt_one
  commutes := by
    let e := Scheme.Spec.mapIso
      ((chartCoordinateRingEquiv (k := k) i).symm.toCommRingCatIso.op)
    let j := Proj.awayι (p1Grading (k := k)) (MvPolynomial.X i)
      (coordinate_mem_p1Grading (k := k) i) Nat.zero_lt_one
    let q := Proj.toSpecZero (p1Grading (k := k))
    let z := Spec.map (CommRingCat.ofHom (algebraMap k (p1Grading (k := k) 0)))
    change (e.inv ≫ j) ≫ (q ≫ z) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k))
    calc
      (e.inv ≫ j) ≫ (q ≫ z) = e.inv ≫ ((j ≫ q) ≫ z) := by simp
      _ = e.inv ≫ (Spec.map
          (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
            (p1Grading (k := k)) (Submonoid.powers (MvPolynomial.X i)))) ≫ z) := by
        rw [show j ≫ q = Spec.map
            (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
              (p1Grading (k := k)) (Submonoid.powers (MvPolynomial.X i)))) by
          exact Proj.awayι_toSpecZero (p1Grading (k := k))
            (MvPolynomial.X i) (coordinate_mem_p1Grading (k := k) i) Nat.zero_lt_one]
      _ = Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) := by
        dsimp [e, z]
        change Spec.map (CommRingCat.ofHom (chartToPolynomial (k := k) i)) ≫
            Spec.map (CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom
              (p1Grading (k := k)) (Submonoid.powers (MvPolynomial.X i)))) ≫
              Spec.map (CommRingCat.ofHom (algebraMap k (p1Grading (k := k) 0))) = _
        rw [← Spec.map_comp, ← Spec.map_comp]
        congr 1
        apply CommRingCat.hom_ext
        apply RingHom.ext
        intro r
        exact chartToPolynomial_scalar (k := k) i r

instance projectiveLineChartInclusion_isOpenImmersion (i : Fin 2) :
    IsOpenImmersion (projectiveLineChartInclusion (k := k) i).hom := by
  change IsOpenImmersion
    ((Scheme.Spec.mapIso
      ((chartCoordinateRingEquiv (k := k) i).symm.toCommRingCatIso.op)).inv ≫
        Proj.awayι (p1Grading (k := k)) (MvPolynomial.X i)
          (coordinate_mem_p1Grading (k := k) i) Nat.zero_lt_one)
  exact IsOpenImmersion.comp _ _

@[simp] theorem projectiveLineChartInclusion_opensRange (i : Fin 2) :
    (projectiveLineChartInclusion (k := k) i).hom.opensRange =
      projectiveLineChartOpen k i := by
  change Scheme.Hom.opensRange
    ((Scheme.Spec.mapIso
      ((chartCoordinateRingEquiv (k := k) i).symm.toCommRingCatIso.op)).inv ≫
        Proj.awayι (p1Grading (k := k)) (MvPolynomial.X i)
          (coordinate_mem_p1Grading (k := k) i) Nat.zero_lt_one) = _
  rw [Scheme.Hom.opensRange_comp_of_isIso]
  exact Proj.opensRange_awayι (p1Grading (k := k)) (MvPolynomial.X i)
    (coordinate_mem_p1Grading (k := k) i) Nat.zero_lt_one

private theorem projectiveLine_adjoin_coordinates :
    Algebra.adjoin (p1Grading (k := k) 0)
      (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k)) = ⊤ := by
  apply top_unique
  intro p hp0
  clear hp0
  induction p using MvPolynomial.induction_on with
  | C r =>
      rw [show MvPolynomial.C r =
          algebraMap (p1Grading (k := k) 0) (MvPolynomial (Fin 2) k)
            ⟨MvPolynomial.C r, by simp⟩ by
        rfl]
      exact (Algebra.adjoin (p1Grading (k := k) 0)
        (Set.range (MvPolynomial.X : Fin 2 → MvPolynomial (Fin 2) k))).algebraMap_mem _
  | add p q hp hq => exact add_mem hp hq
  | mul_X p i hp =>
      exact mul_mem hp (Algebra.subset_adjoin ⟨i, rfl⟩)

/-- The two standard affine charts cover the projective line. -/
theorem iSup_projectiveLineChartOpen_eq_top :
    ⨆ i : Fin 2, projectiveLineChartOpen k i = ⊤ := by
  exact Proj.iSup_basicOpen_eq_top' (p1Grading (k := k)) MvPolynomial.X
    (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X k i⟩)
    projectiveLine_adjoin_coordinates

/-- The standard two-chart open cover, used to glue and compare projective-line morphisms. -/
def projectiveLineChartCover : (projectiveLine k).toScheme.OpenCover :=
  (projectiveLine k).toScheme.openCoverOfIsOpenCover
    (projectiveLineChartOpen k) iSup_projectiveLineChartOpen_eq_top

/-- Scheme morphisms out of the projective line are determined on its two affine charts. -/
theorem projectiveLine_hom_ext {Y : Scheme}
    (f g : (projectiveLine k).toScheme ⟶ Y)
    (h : ∀ i : Fin 2, (projectiveLineChartOpen k i).ι ≫ f =
      (projectiveLineChartOpen k i).ι ≫ g) : f = g := by
  apply (projectiveLineChartCover (k := k)).hom_ext
  intro i
  change (projectiveLineChartOpen k i).ι ≫ f =
    (projectiveLineChartOpen k i).ι ≫ g
  exact h i

/-- The overlap of the `i`th chart with the other standard chart is the principal open where the
ratio coordinate is nonzero. -/
theorem projectiveLineChart_preimage_other (i : Fin 2) :
    (projectiveLineChartInclusion (k := k) i).hom ⁻¹ᵁ projectiveLineChartOpen k (other i) =
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k) := by
  rw [show (projectiveLineChartInclusion (k := k) i).hom =
      (Scheme.Spec.mapIso
        ((chartCoordinateRingEquiv (k := k) i).symm.toCommRingCatIso.op)).inv ≫
        Proj.awayι (p1Grading (k := k)) (MvPolynomial.X i)
          (coordinate_mem_p1Grading (k := k) i) Nat.zero_lt_one by rfl]
  change (Scheme.Spec.mapIso
      ((chartCoordinateRingEquiv (k := k) i).symm.toCommRingCatIso.op)).inv ⁻¹ᵁ
        ((Proj.awayι (p1Grading (k := k)) (MvPolynomial.X i)
          (coordinate_mem_p1Grading (k := k) i) Nat.zero_lt_one) ⁻¹ᵁ
            projectiveLineChartOpen k (other i)) = _
  rw [Proj.awayι_preimage_basicOpen
    (p1Grading (k := k)) (coordinate_mem_p1Grading (k := k) i) Nat.zero_lt_one
      (coordinate_mem_p1Grading (k := k) (other i)) Nat.zero_lt_one]
  rw [projectiveLineChartSpecIso_inv]
  rw [SpecMap_preimage_basicOpen]
  have helem : HomogeneousLocalization.Away.isLocalizationElem
      (coordinate_mem_p1Grading (k := k) i)
        (coordinate_mem_p1Grading (k := k) (other i)) = chartRatio (k := k) i := by
    simp [HomogeneousLocalization.Away.isLocalizationElem, chartRatio]
  rw [helem]
  exact congrArg PrimeSpectrum.basicOpen (chartToPolynomial_ratio (k := k) i)

/-- The projective line is projective. -/
theorem projectiveLine_isProjective : IsProjective (projectiveLine k) :=
  projectiveSpaceByCoordinates_isProjective k (Fin 2)

/-- The projective line is proper over its ground field. -/
theorem projectiveLine_isProper : IsProper (projectiveLine k).structureMap :=
  projectiveSpaceByCoordinates_isProper k (Fin 2)

/-- The projective line is complete. -/
theorem projectiveLine_isComplete : IsComplete (projectiveLine k) :=
  projectiveSpaceByCoordinates_isComplete k (Fin 2)

end Theory.AlgebraicGroup.Variety.Geometric
