module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Theory.AlgebraicGroup.Variety.ProjectiveSpace

/-!
# Rational points of projective space

This module identifies the `k`-rational points of the standard scheme-theoretic projective space
with nonzero homogeneous coordinate vectors modulo scalar multiplication.  A vector defines its
point through evaluation of the homogeneous coordinate ring and `Proj.fromOfGlobalSections`.
Conversely, a rational point is lifted to an affine chart where one coordinate is nonzero; the
closed point of `Spec k` then evaluates the degree-zero fractions `X_j / X_i` and supplies a
normalized coordinate vector.  Equality of the resulting homogeneous prime ideals proves that
these constructions are inverse.

The final equivalence for a finite-dimensional vector space transports this coordinate result
along a chosen basis.  This is the scheme-theoretic form of the homogeneous-coordinate
description in A. Borel, *Linear Algebraic Groups* (`Bor1`), Chapter AG, Section 7.2.  The
public membership criterion below records the Proj closed-point calculation needed by regular
linear substitutions.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped LinearAlgebra.Projectivization

namespace Theory.AlgebraicGroup.Variety.Geometric

universe u

variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable def projectivePointGlobalSections
    {sigma : Type} (v : sigma → k) :
    projectiveCoordinateRing k sigma →+* Γ(Spec (.of k), ⊤) :=
  (Scheme.ΓSpecIso (.of k)).inv.hom.comp
    (MvPolynomial.eval₂Hom (RingHom.id k) v)

omit [IsAlgClosed k] in
private theorem projectiveX_mem {sigma : Type} (i : sigma) :
    MvPolynomial.X i ∈ projectiveGrading k sigma 1 :=
  MvPolynomial.isHomogeneous_X k i

omit [IsAlgClosed k] in
theorem projectivePointGlobalSections_irrelevant
    {sigma : Type} [Finite sigma] (v : sigma → k) (hv : v ≠ 0) :
    Ideal.map (projectivePointGlobalSections v)
      (HomogeneousIdeal.irrelevant (projectiveGrading k sigma)).toIdeal = ⊤ := by
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    simpa [Function.ne_iff] using hv
  have hXi : MvPolynomial.X i ∈
      (HomogeneousIdeal.irrelevant (projectiveGrading k sigma)).toIdeal := by
    change MvPolynomial.X i ∈
      HomogeneousIdeal.irrelevant (projectiveGrading k sigma)
    rw [HomogeneousIdeal.mem_irrelevant_iff]
    exact DirectSum.decompose_of_mem_ne _
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr
        (MvPolynomial.isHomogeneous_X k i)) one_ne_zero
  refine Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem (projectivePointGlobalSections v) hXi) ?_
  simpa [projectivePointGlobalSections] using
    (IsUnit.map (Scheme.ΓSpecIso (.of k)).inv.hom
      (isUnit_iff_ne_zero.mpr hi))

omit [IsAlgClosed k] in
theorem projectivePointGlobalSections_overBase
    {sigma : Type} [Finite sigma] (v : sigma → k) (hv : v ≠ 0) :
    Proj.fromOfGlobalSections (projectiveGrading k sigma)
        (projectivePointGlobalSections v)
        (projectivePointGlobalSections_irrelevant v hv) ≫
      (projectiveSpaceByCoordinates k sigma).structureMap =
        𝟙 (Spec (.of k)) := by
  change Proj.fromOfGlobalSections (projectiveGrading k sigma)
      (projectivePointGlobalSections v)
      (projectivePointGlobalSections_irrelevant v hv) ≫
    (Proj.toSpecZero (projectiveGrading k sigma) ≫
      Spec.map (CommRingCat.ofHom
        (algebraMap k (projectiveGrading k sigma 0)))) =
      𝟙 (Spec (.of k))
  rw [← Category.assoc, Proj.fromOfGlobalSections_toSpecZero,
    ← SpecMap_ΓSpecIso_hom]
  simp only [← Spec.map_comp, CommRingCat.ofHom_comp]
  convert Spec.map_id (CommRingCat.of k) using 1
  rw [Spec.map_injective.eq_iff]
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  simp [projectivePointGlobalSections]

/-- The rational point of coordinate projective space represented by a nonzero vector. -/
noncomputable def projectivePointOfVector
    {sigma : Type} [Finite sigma] (v : sigma → k) (hv : v ≠ 0) :
    Point (projectiveSpaceByCoordinates k sigma) where
  val := Proj.fromOfGlobalSections (projectiveGrading k sigma)
    (projectivePointGlobalSections v)
    (projectivePointGlobalSections_irrelevant v hv)
  property := projectivePointGlobalSections_overBase v hv

omit [IsAlgClosed k] in
private theorem projectiveCoordinate_adjoin_eq_top {sigma : Type} :
    Algebra.adjoin (projectiveGrading k sigma 0)
      (Set.range (MvPolynomial.X : sigma → MvPolynomial sigma k)) = ⊤ := by
  let S := Algebra.adjoin (projectiveGrading k sigma 0)
    (Set.range (MvPolynomial.X : sigma → MvPolynomial sigma k))
  apply top_unique
  intro p hp
  clear hp
  change p ∈ S
  induction p using MvPolynomial.induction_on with
  | C r =>
      simpa using S.algebraMap_mem
        ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C sigma r⟩
  | add p q hp hq => exact S.add_mem hp hq
  | mul_X p i hp =>
      exact S.mul_mem hp (Algebra.subset_adjoin (Set.mem_range_self i))

omit [IsAlgClosed k] in
private theorem projectivePoint_exists_chart
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    ∃ i : sigma,
      x.1 (IsLocalRing.closedPoint k) ∈
        Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i) := by
  have hx : x.1 (IsLocalRing.closedPoint k) ∈
      (⊤ : (Proj (projectiveGrading k sigma)).Opens) := trivial
  rw [← Proj.iSup_basicOpen_eq_top'
    (projectiveGrading k sigma) (MvPolynomial.X : sigma → MvPolynomial sigma k)
    (fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X k i⟩)
    projectiveCoordinate_adjoin_eq_top] at hx
  exact TopologicalSpace.Opens.mem_iSup.mp hx

private noncomputable def projectivePointChartIndex
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) : sigma :=
  (projectivePoint_exists_chart x).choose

omit [IsAlgClosed k] in
private theorem projectivePointChartIndex_mem
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    x.1 (IsLocalRing.closedPoint k) ∈
      Proj.basicOpen (projectiveGrading k sigma)
        (MvPolynomial.X (projectivePointChartIndex x)) :=
  (projectivePoint_exists_chart x).choose_spec

private noncomputable def projectivePointChartLift
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    Spec (.of k) ⟶ Spec (.of <|
      HomogeneousLocalization.Away (projectiveGrading k sigma)
        (MvPolynomial.X (projectivePointChartIndex x))) :=
  by
    let x' : Spec (.of k) ⟶ Proj (projectiveGrading k sigma) := x.val
    have h : Set.range x' ⊆
        (Proj.awayι (projectiveGrading k sigma)
          (MvPolynomial.X (projectivePointChartIndex x))
          (projectiveX_mem (k := k) (projectivePointChartIndex x))
          Nat.zero_lt_one).opensRange := by
      rw [Proj.opensRange_awayι]
      rintro _ ⟨z, rfl⟩
      obtain rfl := Subsingleton.elim z (IsLocalRing.closedPoint k)
      exact projectivePointChartIndex_mem x
    exact IsOpenImmersion.lift
      (Proj.basicOpen (projectiveGrading k sigma)
        (MvPolynomial.X (projectivePointChartIndex x))).ι x'
        (by
          simpa only [Proj.opensRange_awayι, Scheme.Opens.range_ι] using h) ≫
      (Proj.basicOpenIsoSpec (projectiveGrading k sigma)
        (MvPolynomial.X (projectivePointChartIndex x))
        (projectiveX_mem (k := k) (projectivePointChartIndex x)) Nat.zero_lt_one).hom

omit [IsAlgClosed k] in
private theorem projectivePointChartLift_fac
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    projectivePointChartLift x ≫
        Proj.awayι (projectiveGrading k sigma)
          (MvPolynomial.X (projectivePointChartIndex x))
          (projectiveX_mem (k := k) (projectivePointChartIndex x))
          Nat.zero_lt_one = x.val := by
  simp only [projectivePointChartLift, Proj.awayι, Category.assoc,
    Iso.hom_inv_id_assoc]
  exact IsOpenImmersion.lift_fac _ _ _

private noncomputable def projectivePointChartCoordinates
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) : sigma → k :=
  fun j ↦ (Spec.preimage (projectivePointChartLift x)).hom
    (HomogeneousLocalization.Away.mk (projectiveGrading k sigma)
      (projectiveX_mem (k := k) (projectivePointChartIndex x)) 1
      (MvPolynomial.X j) (projectiveX_mem (k := k) j))

omit [IsAlgClosed k] in
private theorem away_mk_X_self
    {sigma : Type} [Finite sigma] (i : sigma) :
    HomogeneousLocalization.Away.mk (projectiveGrading k sigma)
        (projectiveX_mem (k := k) i) 1
        (MvPolynomial.X i) (projectiveX_mem (k := k) i) = 1 := by
  apply HomogeneousLocalization.val_injective
  have hpow : MvPolynomial.X i ∈ Submonoid.powers (MvPolynomial.X i) :=
    Submonoid.mem_powers (MvPolynomial.X i : MvPolynomial sigma k)
  simp only [HomogeneousLocalization.Away.val_mk, pow_one]
  rw [HomogeneousLocalization.val_one]
  simpa only [Localization.mk_eq_mk'] using
    (IsLocalization.mk'_self
      (Localization.Away (MvPolynomial.X i : MvPolynomial sigma k))
      hpow)

omit [IsAlgClosed k] in
private theorem projectivePointChartCoordinates_self
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    projectivePointChartCoordinates x (projectivePointChartIndex x) = 1 := by
  simp [projectivePointChartCoordinates, away_mk_X_self]

omit [IsAlgClosed k] in
private theorem projectivePointChartCoordinates_ne_zero
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    projectivePointChartCoordinates x ≠ 0 := by
  intro h
  have := congr_fun h (projectivePointChartIndex x)
  rw [projectivePointChartCoordinates_self] at this
  exact one_ne_zero this

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency.types false in
private theorem closedPoint_mem_basicOpen_iff (r : k) :
    (IsLocalRing.closedPoint k : (Spec (.of k)).carrier) ∈
        (Spec (.of k)).basicOpen ((Scheme.ΓSpecIso (.of k)).inv r) ↔ r ≠ 0 := by
  rw [basicOpen_eq_of_affine]
  change r ∉ (IsLocalRing.closedPoint k).asIdeal ↔ r ≠ 0
  have hclosed : (IsLocalRing.closedPoint k).asIdeal = (⊥ : Ideal k) :=
    (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
  rw [hclosed]
  simp

private theorem eval₂Hom_smul_of_isHomogeneous
    {R S sigma : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (p : MvPolynomial sigma R) (n : ℕ)
    (hp : p.IsHomogeneous n) (a : S) (v : sigma → S) :
    MvPolynomial.eval₂Hom f (a • v) p =
      a ^ n * MvPolynomial.eval₂Hom f v p := by
  classical
  rw [← p.support_sum_monomial_coeff]
  simp only [map_sum, MvPolynomial.eval₂Hom_monomial, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [hp.degree_eq_sum_deg_support hd]
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finsupp.prod]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
/-- A homogeneous coordinate polynomial vanishes at the projective point represented by
`v` exactly when its evaluation at `v` vanishes. -/
public theorem projectivePointOfVector_mem_iff
    {sigma : Type} [Finite sigma] (v : sigma → k) (hv : v ≠ 0)
    {p : MvPolynomial sigma k} {n : ℕ}
    (hp : p ∈ projectiveGrading k sigma n) :
    p ∈ ((projectivePointOfVector v hv).1 (IsLocalRing.closedPoint k)).asHomogeneousIdeal ↔
      MvPolynomial.eval₂Hom (RingHom.id k) v p = 0 := by
  by_cases hn : n = 0
  · subst n
    let y : Proj (projectiveGrading k sigma) :=
      (projectivePointOfVector v hv).1 (IsLocalRing.closedPoint k)
    change p ∈ y.asHomogeneousIdeal ↔ _
    change p ∈ MvPolynomial.homogeneousSubmodule sigma k 0 at hp
    rw [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] at hp
    obtain ⟨r, rfl⟩ := hp
    simp only [MvPolynomial.algebraMap_eq, MvPolynomial.eval₂Hom_C,
      RingHom.id_apply]
    change MvPolynomial.C r ∈ y.asHomogeneousIdeal ↔ r = 0
    constructor
    · intro hr
      by_contra hr0
      exact y.2.ne_top (y.asHomogeneousIdeal.toIdeal.eq_top_of_isUnit_mem hr
        ((isUnit_iff_ne_zero.mpr hr0).map
          (MvPolynomial.C : k →+* MvPolynomial sigma k)))
    · rintro rfl
      simp
  · rw [← not_iff_not]
    change p ∉ _ ↔ MvPolynomial.eval₂Hom (RingHom.id k) v p ≠ 0
    rw [← Proj.mem_basicOpen (projectiveGrading k sigma) p
      ((projectivePointOfVector v hv).1 (IsLocalRing.closedPoint k))]
    let y : Proj (projectiveGrading k sigma) :=
      (projectivePointOfVector v hv).1 (IsLocalRing.closedPoint k)
    change y ∈ Proj.basicOpen (projectiveGrading k sigma) p ↔ _
    dsimp only [y, projectivePointOfVector]
    rw [← SetLike.mem_coe, ← Set.mem_preimage,
      ← TopologicalSpace.Opens.map_coe,
      Proj.fromOfGlobalSections_preimage_basicOpen
        (projectiveGrading k sigma) (projectivePointGlobalSections v)
        (projectivePointGlobalSections_irrelevant v hv) (Nat.pos_of_ne_zero hn) hp]
    simpa only [SetLike.mem_coe, projectivePointGlobalSections,
      RingHom.comp_apply, RingHom.id_apply] using
      closedPoint_mem_basicOpen_iff
        (MvPolynomial.eval₂Hom (RingHom.id k) v p)

/-- Multiplying all homogeneous coordinates by a nonzero scalar does not change the point. -/
theorem projectivePointOfVector_smul
    {sigma : Type} [Finite sigma] (v : sigma → k) (hv : v ≠ 0)
    (a : k) (ha : a ≠ 0) :
    projectivePointOfVector (a • v) (smul_ne_zero ha hv) =
      projectivePointOfVector v hv := by
  apply Subtype.ext
  apply ext_of_apply_closedPoint_eq
    (projectiveSpaceByCoordinates k sigma).structureMap
    (projectivePointOfVector (a • v) (smul_ne_zero ha hv)).property
    (projectivePointOfVector v hv).property
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  rw [projectivePointOfVector_mem_iff (a • v) (smul_ne_zero ha hv) hp,
    projectivePointOfVector_mem_iff v hv hp,
    eval₂Hom_smul_of_isHomogeneous (R := k) (S := k)
      (RingHom.id k) p n hp]
  simp [ha]

omit [IsAlgClosed k] in
private theorem away_eval_coordinates
    {sigma : Type} [Finite sigma] (i : sigma)
    (p : MvPolynomial sigma k) (n : ℕ)
    (hp : p ∈ projectiveGrading k sigma n) :
    MvPolynomial.eval₂Hom
        ((HomogeneousLocalization.fromZeroRingHom
          (projectiveGrading k sigma) _).comp
            (algebraMap k (projectiveGrading k sigma 0)))
        (fun j ↦ HomogeneousLocalization.Away.mk
          (projectiveGrading k sigma) (projectiveX_mem (k := k) i) 1
          (MvPolynomial.X j) (projectiveX_mem (k := k) j)) p =
      HomogeneousLocalization.Away.mk
        (projectiveGrading k sigma) (projectiveX_mem (k := k) i) n p
          (by simpa using hp) := by
  classical
  let L := Localization.Away (MvPolynomial.X i : MvPolynomial sigma k)
  let A₀ := HomogeneousLocalization.Away
    (projectiveGrading k sigma) (MvPolynomial.X i)
  let valHom : A₀ →+* L := algebraMap _ _
  let polynomialMap : MvPolynomial sigma k →+* L := algebraMap _ _
  let inverseCoordinate : L := IsLocalization.mk' L 1
    ⟨MvPolynomial.X i,
      Submonoid.mem_powers (MvPolynomial.X i : MvPolynomial sigma k)⟩
  have hcoeff : valHom.comp
        ((HomogeneousLocalization.fromZeroRingHom
          (projectiveGrading k sigma) _).comp
            (algebraMap k (projectiveGrading k sigma 0))) =
      polynomialMap.comp MvPolynomial.C := by
    ext r
    change Localization.mk (MvPolynomial.C r) ⟨1, Submonoid.one_mem _⟩ =
      algebraMap (MvPolynomial sigma k) L (MvPolynomial.C r)
    rw [Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul]
    simp [L]
  have hcoordinate (j : sigma) :
      valHom (HomogeneousLocalization.Away.mk
        (projectiveGrading k sigma) (projectiveX_mem (k := k) i) 1
        (MvPolynomial.X j) (projectiveX_mem (k := k) j)) =
        inverseCoordinate * polynomialMap (MvPolynomial.X j) := by
    dsimp only [valHom, A₀]
    rw [HomogeneousLocalization.algebraMap_apply,
      HomogeneousLocalization.Away.val_mk]
    rw [Localization.mk_eq_mk']
    simpa only [inverseCoordinate, polynomialMap, pow_one, mul_comm] using
      (IsLocalization.mk'_eq_mul_mk'_one
        (S := L) (MvPolynomial.X j)
          ⟨MvPolynomial.X i,
            Submonoid.mem_powers (MvPolynomial.X i : MvPolynomial sigma k)⟩)
  apply HomogeneousLocalization.val_injective
  conv_lhs => rw [← HomogeneousLocalization.algebraMap_apply]
  conv_rhs => rw [← HomogeneousLocalization.algebraMap_apply]
  change valHom (MvPolynomial.eval₂Hom _ _ p) = valHom _
  rw [MvPolynomial.map_eval₂Hom, hcoeff]
  simp_rw [hcoordinate]
  rw [show (fun j ↦ inverseCoordinate * polynomialMap (MvPolynomial.X j)) =
      inverseCoordinate • (fun j ↦ polynomialMap (MvPolynomial.X j)) by
    ext
    simp]
  rw [eval₂Hom_smul_of_isHomogeneous
    (R := k) (S := L) (polynomialMap.comp MvPolynomial.C) p n hp]
  have heval : MvPolynomial.eval₂Hom
      (polynomialMap.comp MvPolynomial.C)
      (fun j ↦ polynomialMap (MvPolynomial.X j)) p = polynomialMap p := by
    exact RingHom.congr_fun (by ext <;> simp) p
  rw [heval]
  dsimp only [valHom, A₀]
  rw [HomogeneousLocalization.algebraMap_apply,
    HomogeneousLocalization.Away.val_mk]
  rw [Localization.mk_eq_mk']
  change inverseCoordinate ^ n * polynomialMap p =
    IsLocalization.mk' L p ⟨MvPolynomial.X i ^ n,
      (show MvPolynomial.X i ^ n ∈
        Submonoid.powers (MvPolynomial.X i : MvPolynomial sigma k) from ⟨n, rfl⟩)⟩
  rw [← IsLocalization.mk'_pow, one_pow, mul_comm,
    IsLocalization.mul_mk'_eq_mk'_of_mul]
  congr 1
  simp

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
private theorem projectivePointChartLift_overBase
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    projectivePointChartLift x ≫
        Spec.map (CommRingCat.ofHom <|
          (HomogeneousLocalization.fromZeroRingHom
            (projectiveGrading k sigma) _).comp
              (algebraMap k (projectiveGrading k sigma 0))) =
      𝟙 (Spec (.of k)) := by
  have haway :
      Proj.awayι (projectiveGrading k sigma)
          (MvPolynomial.X (projectivePointChartIndex x))
          (projectiveX_mem (k := k) (projectivePointChartIndex x))
          Nat.zero_lt_one ≫
        (Proj.toSpecZero (projectiveGrading k sigma) ≫
          Spec.map (CommRingCat.ofHom
            (algebraMap k (projectiveGrading k sigma 0)))) =
      Spec.map (CommRingCat.ofHom <|
        (HomogeneousLocalization.fromZeroRingHom
          (projectiveGrading k sigma) _).comp
            (algebraMap k (projectiveGrading k sigma 0))) := by
    rw [← Category.assoc, Proj.awayι_toSpecZero,
      ← Spec.map_comp, CommRingCat.ofHom_comp]
  rw [← haway, ← Category.assoc, projectivePointChartLift_fac]
  exact x.property

omit [IsAlgClosed k] in
private theorem projectivePointChartHom_comp_coefficients
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    (Spec.preimage (projectivePointChartLift x)).hom.comp
        ((HomogeneousLocalization.fromZeroRingHom
          (projectiveGrading k sigma) _).comp
            (algebraMap k (projectiveGrading k sigma 0))) =
      RingHom.id k := by
  have h := congrArg Spec.preimage (projectivePointChartLift_overBase x)
  have h' := congrArg CommRingCat.Hom.hom h
  simp only [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id,
    CommRingCat.hom_comp] at h'
  exact h'

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
private theorem projectivePointChartLift_closedPoint
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    projectivePointChartLift x (IsLocalRing.closedPoint k) =
      (ProjectiveSpectrum.Proj.toSpec (projectiveGrading k sigma)
        (MvPolynomial.X (projectivePointChartIndex x))).base
          ⟨x.1 (IsLocalRing.closedPoint k), projectivePointChartIndex_mem x⟩ := by
  let y : (Proj.basicOpen (projectiveGrading k sigma)
      (MvPolynomial.X (projectivePointChartIndex x))).toScheme :=
    ⟨x.1 (IsLocalRing.closedPoint k), projectivePointChartIndex_mem x⟩
  have hRange : Set.range x.val ⊆
      Set.range (Proj.basicOpen (projectiveGrading k sigma)
        (MvPolynomial.X (projectivePointChartIndex x))).ι := by
    rintro _ ⟨z, rfl⟩
    obtain rfl := Subsingleton.elim z (IsLocalRing.closedPoint k)
    exact ⟨y, rfl⟩
  have hlift :
      (IsOpenImmersion.lift
        (Proj.basicOpen (projectiveGrading k sigma)
          (MvPolynomial.X (projectivePointChartIndex x))).ι x.val hRange)
          (IsLocalRing.closedPoint k) = y := by
    apply Subtype.ext
    exact congrArg (fun f ↦ f (IsLocalRing.closedPoint k))
      (IsOpenImmersion.lift_fac
        (Proj.basicOpen (projectiveGrading k sigma)
          (MvPolynomial.X (projectivePointChartIndex x))).ι x.val hRange)
  change (Proj.basicOpenIsoSpec (projectiveGrading k sigma)
    (MvPolynomial.X (projectivePointChartIndex x))
      (projectiveX_mem (k := k) (projectivePointChartIndex x))
      Nat.zero_lt_one).hom.base
      ((IsOpenImmersion.lift _ x.val _) (IsLocalRing.closedPoint k)) = _
  rw [hlift]
  rfl

omit [IsAlgClosed k] in
private theorem projectivePointChartLift_mem_iff
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma))
    (z : HomogeneousLocalization.Away (projectiveGrading k sigma)
      (MvPolynomial.X (projectivePointChartIndex x))) :
    z ∈ (projectivePointChartLift x (IsLocalRing.closedPoint k)).asIdeal ↔
      (Spec.preimage (projectivePointChartLift x)).hom z = 0 := by
  have hmap := congrArg (fun f ↦ f (IsLocalRing.closedPoint k))
    (Spec.map_preimage (projectivePointChartLift x))
  rw [← hmap]
  change z ∈ (PrimeSpectrum.comap
    (Spec.preimage (projectivePointChartLift x)).hom
      (IsLocalRing.closedPoint k)).asIdeal ↔ _
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap]
  have hclosed : (IsLocalRing.closedPoint k).asIdeal = (⊥ : Ideal k) :=
    (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
  rw [hclosed]
  exact Ideal.mem_bot

omit [IsAlgClosed k] in
set_option backward.isDefEq.respectTransparency false in
private theorem projectivePoint_mem_iff_chart_eval
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma))
    {p : MvPolynomial sigma k} {n : ℕ}
    (hp : p ∈ projectiveGrading k sigma n) :
    p ∈ (x.1 (IsLocalRing.closedPoint k)).asHomogeneousIdeal ↔
      MvPolynomial.eval₂Hom (RingHom.id k)
        (projectivePointChartCoordinates x) p = 0 := by
  let y : (Proj.basicOpen (projectiveGrading k sigma)
      (MvPolynomial.X (projectivePointChartIndex x))).toScheme :=
    ⟨x.1 (IsLocalRing.closedPoint k), projectivePointChartIndex_mem x⟩
  let z : HomogeneousLocalization.NumDenSameDeg
      (projectiveGrading k sigma)
      (Submonoid.powers (MvPolynomial.X (projectivePointChartIndex x))) :=
    { deg := n
      num := ⟨p, hp⟩
      den := ⟨MvPolynomial.X (projectivePointChartIndex x) ^ n,
        MvPolynomial.isHomogeneous_X_pow _ _⟩
      den_mem := ⟨n, rfl⟩ }
  have hz : HomogeneousLocalization.mk z ∈
        (projectivePointChartLift x (IsLocalRing.closedPoint k)).asIdeal ↔
      p ∈ (x.1 (IsLocalRing.closedPoint k)).asHomogeneousIdeal := by
    rw [projectivePointChartLift_closedPoint]
    exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply
      (projectiveGrading k sigma) y z
  have hzmk : HomogeneousLocalization.mk z =
      HomogeneousLocalization.Away.mk (projectiveGrading k sigma)
        (projectiveX_mem (k := k) (projectivePointChartIndex x)) n p
          (by simpa using hp) := by
    apply HomogeneousLocalization.val_injective
    rfl
  rw [← hz, projectivePointChartLift_mem_iff]
  rw [hzmk]
  rw [← away_eval_coordinates (projectivePointChartIndex x) p n hp,
    MvPolynomial.map_eval₂Hom, projectivePointChartHom_comp_coefficients]
  rfl

private theorem projectivePointOfVector_chartCoordinates
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    projectivePointOfVector (projectivePointChartCoordinates x)
        (projectivePointChartCoordinates_ne_zero x) = x := by
  apply Subtype.ext
  apply ext_of_apply_closedPoint_eq
    (projectiveSpaceByCoordinates k sigma).structureMap
    (projectivePointOfVector (projectivePointChartCoordinates x)
      (projectivePointChartCoordinates_ne_zero x)).property
    x.property
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  rw [projectivePointOfVector_mem_iff _ _ hp,
    projectivePoint_mem_iff_chart_eval x hp]

theorem projectivePointOfVector_eq_iff_mk_eq
    {sigma : Type} [Finite sigma]
    (v w : sigma → k) (hv : v ≠ 0) (hw : w ≠ 0) :
    projectivePointOfVector v hv = projectivePointOfVector w hw ↔
      Projectivization.mk k v hv = Projectivization.mk k w hw := by
  constructor
  · intro h
    have hclosed := congrArg
      (fun z : Point (projectiveSpaceByCoordinates k sigma) ↦
        z.1 (IsLocalRing.closedPoint k)) h
    obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
      simpa [Function.ne_iff] using hv
    have hwi : w i ≠ 0 := by
      intro hwi
      have hmemw : MvPolynomial.X i ∈
          ((projectivePointOfVector w hw).1
            (IsLocalRing.closedPoint k)).asHomogeneousIdeal :=
        (projectivePointOfVector_mem_iff w hw
          (projectiveX_mem (k := k) i)).2 (by simp [hwi])
      have hmemv : MvPolynomial.X i ∈
          ((projectivePointOfVector v hv).1
            (IsLocalRing.closedPoint k)).asHomogeneousIdeal := by
        rw [hclosed]
        exact hmemw
      exact hi (by
        simpa using (projectivePointOfVector_mem_iff v hv
          (projectiveX_mem (k := k) i)).1 hmemv)
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨v i / w i, ?_⟩
    funext j
    let p : MvPolynomial sigma k :=
      MvPolynomial.C (w i) * MvPolynomial.X j -
        MvPolynomial.C (w j) * MvPolynomial.X i
    have hp : p ∈ projectiveGrading k sigma 1 :=
      (MvPolynomial.isHomogeneous_C_mul_X (w i) j).sub
        (MvPolynomial.isHomogeneous_C_mul_X (w j) i)
    have hmemw : p ∈ ((projectivePointOfVector w hw).1
        (IsLocalRing.closedPoint k)).asHomogeneousIdeal :=
      (projectivePointOfVector_mem_iff w hw hp).2 (by
        simp [p]
        ring)
    have hmemv : p ∈ ((projectivePointOfVector v hv).1
        (IsLocalRing.closedPoint k)).asHomogeneousIdeal := by
      rw [hclosed]
      exact hmemw
    have heq := (projectivePointOfVector_mem_iff v hv hp).1 hmemv
    simp only [Pi.smul_apply, smul_eq_mul]
    simp only [p, map_sub, map_mul, MvPolynomial.eval₂Hom_C,
      RingHom.id_apply, MvPolynomial.eval₂Hom_X'] at heq
    field_simp
    linear_combination -heq
  · rw [Projectivization.mk_eq_mk_iff']
    rintro ⟨a, ha⟩
    have ha0 : a ≠ 0 := by
      intro ha0
      apply hv
      rw [← ha, ha0, zero_smul]
    simpa only [ha] using projectivePointOfVector_smul w hw a ha0

noncomputable def projectivePointOfProjectivization
    {sigma : Type} [Finite sigma] :
    Projectivization k (sigma → k) →
      Point (projectiveSpaceByCoordinates k sigma) :=
  Projectivization.lift
    (fun v ↦ projectivePointOfVector v.1 v.2)
    (by
      rintro ⟨v, hv⟩ ⟨w, hw⟩ a h
      apply (projectivePointOfVector_eq_iff_mk_eq v w hv hw).2
      rw [Projectivization.mk_eq_mk_iff']
      exact ⟨a, h.symm⟩)

private theorem projectivePointOfProjectivization_injective
    {sigma : Type} [Finite sigma] :
    Function.Injective
      (projectivePointOfProjectivization (k := k) (sigma := sigma)) := by
  intro q r h
  induction q using Projectivization.ind with
  | h v hv =>
    induction r using Projectivization.ind with
    | h w hw =>
      exact (projectivePointOfVector_eq_iff_mk_eq v w hv hw).1 h

private noncomputable def projectiveClassOfPoint
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    Projectivization k (sigma → k) :=
  Projectivization.mk k (projectivePointChartCoordinates x)
    (projectivePointChartCoordinates_ne_zero x)

private theorem projectivePointOfProjectiveClass
    {sigma : Type} [Finite sigma]
    (x : Point (projectiveSpaceByCoordinates k sigma)) :
    projectivePointOfProjectivization (projectiveClassOfPoint x) = x :=
  projectivePointOfVector_chartCoordinates x

theorem projectivePointOfProjectivization_bijective
    {sigma : Type} [Finite sigma] :
    Function.Bijective
      (projectivePointOfProjectivization (k := k) (sigma := sigma)) :=
  ⟨projectivePointOfProjectivization_injective,
    fun x ↦ ⟨projectiveClassOfPoint x, projectivePointOfProjectiveClass x⟩⟩

/-- Rational points of coordinate projective space are nonzero coordinate vectors modulo scale. -/
noncomputable def projectiveSpaceByCoordinatesPointEquiv
    {sigma : Type} [Finite sigma] :
    Point (projectiveSpaceByCoordinates k sigma) ≃
      Projectivization k (sigma → k) :=
  (Equiv.ofBijective projectivePointOfProjectivization
    projectivePointOfProjectivization_bijective).symm

@[simp]
theorem projectiveSpaceByCoordinatesPointEquiv_symm_mk
    {sigma : Type} [Finite sigma] (v : sigma → k) (hv : v ≠ 0) :
    (projectiveSpaceByCoordinatesPointEquiv (k := k) (sigma := sigma)).symm
        (Projectivization.mk k v hv) =
      projectivePointOfVector v hv :=
  rfl

@[simp]
theorem projectiveSpaceByCoordinatesPointEquiv_projectivePointOfVector
    {sigma : Type} [Finite sigma] (v : sigma → k) (hv : v ≠ 0) :
    projectiveSpaceByCoordinatesPointEquiv
        (projectivePointOfVector v hv) =
      Projectivization.mk k v hv := by
  simpa only [projectiveSpaceByCoordinatesPointEquiv_symm_mk] using
    (projectiveSpaceByCoordinatesPointEquiv (k := k) (sigma := sigma)).apply_symm_apply
      (Projectivization.mk k v hv)

noncomputable def projectivizationEquivOfLinearEquiv
    {V W : Type*} [AddCommGroup V] [Module k V]
    [AddCommGroup W] [Module k W] (e : V ≃ₗ[k] W) :
    Projectivization k V ≃ Projectivization k W where
  toFun := Projectivization.map e.toLinearMap e.injective
  invFun := Projectivization.map e.symm.toLinearMap e.symm.injective
  left_inv q := by
    induction q using Projectivization.ind with
    | h v hv =>
      rw [Projectivization.map_mk, Projectivization.map_mk,
        Projectivization.mk_eq_mk_iff']
      refine ⟨1, ?_⟩
      simp only [one_smul]
      change v = e.symm (e v)
      exact e.symm_apply_apply v |>.symm
  right_inv q := by
    induction q using Projectivization.ind with
    | h w hw =>
      rw [Projectivization.map_mk, Projectivization.map_mk,
        Projectivization.mk_eq_mk_iff']
      refine ⟨1, ?_⟩
      simp only [one_smul]
      change w = e (e.symm w)
      exact e.apply_symm_apply w |>.symm

/-- A basis identifies rational points of geometric projective space with lines in the vector
space. -/
noncomputable def projectiveSpacePointEquivOf
    {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (b : Module.Basis (Fin (Module.finrank k E)) k E) :
    Point (projectiveSpace k E) ≃ Projectivization k E :=
  (projectiveSpaceByCoordinatesPointEquiv
    (k := k) (sigma := Fin (Module.finrank k E))).trans
      (projectivizationEquivOfLinearEquiv b.equivFun.symm)

@[simp]
theorem projectiveSpacePointEquivOf_projectivePointOfVector
    {E : Type u} [AddCommGroup E] [Module k E] [FiniteDimensional k E]
    (b : Module.Basis (Fin (Module.finrank k E)) k E) (v : E) (hv : v ≠ 0) :
    projectiveSpacePointEquivOf b
        (projectivePointOfVector (b.equivFun v) (b.equivFun.map_ne_zero_iff.mpr hv)) =
      Projectivization.mk k v hv := by
  change projectivizationEquivOfLinearEquiv b.equivFun.symm
    (projectiveSpaceByCoordinatesPointEquiv
      (projectivePointOfVector (b.equivFun v) _)) = _
  rw [projectiveSpaceByCoordinatesPointEquiv_projectivePointOfVector]
  change Projectivization.map b.equivFun.symm.toLinearMap b.equivFun.symm.injective
    (Projectivization.mk k (b.equivFun v) _) = _
  rw [Projectivization.map_mk, Projectivization.mk_eq_mk_iff']
  exact ⟨1, by simp⟩

end Theory.AlgebraicGroup.Variety.Geometric
