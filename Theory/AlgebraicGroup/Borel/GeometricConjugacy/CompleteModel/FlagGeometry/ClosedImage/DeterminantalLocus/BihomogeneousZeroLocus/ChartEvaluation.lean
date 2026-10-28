module

public import Theory.AlgebraicGroup.Borel.GeometricConjugacy.CompleteModel.FlagGeometry.ClosedImage.DeterminantalLocus.Assembly
/-!
# Evaluation on standard projective charts

The degree-zero localization at `X_i` contains the normalized coordinates
`X_j / X_i`. For a rational point represented by `v`, any lift to this affine
chart evaluates these coordinates as `v_j / v_i`. The proof compares homogeneous
prime ideals through the Proj chart isomorphism, then applies that comparison to
`v_i X_j - v_j X_i`.

The homogeneous-localization calculation extends the private chart argument in
`Variety.ProjectivePoint`. This supplies the chart comparison for biprojective
equations, used for the flag variety in Borel, *Linear Algebraic Groups*, §11.1.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup.Variety.Geometric
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus.BihomogeneousCharts
universe u
variable {k : Type u} [Field k]
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

private theorem away_eval_coordinates
    {sigma : Type} [Finite sigma] (i : sigma)
    (p : MvPolynomial sigma k) (n : ℕ)
    (hp : p ∈ projectiveGrading k sigma n) :
    MvPolynomial.eval₂Hom
        ((HomogeneousLocalization.fromZeroRingHom
          (projectiveGrading k sigma) _).comp
            (algebraMap k (projectiveGrading k sigma 0)))
        (fun j ↦ HomogeneousLocalization.Away.mk
          (projectiveGrading k sigma) (MvPolynomial.isHomogeneous_X k i) 1
          (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X k j)) p =
      HomogeneousLocalization.Away.mk
        (projectiveGrading k sigma) (MvPolynomial.isHomogeneous_X k i) n p
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
        (projectiveGrading k sigma) (MvPolynomial.isHomogeneous_X k i) 1
        (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X k j)) =
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


/-- The degree-zero coordinate ring of the standard chart at `X_i`. -/
abbrev ChartRing {sigma : Type} (i : sigma) :=
  HomogeneousLocalization.Away (projectiveGrading k sigma) (MvPolynomial.X i)

/-- The coordinate fraction `X_j / X_i` in the standard chart. -/
def coordinate {sigma : Type} (i j : sigma) : ChartRing (k := k) i :=
  HomogeneousLocalization.Away.mk (projectiveGrading k sigma)
    (MvPolynomial.isHomogeneous_X k i) 1 (MvPolynomial.X j) (MvPolynomial.isHomogeneous_X k j)

private def coefficients {sigma : Type} (i : sigma) : k →+* ChartRing (k := k) i :=
  (HomogeneousLocalization.fromZeroRingHom (projectiveGrading k sigma) _).comp
    (algebraMap k (projectiveGrading k sigma 0))

/-- The standard affine-chart open immersion into projective space. -/
def inclusion {sigma : Type} (i : sigma) :
    Spec (.of (ChartRing (k := k) i)) ⟶ Proj (projectiveGrading k sigma) :=
  Proj.awayι (projectiveGrading k sigma) (MvPolynomial.X i)
    (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one

private theorem coordinate_self {sigma : Type} (i : sigma) :
    coordinate (k := k) i i = 1 := by
  apply HomogeneousLocalization.val_injective
  have hpow : MvPolynomial.X i ∈ Submonoid.powers (MvPolynomial.X i) :=
    Submonoid.mem_powers (MvPolynomial.X i : MvPolynomial sigma k)
  simp only [coordinate, HomogeneousLocalization.Away.val_mk, pow_one]
  rw [HomogeneousLocalization.val_one]
  simpa only [Localization.mk_eq_mk'] using
    (IsLocalization.mk'_self (Localization.Away (MvPolynomial.X i : MvPolynomial sigma k)) hpow)

private theorem coefficients_comp {sigma : Type} [Finite sigma] (i : sigma)
    (v : sigma → k) (hv : v ≠ 0)
    (q : Spec (.of k) ⟶ Spec (.of (ChartRing (k := k) i)))
    (hq : q ≫ inclusion i = (projectivePointOfVector v hv).val) :
    (Spec.preimage q).hom.comp (coefficients i) = RingHom.id k := by
  have he : inclusion (k := k) i ≫
      (projectiveSpaceByCoordinates k sigma).structureMap =
      Spec.map (CommRingCat.ofHom (coefficients i)) := by
    change Proj.awayι _ _ _ _ ≫ (Proj.toSpecZero _ ≫ Spec.map _) = _
    rw [← Category.assoc, Proj.awayι_toSpecZero, ← Spec.map_comp]
    rfl
  have h : q ≫ Spec.map (CommRingCat.ofHom (coefficients i)) = 𝟙 _ := by
    rw [← he, ← Category.assoc, hq]
    exact (projectivePointOfVector v hv).property
  have h' := congrArg (fun f => (Spec.preimage f).hom) h
  simp only [Spec.preimage_comp, Spec.preimage_map, Spec.preimage_id,
    CommRingCat.hom_comp] at h'
  exact h'

set_option backward.isDefEq.respectTransparency false in
private theorem homogeneous_eval {sigma : Type} [Finite sigma] (i : sigma)
    (v : sigma → k) (hv : v ≠ 0)
    (q : Spec (.of k) ⟶ Spec (.of (ChartRing (k := k) i)))
    (hq : q ≫ inclusion i = (projectivePointOfVector v hv).val)
    (p : MvPolynomial sigma k) (n : ℕ) (hp : p ∈ projectiveGrading k sigma n) :
    MvPolynomial.eval (fun j => (Spec.preimage q).hom (coordinate i j)) p = 0 ↔
      MvPolynomial.eval v p = 0 := by
  let y := q (IsLocalRing.closedPoint k)
  let x := inclusion i y
  have hx : x ∈ Proj.basicOpen (projectiveGrading k sigma) (MvPolynomial.X i) := by
    rw [← Proj.opensRange_awayι _ _ (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one]
    exact ⟨y, rfl⟩
  have hxy : (ProjectiveSpectrum.Proj.toSpec (projectiveGrading k sigma)
      (MvPolynomial.X i)).base ⟨x, hx⟩ = y := by
    change (Proj.basicOpenIsoSpec (projectiveGrading k sigma)
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).hom
      ((Proj.basicOpenIsoSpec (projectiveGrading k sigma)
      (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).inv y) = y
    exact congrArg (fun f : Spec (.of (ChartRing (k := k) i)) ⟶
      Spec (.of (ChartRing (k := k) i)) => f y)
      (Proj.basicOpenIsoSpec (projectiveGrading k sigma)
        (MvPolynomial.X i) (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).inv_hom_id
  let z : HomogeneousLocalization.NumDenSameDeg (projectiveGrading k sigma)
      (Submonoid.powers (MvPolynomial.X i)) :=
    { deg := n
      num := ⟨p, hp⟩
      den := ⟨MvPolynomial.X i ^ n, MvPolynomial.isHomogeneous_X_pow _ _⟩
      den_mem := ⟨n, rfl⟩ }
  have hz : HomogeneousLocalization.mk z ∈ y.asIdeal ↔
      p ∈ x.asHomogeneousIdeal := by
    rw [← hxy]
    exact ProjectiveSpectrum.Proj.mk_mem_toSpec_base_apply _ _ z
  have hzmk : HomogeneousLocalization.mk z =
      HomogeneousLocalization.Away.mk (projectiveGrading k sigma)
        (MvPolynomial.isHomogeneous_X k i) n p (by simpa using hp) := by
    apply HomogeneousLocalization.val_injective
    rfl
  have hmem (t : ChartRing (k := k) i) : t ∈ y.asIdeal ↔ (Spec.preimage q).hom t = 0 := by
    have hmap := congrArg (fun f => f (IsLocalRing.closedPoint k)) (Spec.map_preimage q)
    dsimp only [y]
    rw [← hmap]
    change (Spec.preimage q).hom t ∈ (IsLocalRing.closedPoint k).asIdeal ↔ _
    have hclosed : (IsLocalRing.closedPoint k).asIdeal = (⊥ : Ideal k) :=
      (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
    rw [hclosed]
    exact Ideal.mem_bot
  rw [hzmk, hmem, ← away_eval_coordinates i p n hp,
    MvPolynomial.map_eval₂Hom] at hz
  change MvPolynomial.eval₂Hom ((Spec.preimage q).hom.comp (coefficients i))
    (fun j => (Spec.preimage q).hom (coordinate i j)) p = 0 ↔
      p ∈ x.asHomogeneousIdeal at hz
  rw [coefficients_comp i v hv q hq] at hz
  change MvPolynomial.eval (fun j => (Spec.preimage q).hom (coordinate i j)) p = 0 ↔
    p ∈ x.asHomogeneousIdeal at hz
  rw [hz]
  have he : x = (projectivePointOfVector v hv).val (IsLocalRing.closedPoint k) :=
    congrArg (fun f => f (IsLocalRing.closedPoint k)) hq
  rw [he]
  exact projectivePointOfVector_mem_iff v hv hp

/-- The normalized coordinate on a standard chart evaluates to the corresponding ratio. -/
theorem point_coordinate {sigma : Type} [Finite sigma] (i j : sigma)
    (v : sigma → k) (hv : v ≠ 0) (hi : v i ≠ 0)
    (q : Spec (.of k) ⟶ Spec (.of (ChartRing (k := k) i)))
    (hq : q ≫ inclusion i = (projectivePointOfVector v hv).val) :
    (Spec.preimage q).hom (coordinate i j) = (v i)⁻¹ * v j := by
  have hp : (MvPolynomial.C (v i) * MvPolynomial.X j -
      MvPolynomial.C (v j) * MvPolynomial.X i : MvPolynomial sigma k) ∈
      projectiveGrading k sigma 1 :=
    ((MvPolynomial.isHomogeneous_X k j).C_mul _).sub
      ((MvPolynomial.isHomogeneous_X k i).C_mul _)
  have h := (homogeneous_eval i v hv q hq _ 1 hp).mpr (by simp [mul_comm])
  simp only [map_sub, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    coordinate_self, map_one, mul_one, sub_eq_zero] at h
  rw [← h]
  field_simp

/-- Evaluation of a global section at a rational scheme point. -/
def pointEval {X : Scheme.{u}} (q : Spec (.of k) ⟶ X) : Γ(X, ⊤) →+* k :=
  (Scheme.ΓSpecIso (.of k)).hom.hom.comp q.appTop.hom

/-- Evaluating a pulled-back affine function is the corresponding ring homomorphism. -/
theorem pointEval_spec {X : Scheme.{u}} {R : CommRingCat.{u}}
    (q : Spec (.of k) ⟶ X) (f : X ⟶ Spec R) (r : R) :
    pointEval q (f.appTop ((Scheme.ΓSpecIso R).inv r)) =
      (Spec.preimage (q ≫ f)).hom r := by
  have h := Scheme.ΓSpecIso_naturality (Spec.preimage (q ≫ f))
  rw [Spec.map_preimage, Scheme.Hom.comp_appTop] at h
  have h' := congrArg (fun g : Γ(Spec R, ⊤) ⟶ CommRingCat.of k =>
    g ((Scheme.ΓSpecIso R).inv r)) h
  change pointEval q (f.appTop ((Scheme.ΓSpecIso R).inv r)) =
    (Spec.preimage (q ≫ f)).hom
      ((Scheme.ΓSpecIso R).hom ((Scheme.ΓSpecIso R).inv r)) at h'
  simpa only [Iso.inv_hom_id_apply] using h'

/-- A rational point over the base field evaluates constant sections identically. -/
theorem pointEval_coeff {X : Scheme.{u}}
    (q : Spec (.of k) ⟶ X) (s : X ⟶ Spec (.of k)) (hs : q ≫ s = 𝟙 _) (r : k) :
    pointEval q (s.appTop ((Scheme.ΓSpecIso (.of k)).inv r)) = r := by
  rw [pointEval_spec, hs, Spec.preimage_id]
  rfl

/-- The nonvanishing open of a section detects nonzero rational-point evaluation. -/
theorem pointEval_nonzero {X : Scheme.{u}} (q : Spec (.of k) ⟶ X) (r : Γ(X, ⊤)) :
    q (IsLocalRing.closedPoint k) ∈ X.basicOpen r ↔ pointEval q r ≠ 0 := by
  change IsLocalRing.closedPoint k ∈ q ⁻¹ᵁ X.basicOpen r ↔ _
  rw [Scheme.preimage_basicOpen_top]
  have hr : q.appTop r = (Scheme.ΓSpecIso (.of k)).inv (pointEval q r) :=
    ((Scheme.ΓSpecIso (.of k)).hom_inv_id_apply _).symm
  rw [hr, basicOpen_eq_of_affine]
  change pointEval q r ∉ (IsLocalRing.closedPoint k).asIdeal ↔ _
  have hclosed : (IsLocalRing.closedPoint k).asIdeal = (⊥ : Ideal k) :=
    (Ideal.eq_bot_or_top _).resolve_right (IsLocalRing.closedPoint k).isPrime.ne_top
  rw [hclosed]
  rfl
end Theory.AlgebraicGroup.BorelGeometricConjugacy.FlagGeometry.DeterminantalLocus.BihomogeneousCharts
