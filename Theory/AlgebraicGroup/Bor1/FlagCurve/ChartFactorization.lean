module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.PolynomialChart

/-!
# The literal polynomial chart factorization

On a unit-coordinate chart the native projective polynomial curve is exactly
the spectrum map of its homogeneous-localization pullback. The proof uses the
Proj chart gluing identity and the localization universal property; no point
bijection is substituted for a scheme identity. This connects the monomial
normalization calculation to the original curve in Borel §13.13.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] {ι : Type} [Finite ι]

set_option backward.isDefEq.respectTransparency false in
@[expose]
noncomputable def polynomialChartFactor (p : ι → Polynomial k) (i : ι) (hi : IsUnit (p i)) :
    (polynomialAffineLine k).toScheme ⟶
      (Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X (R := k) i)).toScheme :=
  Spec.map (CommRingCat.ofHom (polynomialChartMap p i hi)) ≫
    (Proj.basicOpenIsoSpec (projectiveGrading k ι) (MvPolynomial.X (R := k) i)
      (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).inv

omit [Finite ι] in
/-- The explicit spectrum map on the homogeneous coordinate chart. -/
theorem polynomialChartFactor_eq (p : ι → Polynomial k) (i : ι) (hi : IsUnit (p i)) :
    polynomialChartFactor p i hi =
      Spec.map (CommRingCat.ofHom (polynomialChartMap p i hi)) ≫
        (Proj.basicOpenIsoSpec (projectiveGrading k ι) (MvPolynomial.X i)
          (MvPolynomial.isHomogeneous_X k i) Nat.zero_lt_one).inv := rfl

omit [Finite ι] in
set_option backward.isDefEq.respectTransparency false in
theorem polynomialChartMap_localize (p : ι → Polynomial k) (i : ι) (hi : IsUnit (p i))
    (h : Submonoid.powers (MvPolynomial.X (R := k) i) ≤
      (Submonoid.powers (sections p (MvPolynomial.X (R := k) i))).comap (sections p)) :
    (IsLocalization.map (Localization.Away (sections p (MvPolynomial.X (R := k) i)))
        (sections p) h).comp
      (algebraMap (HomogeneousLocalization.Away (projectiveGrading k ι) (MvPolynomial.X (R := k) i))
        (Localization.Away (MvPolynomial.X (R := k) i))) =
      (algebraMap Γ(Spec (.of (Polynomial k)), ⊤)
        (Localization.Away (sections p (MvPolynomial.X (R := k) i)))).comp
      ((Scheme.ΓSpecIso (.of (Polynomial k))).inv.hom.comp (polynomialChartMap p i hi)) := by
  have H : IsLocalization.map (Localization.Away (sections p (MvPolynomial.X (R := k) i)))
        (sections p) h =
      (algebraMap Γ(Spec (.of (Polynomial k)), ⊤)
        (Localization.Away (sections p (MvPolynomial.X (R := k) i)))).comp
      ((Scheme.ΓSpecIso (.of (Polynomial k))).inv.hom.comp
        (Localization.awayLift (MvPolynomial.aeval p).toRingHom (MvPolynomial.X (R := k) i)
          (by simpa using hi))) := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (MvPolynomial.X (R := k) i))
    apply RingHom.ext
    intro a
    simp only [RingHom.comp_apply, IsLocalization.map_eq, Localization.awayLift,
      IsLocalization.Away.lift_eq]
    rfl
  ext x
  rw [RingHom.comp_apply, H]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem polynomialChartFactor_fac (p : ι → Polynomial k) (i : ι) (hi : IsUnit (p i)) :
    polynomialChartFactor p i hi ≫
      (Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X (R := k) i)).ι =
      (curve p ⟨i, hi⟩).hom := by
  let X := (polynomialAffineLine k).toScheme
  let U := Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X (R := k) i)
  let r := sections p (MvPolynomial.X (R := k) i)
  have hr : IsUnit r := by
    change IsUnit ((Scheme.ΓSpecIso (.of (Polynomial k))).inv.hom
      ((MvPolynomial.aeval p) (MvPolynomial.X (R := k) i)))
    rw [MvPolynomial.aeval_X]
    exact hi.map _
  have htop : X.basicOpen r = ⊤ := X.basicOpen_of_isUnit hr
  have hres := Proj.fromOfGlobalSections_resLE (projectiveGrading k ι) (sections p)
    (irrelevant p ⟨i, hi⟩) Nat.zero_lt_one (MvPolynomial.isHomogeneous_X k i)
  have hfac : (X.basicOpen r).ι ≫ (curve p ⟨i, hi⟩).hom =
      Proj.toBasicOpenOfGlobalSections (projectiveGrading k ι) (sections p) rfl
        Nat.zero_lt_one (MvPolynomial.isHomogeneous_X k i) ≫ U.ι := by
    rw [← hres, Scheme.Hom.resLE_comp_ι]
    rfl
  have : IsIso (X.basicOpen r).ι := by
    rw [htop]
    change IsIso (Scheme.topIso X).hom
    infer_instance
  rw [← cancel_epi (X.basicOpen r).ι]
  rw [hfac]
  change ((X.basicOpen r).ι ≫ polynomialChartFactor p i hi) ≫ U.ι = _
  rw [cancel_mono]
  unfold polynomialChartFactor Proj.toBasicOpenOfGlobalSections
  simp only [← Category.assoc, cancel_mono]
  rw [polynomialChartMap_localize p i hi]
  simp only [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc,
    basicOpenIsoSpecAway_hom_SpecMap_assoc, morphismRestrict_ι_assoc,
    Scheme.isoOfEq_inv_ι_assoc]
  rw [← SpecMap_ΓSpecIso_hom]
  simp
  rfl

end Theory.AlgebraicGroup.Bor1.FlagCurve
