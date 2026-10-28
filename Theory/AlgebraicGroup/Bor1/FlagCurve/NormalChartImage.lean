module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.PolynomialChart
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Normality identifies the literal monomial chart

The coordinate ratios give all occupied monomials in the faithful pullback of
a normal affine chart. Coprime exponents therefore force surjectivity. The
final theorem applies this to an actual dominant scheme morphism whose literal
coordinate-chart composite is the polynomial parametrization, proving that
morphism is an isomorphism. This is the local curve-identification step in
Borel, Linear Algebraic Groups, §13.13, valid in every characteristic.
-/

public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory MorphismProperty AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u v
variable {k : Type u} [Field k] {ι : Type}

noncomputable def chartScalar (i : ι) :
    k →+* HomogeneousLocalization.Away (projectiveGrading k ι) (MvPolynomial.X i) :=
  (HomogeneousLocalization.fromZeroRingHom (projectiveGrading k ι)
    (Submonoid.powers (MvPolynomial.X i))).comp (algebraMap k (projectiveGrading k ι 0))

theorem polynomialChartMap_scalar (p : ι → Polynomial k) (i : ι) (hi : IsUnit (p i)) (x : k) :
    polynomialChartMap p i hi (chartScalar i x) = Polynomial.C x := by
  change Localization.awayLift (MvPolynomial.aeval p).toRingHom (MvPolynomial.X i) (by simpa using hi)
    (Localization.mk (MvPolynomial.C x) 1) = _
  rw [Localization.mk_one_eq_algebraMap]
  simp [Localization.awayLift]

theorem monomialChartMap_ratio (c : ι → k) (n : ι → ℕ) (i j : ι)
    (hn : n i = 0) (hc : c i ≠ 0) (hi : IsUnit (monomialCoordinates c n i)) :
    polynomialChartMap (monomialCoordinates c n) i hi
      (HomogeneousLocalization.Away.mk (projectiveGrading k ι)
        (MvPolynomial.isHomogeneous_X k i) 1 (MvPolynomial.X j)
          (MvPolynomial.isHomogeneous_X k j)) =
      Polynomial.C (c j / c i) * Polynomial.X ^ n j := by
  rw [polynomialChartMap_mk (monomialCoordinates c n) i hi (Polynomial.C ((c i)⁻¹))
    (by simp [monomialCoordinates, hn, ← Polynomial.C_mul, hc])]
  simp only [MvPolynomial.aeval_X, monomialCoordinates, pow_one, div_eq_mul_inv,
    Polynomial.C_mul]
  ring

theorem normal_monomial_chart_image_surjective
    {R : Type v} [CommRing R] [IsIntegrallyClosed R]
    (c : ι → k) (n : ι → ℕ) (i : ι) (hn : n i = 0) (hc : c i ≠ 0)
    (hi : IsUnit (monomialCoordinates c n i))
    (α : HomogeneousLocalization.Away (projectiveGrading k ι) (MvPolynomial.X i) →+* R)
    (β : R →+* Polynomial k) (hβ : Function.Injective β)
    (hcomp : β.comp α = polynomialChartMap (monomialCoordinates c n) i hi)
    (s : Finset ι) (hcs : ∀ j ∈ s, c j ≠ 0) (hgcd : s.gcd n = 1) :
    Function.Surjective β := by
  let : Algebra k R := (α.comp (chartScalar i)).toAlgebra
  let f : R →ₐ[k] Polynomial k :=
    { toRingHom := β
      commutes' := fun x => (DFunLike.congr_fun hcomp (chartScalar i x)).trans
        (polynomialChartMap_scalar (monomialCoordinates c n) i hi x) }
  apply normal_polynomial_hom_surjective f hβ s n (fun j => c j / c i)
    (fun j hj => div_ne_zero (hcs j hj) hc) hgcd
  intro j hj
  refine ⟨α (HomogeneousLocalization.Away.mk (projectiveGrading k ι)
    (MvPolynomial.isHomogeneous_X k i) 1 (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X k j)), ?_⟩
  exact (DFunLike.congr_fun hcomp _).trans (monomialChartMap_ratio c n i j hn hc hi)

/-- A dominant map into a normal affine curve is a chart isomorphism when
its actual composite with the projective coordinate chart is the coprime
monomial parametrization. -/
theorem normal_monomial_chart_isIso
    {X : Scheme.{u}} [IsAffine X] [IsReduced X] [IsIntegrallyClosed Γ(X, ⊤)]
    (c : ι → k) (n : ι → ℕ) (i : ι) (hn : n i = 0) (hc : c i ≠ 0)
    (hi : IsUnit (monomialCoordinates c n i))
    (f : Spec (.of (Polynomial k)) ⟶ X) [IsDominant f] [QuasiCompact f]
    (j : X ⟶ Spec (.of (HomogeneousLocalization.Away (projectiveGrading k ι)
      (MvPolynomial.X i))))
    (hfac : f ≫ j = Spec.map (CommRingCat.ofHom
      (polynomialChartMap (monomialCoordinates c n) i hi)))
    (s : Finset ι) (hcs : ∀ j ∈ s, c j ≠ 0) (hgcd : s.gcd n = 1) : IsIso f := by
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  let R := HomogeneousLocalization.Away (projectiveGrading k ι) (MvPolynomial.X i)
  let α := ((Scheme.ΓSpecIso (.of R)).inv ≫ j.appTop).hom
  let β := (f.appTop ≫ (Scheme.ΓSpecIso (.of (Polynomial k))).hom).hom
  have hβ : Function.Injective β :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of (Polynomial k))).hom).1.comp
      (f.app_injective ⊤)
  have hcomp : β.comp α = polynomialChartMap (monomialCoordinates c n) i hi := by
    have he : (Scheme.ΓSpecIso (.of R)).inv ≫ j.appTop ≫ f.appTop ≫
        (Scheme.ΓSpecIso (.of (Polynomial k))).hom =
        CommRingCat.ofHom (polynomialChartMap (monomialCoordinates c n) i hi) := by
      rw [← Scheme.Hom.comp_appTop_assoc, hfac, Scheme.ΓSpecIso_naturality,
        Iso.inv_hom_id_assoc]
    exact congrArg CommRingCat.Hom.hom he
  have hsurj : Function.Surjective β :=
    normal_monomial_chart_image_surjective c n i hn hc hi α β hβ hcomp s hcs hgcd
  have : IsIso (f.appTop ≫ (Scheme.ΓSpecIso (.of (Polynomial k))).hom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hβ, hsurj⟩
  have : IsIso f.appTop :=
    IsIso.of_isIso_comp_right _ (Scheme.ΓSpecIso (.of (Polynomial k))).hom
  exact (arrow_mk_iso_iff (isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map f.appTop)))

end Theory.AlgebraicGroup.Bor1.FlagCurve
