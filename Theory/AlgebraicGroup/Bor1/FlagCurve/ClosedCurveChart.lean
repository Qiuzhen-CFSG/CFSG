module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.NormalChartImage
public import Theory.AlgebraicGroup.Bor1.FlagCurve.ChartFactorization
public import Theory.AlgebraicGroup.Variety.OpenSubvariety
public import Theory.AlgebraicGroup.Variety.BijectiveNormalization

/-!
# Normal closed curves and their monomial open charts

A dominant monomial parametrization of a normal irreducible projective curve
is an open immersion after dividing the occupied exponents to gcd one. The
proof restricts the actual curve to its constant-coordinate basic open, uses
normality of its section ring, and applies the literal chart factorization.
This is the local isomorphism step in Borel, Linear Algebraic Groups, §13.13.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
open Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] {ι : Type} [Finite ι]

set_option backward.isDefEq.respectTransparency false in
theorem closed_curve_chart_normal
    {Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (hY : IsIrreducible Y) (hN : IsNormal Y)
    (i : Morphism Y (projectiveSpaceByCoordinates k ι)) [IsClosedImmersion i.hom]
    (a : ι)
    (hne : Nonempty (i.hom ⁻¹ᵁ Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X a))) :
    IsIntegrallyClosed Γ((i.hom ⁻¹ᵁ Proj.basicOpen (projectiveGrading k ι)
      (MvPolynomial.X a)).toScheme, ⊤) := by
  let U := i.hom ⁻¹ᵁ Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X a)
  have : IrreducibleSpace Y.toScheme := hY
  have : IsIntegral Y.toScheme := isIntegral_of_irreducibleSpace_of_isReduced _
  have : Nonempty U := hne
  have hU : IsAffineOpen U :=
    (Proj.isAffineOpen_basicOpen (projectiveGrading k ι) (MvPolynomial.X a)
      (MvPolynomial.isHomogeneous_X k a) Nat.zero_lt_one).preimage i.hom
  have : IsIntegrallyClosed Γ(Y.toScheme, U) :=
    affineSections_isIntegrallyClosed_of_isNormal hN hU
  exact IsIntegrallyClosed.of_equiv U.topIso.commRingCatIsoToRingEquiv.symm

set_option backward.isDefEq.respectTransparency false in
theorem normal_monomial_parametrization_isOpenImmersion
    {Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (hY : IsIrreducible Y) (hN : IsNormal Y)
    (i : Morphism Y (projectiveSpaceByCoordinates k ι)) [IsClosedImmersion i.hom]
    (c : ι → k) (n : ι → ℕ) (a : ι) (ha : n a = 0) (hca : c a ≠ 0)
    (f : Morphism (polynomialAffineLine k) Y) [IsDominant f.hom]
    (hfac : f.comp i = monomialCurve c n ⟨a, ha, hca⟩)
    (s : Finset ι) (hcs : ∀ j ∈ s, c j ≠ 0) (hgcd : s.gcd n = 1) :
    IsOpenImmersion f.hom := by
  let V := Proj.basicOpen (projectiveGrading k ι) (MvPolynomial.X a)
  let U := i.hom ⁻¹ᵁ V
  have hunit : IsUnit (monomialCoordinates c n a) := by
    simpa [monomialCoordinates, ha] using
      (isUnit_iff_ne_zero.mpr hca).map (Polynomial.C : k →+* Polynomial k)
  have hrange : Set.range f.hom ⊆ U := by
    rintro _ ⟨x, rfl⟩
    have h := curve_preimage_coordinate_top (monomialCoordinates c n) a hunit
    have hm : x ∈ (monomialCurve c n ⟨a, ha, hca⟩).hom ⁻¹ᵁ V := by
      change x ∈ (curve (monomialCoordinates c n) ⟨a, hunit⟩).hom ⁻¹ᵁ V
      rw [h]
      trivial
    rw [← hfac] at hm
    exact hm
  let fU := restrictToOpenSubvariety U f hrange
  have hfu : fU.hom ≫ U.ι = f.hom :=
    congrArg Morphism.hom (restrictToOpenSubvariety_inclusion U f hrange)
  have : IsDominant fU.hom := by
    have : IsDominant (fU.hom ≫ U.ι) := hfu ▸ inferInstance
    exact IsDominant.of_comp_of_isOpenImmersion fU.hom U.ι
  have hne : Nonempty U := ⟨⟨f.hom (PrimeSpectrum.comap (Polynomial.evalRingHom 0) (IsLocalRing.closedPoint k)),
    hrange (Set.mem_range_self _)⟩⟩
  have : IsIntegrallyClosed Γ(U.toScheme, ⊤) := closed_curve_chart_normal hY hN i a hne
  have hU : IsAffineOpen U :=
    (Proj.isAffineOpen_basicOpen (projectiveGrading k ι) (MvPolynomial.X a)
      (MvPolynomial.isHomogeneous_X k a) Nat.zero_lt_one).preimage i.hom
  have : IsAffine U.toScheme := hU
  let j : U.toScheme ⟶ Spec (.of (HomogeneousLocalization.Away
      (projectiveGrading k ι) (MvPolynomial.X a))) :=
    i.hom ∣_ V ≫ (Proj.basicOpenIsoSpec (projectiveGrading k ι) (MvPolynomial.X a)
      (MvPolynomial.isHomogeneous_X k a) Nat.zero_lt_one).hom
  have hj : fU.hom ≫ j = Spec.map (CommRingCat.ofHom
      (polynomialChartMap (monomialCoordinates c n) a hunit)) := by
    apply (cancel_mono (Proj.awayι (projectiveGrading k ι) (MvPolynomial.X a)
      (MvPolynomial.isHomogeneous_X k a) Nat.zero_lt_one)).mp
    simp only [j, Proj.awayι, Category.assoc, Iso.hom_inv_id_assoc]
    change fU.hom ≫ (i.hom ∣_ V) ≫ V.ι = _
    rw [morphismRestrict_ι, ← Category.assoc, hfu]
    have hp := polynomialChartFactor_fac (monomialCoordinates c n) a hunit
    rw [polynomialChartFactor_eq] at hp
    exact (congrArg Morphism.hom hfac).trans hp.symm
  have : IsAffine (Y.openSubvariety U).toGeometric.toScheme := hU
  have : IsIntegrallyClosed Γ((Y.openSubvariety U).toGeometric.toScheme, ⊤) :=
    closed_curve_chart_normal hY hN i a hne
  have : IsIso fU.hom :=
    normal_monomial_chart_isIso c n a ha hca hunit fU.hom j hj s hcs hgcd
  rw [← hfu]
  infer_instance

end Theory.AlgebraicGroup.Bor1.FlagCurve
