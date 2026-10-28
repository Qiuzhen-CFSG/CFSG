module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.NormalMonomial
public import Theory.AlgebraicGroup.Variety.ProjectiveLine
public import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-!
# Normal monomial affine charts

A faithful affine parametrization whose normal coordinate ring contains the
coprime monomials is an isomorphism. This turns the normalization calculation
into the literal scheme morphism used for the two charts in Borel §13.13.
-/

public noncomputable section

open CategoryTheory MorphismProperty AlgebraicGeometry
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k]

/-- The actual affine parametrization is an isomorphism when its faithful
coordinate pullback has a normal source and coprime monomial image. -/
theorem affine_chart_isIso_of_normal_monomials
    {X : Scheme.{u}} [IsAffine X] [Algebra k Γ(X, ⊤)] [IsIntegrallyClosed Γ(X, ⊤)]
    (f : Spec (.of (Polynomial k)) ⟶ X)
    (φ : Γ(X, ⊤) →ₐ[k] Polynomial k)
    (hφ : f.appTop ≫ (Scheme.ΓSpecIso (.of (Polynomial k))).hom =
      CommRingCat.ofHom φ.toRingHom)
    (hinj : Function.Injective φ)
    {ι : Type*} (s : Finset ι) (n : ι → ℕ) (c : ι → k)
    (hc : ∀ i ∈ s, c i ≠ 0) (hgcd : s.gcd n = 1)
    (hgen : ∀ i ∈ s, Polynomial.C (c i) * Polynomial.X ^ n i ∈ φ.range) :
    IsIso f := by
  have hbij : Function.Bijective φ :=
    ⟨hinj, normal_polynomial_hom_surjective φ hinj s n c hc hgcd hgen⟩
  have : IsIso (CommRingCat.ofHom φ.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr hbij
  have : IsIso (f.appTop ≫ (Scheme.ΓSpecIso (.of (Polynomial k))).hom) := hφ ▸ inferInstance
  have : IsIso f.appTop := IsIso.of_isIso_comp_right _ (Scheme.ΓSpecIso (.of (Polynomial k))).hom
  exact (arrow_mk_iso_iff (isomorphisms _) (arrowIsoSpecΓOfIsAffine f)).mpr
    (inferInstanceAs (IsIso (Spec.map f.appTop)))

end Theory.AlgebraicGroup.Bor1.FlagCurve
