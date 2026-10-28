module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.GlobalIso
public import Theory.AlgebraicGroup.Bor1.FlagCurve.ClosedCurveChart
public import Theory.AlgebraicGroup.Bor1.FlagCurve.ReciprocalDensity
public import Theory.AlgebraicGroup.Bor1.FlagCurve.MonomialEndpoints
public import Theory.AlgebraicGroup.Bor1.FlagCurve.WeightNormalization

/-!
# A normal projective monomial curve is the projective line

The two literal monomial charts on a normal irreducible closed curve are open
immersions after normalization to coprime exponents. Reciprocal compatibility
makes both dominant. Distinct endpoints and completeness then turn the global
parametrization into a scheme isomorphism, including in positive characteristic.
This is the monomial-curve identification in Borel, Linear Algebraic Groups, §13.13.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
open Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {ι : Type} [Finite ι]

set_option backward.isDefEq.respectTransparency false in
theorem normal_projective_monomial_curve_isIso
    {Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (hY : IsIrreducible Y) (hN : IsNormal Y)
    (i : Variety.Geometric.Morphism Y (projectiveSpaceByCoordinates k ι)) [IsClosedImmersion i.hom]
    (c : ι → k) (n : ι → ℕ) (N : ℕ) (hNpos : 0 < N)
    (a b : ι) (ha : n a = 0) (hb : n b = N) (hca : c a ≠ 0) (hcb : c b ≠ 0)
    (hbound : ∀ j, n j ≤ N)
    (s : Finset ι) (has : a ∈ s) (hcs : ∀ j ∈ s, c j ≠ 0) (hgcd : s.gcd n = 1)
    (f : Variety.Geometric.Morphism (projectiveLine k) Y)
    (hfac : f.comp i = monomialProjectiveCurve c n N ⟨a, ha, hca⟩ ⟨b, hb, hcb⟩ hbound)
    (hdom : IsDominant ((projectiveLineChartInclusion (k := k) 0).comp f).hom) :
    IsIso f.hom := by
  let f₀ := (projectiveLineChartInclusion (k := k) 0).comp f
  let f₁ := (projectiveLineChartInclusion (k := k) 1).comp f
  have : IsDominant f₀.hom := hdom
  have h₀ : f₀.comp i = monomialCurve c n ⟨a, ha, hca⟩ := by
    have he := congrArg (fun q => (projectiveLineChartInclusion (k := k) 0).comp q) hfac
    exact he.trans (monomialProjectiveCurve_chart_zero c n N _ _ hbound)
  have h₁ : f₁.comp i = monomialCurve c (fun j => N - n j)
      ⟨b, by simp [hb], hcb⟩ := by
    have he := congrArg (fun q => (projectiveLineChartInclusion (k := k) 1).comp q) hfac
    exact he.trans (monomialProjectiveCurve_chart_one c n N _ _ hbound)
  have hrec (z : k) (hz : z ≠ 0) : f₀ (affinePoint z) = f₁ (affinePoint z⁻¹) := by
    apply Subtype.ext
    apply (cancel_mono i.hom).mp
    have h := monomialCurve_reciprocal c n N ⟨a, ha, hca⟩ ⟨b, hb, hcb⟩ hbound z hz
    rw [← h₀, ← h₁] at h
    exact congrArg Subtype.val h
  have : IsDominant f₁.hom := reciprocal_curve_dominant f₀ f₁ hrec
  have : IsDominant ((projectiveLineChartInclusion (k := k) 0).hom ≫ f.hom) := hdom
  have : IsDominant f.hom := IsDominant.of_comp (projectiveLineChartInclusion (k := k) 0).hom f.hom
  have hOI₀ : IsOpenImmersion f₀.hom :=
    normal_monomial_parametrization_isOpenImmersion hY hN i c n a ha hca f₀ h₀ s hcs hgcd
  have hOI₁ : IsOpenImmersion f₁.hom :=
    normal_monomial_parametrization_isOpenImmersion hY hN i c (fun j => N - n j)
      b (by simp [hb]) hcb f₁ h₁ s hcs
      (reflected_exponents_gcd_one s n N a has ha (fun j _ => hbound j) hgcd)
  apply projectiveLine_isIso_of_open_charts f
  · intro j
    fin_cases j
    · exact hOI₀
    · exact hOI₁
  · intro he
    have hh := congrArg (fun p : Point Y => i p) he
    change (f₀.comp i) (affinePoint 0) = (f₁.comp i) (affinePoint 0) at hh
    rw [h₀, h₁] at hh
    exact monomial_endpoints_ne c n N hNpos ⟨a, ha, hca⟩ ⟨b, hb, hcb⟩ hh

end Theory.AlgebraicGroup.Bor1.FlagCurve
