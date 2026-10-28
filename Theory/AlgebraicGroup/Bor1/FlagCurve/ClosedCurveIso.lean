module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.NormalProjectiveCurve
public import Theory.AlgebraicGroup.Bor1.FlagCurve.CurveDominance
public import Theory.AlgebraicGroup.Bor1.FlagCurve.MonomialNonconstant

/-!
# The projective line of a normal monomial curve

Two reciprocal polynomial charts factor through the original closed curve.
Its dimension one and the distinct endpoint values make the first chart
 dominant. Normality then identifies both charts with affine lines; gluing
produces the scheme isomorphism over the original field. This is the explicit
normal monomial-curve step of Borel, Linear Algebraic Groups, §13.13.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
open Theory.AlgebraicGroup.Bor1.SeparatingBorel.ProjectiveLimit
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k] {ι : Type} [Finite ι]

set_option backward.isDefEq.respectTransparency false in
theorem normal_projective_monomial_curve_isIso_of_dimension_one
    {Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (hY : IsIrreducible Y) (hN : IsNormal Y) (hdim : dimension Y = 1)
    (i : Variety.Geometric.Morphism Y (projectiveSpaceByCoordinates k ι)) [IsClosedImmersion i.hom]
    (c : ι → k) (n : ι → ℕ) (N : ℕ) (hNpos : 0 < N)
    (a b : ι) (ha : n a = 0) (hb : n b = N) (hca : c a ≠ 0) (hcb : c b ≠ 0)
    (hbound : ∀ j, n j ≤ N)
    (s : Finset ι) (has : a ∈ s) (hcs : ∀ j ∈ s, c j ≠ 0) (hgcd : s.gcd n = 1)
    (f : Variety.Geometric.Morphism (projectiveLine k) Y)
    (hfac : f.comp i = monomialProjectiveCurve c n N ⟨a, ha, hca⟩ ⟨b, hb, hcb⟩ hbound) :
    IsIso f.hom := by
  let f₀ := (projectiveLineChartInclusion (k := k) 0).comp f
  have h₀ : f₀.comp i = monomialCurve c n ⟨a, ha, hca⟩ := by
    have he := congrArg (fun q => (projectiveLineChartInclusion (k := k) 0).comp q) hfac
    exact he.trans (monomialProjectiveCurve_chart_zero c n N _ _ hbound)
  have : IrreducibleSpace Y.toScheme := hY
  have : IrreducibleSpace (polynomialAffineLine k).toScheme := by
    change IrreducibleSpace (PrimeSpectrum (Polynomial k))
    infer_instance
  have hdom : IsDominant f₀.hom := f₀.dominant_of_nonconstant_to_irreducible_curve hdim
    (affinePoint 0) (affinePoint 1) (by
      intro he
      have hh := congrArg (fun p : Point Y => i p) he
      change (f₀.comp i) (affinePoint 0) = (f₀.comp i) (affinePoint 1) at hh
      rw [h₀] at hh
      exact monomialCurve_zero_ne_one c n ⟨a, ha, hca⟩ b
        (hb ▸ Nat.ne_of_gt hNpos) hcb hh)
  exact normal_projective_monomial_curve_isIso hY hN i c n N hNpos a b ha hb hca hcb
    hbound s has hcs hgcd f hfac hdom

omit [IsAlgClosed k] in
private noncomputable def liftClosed
    {X Y Z : Theory.AlgebraicGroup.Variety.Geometric k}
    (i : Variety.Geometric.Morphism Y Z) [IsClosedImmersion i.hom]
    (f : Variety.Geometric.Morphism X Z) (hf : Set.range f.hom ⊆ Set.range i.hom) :
    Variety.Geometric.Morphism X Y := by
  let C : Closeds Z.toScheme := ⟨Set.range i.hom, i.hom.isClosedEmbedding.isClosed_range⟩
  have hker : i.hom.ker ≤ f.hom.ker :=
    (Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp i.hom.range_subset_ker_support).trans
      (vanishingIdeal_le_ker_of_isReduced C f.hom hf)
  exact ⟨IsClosedImmersion.lift i.hom f.hom hker, by
    rw [← i.commutes, ← Category.assoc, IsClosedImmersion.lift_fac, f.commutes]⟩

omit [IsAlgClosed k] in
private theorem liftClosed_fac
    {X Y Z : Theory.AlgebraicGroup.Variety.Geometric k}
    (i : Variety.Geometric.Morphism Y Z) [IsClosedImmersion i.hom]
    (f : Variety.Geometric.Morphism X Z) (hf : Set.range f.hom ⊆ Set.range i.hom) :
    (liftClosed i f hf).comp i = f := by
  apply Variety.Geometric.Morphism.ext
  exact IsClosedImmersion.lift_fac _ _ _

set_option backward.isDefEq.respectTransparency false in
theorem exists_projectiveLine_iso_of_monomial_units
    {Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (hY : IsIrreducible Y) (hN : IsNormal Y) (hdim : dimension Y = 1)
    (i : Variety.Geometric.Morphism Y (projectiveSpaceByCoordinates k ι)) [IsClosedImmersion i.hom]
    (c : ι → k) (n : ι → ℕ) (N : ℕ) (hNpos : 0 < N)
    (a b : ι) (ha : n a = 0) (hb : n b = N) (hca : c a ≠ 0) (hcb : c b ≠ 0)
    (hbound : ∀ j, n j ≤ N)
    (s : Finset ι) (has : a ∈ s) (hcs : ∀ j ∈ s, c j ≠ 0) (hgcd : s.gcd n = 1)
    (hunits : ∀ z : k, z ≠ 0 →
      (monomialCurve c n ⟨a, ha, hca⟩ (affinePoint z)).1 (IsLocalRing.closedPoint k) ∈
        Set.range i.hom) :
    ∃ e : Y.toScheme ≅ (projectiveLine k).toScheme,
      e.hom ≫ (projectiveLine k).structureMap = Y.structureMap := by
  let F := monomialProjectiveCurve c n N ⟨a, ha, hca⟩ ⟨b, hb, hcb⟩ hbound
  have hclosed := i.hom.isClosedEmbedding.isClosed_range
  have h₀ := affine_curve_range_subset_closed_of_nonzero
    (monomialCurve c n ⟨a, ha, hca⟩) hclosed hunits
  have h₁ : Set.range (monomialCurve c (fun j => N - n j)
      ⟨b, by simp [hb], hcb⟩).hom ⊆ Set.range i.hom :=
    affine_curve_range_subset_closed_of_nonzero _ hclosed (by
      intro z hz
      have he := monomialCurve_reciprocal c n N ⟨a, ha, hca⟩ ⟨b, hb, hcb⟩ hbound
        z⁻¹ (inv_ne_zero hz)
      rw [inv_inv] at he
      rw [← he]
      exact hunits z⁻¹ (inv_ne_zero hz))
  have hF : Set.range F.hom ⊆ Set.range i.hom := by
    rintro _ ⟨x, rfl⟩
    have hx : ∃ j : Fin 2, ∃ z : (polynomialAffineLine k).toScheme,
        (projectiveLineChartInclusion j).hom z = x :=
      (projectiveLineAffineCover (k := k)).exists_eq x
    obtain ⟨j, z, hz⟩ := hx
    rw [← hz, ← Scheme.Hom.comp_apply]
    fin_cases j
    · have he := congrArg Variety.Geometric.Morphism.hom
        (monomialProjectiveCurve_chart_zero c n N ⟨a, ha, hca⟩ ⟨b, hb, hcb⟩ hbound)
      apply h₀
      exact ⟨z, (congrArg (fun q => q z) he).symm⟩
    · have he := congrArg Variety.Geometric.Morphism.hom
        (monomialProjectiveCurve_chart_one c n N ⟨a, ha, hca⟩ ⟨b, hb, hcb⟩ hbound)
      apply h₁
      exact ⟨z, (congrArg (fun q => q z) he).symm⟩
  let f := liftClosed i F hF
  have hfac : f.comp i = F := liftClosed_fac i F hF
  have : IsIso f.hom := normal_projective_monomial_curve_isIso_of_dimension_one
    hY hN hdim i c n N hNpos a b ha hb hca hcb hbound s has hcs hgcd f hfac
  refine ⟨(asIso f.hom).symm, ?_⟩
  change inv f.hom ≫ (projectiveLine k).structureMap = Y.structureMap
  rw [← f.commutes, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]

end Theory.AlgebraicGroup.Bor1.FlagCurve
