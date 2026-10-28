module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.LineGluing
public import Theory.AlgebraicGroup.Variety.GeometricPointBijectivity
public import Theory.AlgebraicGroup.Bor1.FlagCurve.PointCharts

/-!
# Identifying a curve from its two affine-line charts

A dominant morphism from the projective line is an isomorphism if its two
standard chart maps are open immersions and their origins have distinct images.
Reciprocal coordinates give point injectivity; completeness gives surjectivity;
the chart immersions then establish the actual global scheme isomorphism.
This is the global part of the normal monomial-curve argument in Borel §13.13.
-/

public noncomputable section

open CategoryTheory AlgebraicGeometry
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

omit [IsAlgClosed k] in
private theorem point_injective_of_mono
    {X Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (f : Morphism X Y) [Mono f.hom] : Function.Injective f := by
  intro p q h
  apply Subtype.ext
  exact (cancel_mono f.hom).mp (congrArg Subtype.val h)

set_option backward.isDefEq.respectTransparency false in
theorem projectiveLine_isIso_of_open_charts
    {Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (f : Morphism (projectiveLine k) Y) [IsDominant f.hom]
    (hchart : ∀ i : Fin 2, IsOpenImmersion
      ((projectiveLineChartInclusion (k := k) i).hom ≫ f.hom))
    (hend : f (projectiveLineChartInclusion (k := k) 0 (affinePoint 0)) ≠
      f (projectiveLineChartInclusion (k := k) 1 (affinePoint 0))) : IsIso f.hom := by
  have : UniversallyClosed (f.hom ≫ Y.structureMap) := by
    rw [f.commutes]
    exact projectiveLine_isComplete
  have : UniversallyClosed f.hom := .of_comp_of_isSeparated f.hom Y.structureMap
  have : Surjective f.hom := surjective_of_isDominant_of_isClosed_range f.hom
    f.hom.isClosedMap.isClosed_range
  have hsurj : Function.Surjective (fun p : Point (projectiveLine k) => f p) := by
    intro y
    exact (f.point_mem_range_iff_closedPoint_mem_range y).mpr
      (f.hom.surjective (y.1 (IsLocalRing.closedPoint k)))
  have hfi (i : Fin 2) : Function.Injective
      ((projectiveLineChartInclusion (k := k) i).comp f) := by
    have : IsOpenImmersion ((projectiveLineChartInclusion (k := k) i).comp f).hom := hchart i
    exact point_injective_of_mono _
  have hpinj : Function.Injective (fun p : Point (projectiveLine k) => f p) := by
    intro p q hpq
    obtain ⟨i, a, rfl⟩ := projectiveLine_point_chart p
    obtain ⟨j, b, rfl⟩ := projectiveLine_point_chart q
    by_cases hij : i = j
    · subst j
      exact congrArg (projectiveLineChartInclusion (k := k) i) (hfi i hpq)
    · have hcross (a b : k)
          (he : f (projectiveLineChartInclusion (k := k) 0 (affinePoint a)) =
            f (projectiveLineChartInclusion (k := k) 1 (affinePoint b))) :
          projectiveLineChartInclusion (k := k) 0 (affinePoint a) =
            projectiveLineChartInclusion (k := k) 1 (affinePoint b) := by
        by_cases hb : b = 0
        · subst b
          by_cases ha : a = 0
          · subst a
            exact False.elim (hend he)
          · rw [projectiveLine_chart_reciprocal a ha] at he ⊢
            exact congrArg (projectiveLineChartInclusion (k := k) 1) (hfi 1 he)
        · have hj : projectiveLineChartInclusion (k := k) 1 (affinePoint b) =
              projectiveLineChartInclusion (k := k) 0 (affinePoint b⁻¹) := by
            simpa using (projectiveLine_chart_reciprocal b⁻¹ (inv_ne_zero hb)).symm
          rw [hj] at he ⊢
          exact congrArg (projectiveLineChartInclusion (k := k) 0) (hfi 0 he)
      fin_cases i <;> fin_cases j
      · exact False.elim (hij rfl)
      · exact hcross a b hpq
      · exact (hcross b a hpq.symm).symm
      · exact False.elim (hij rfl)
  have hbij := f.bijective_hom_of_bijective_points ⟨hpinj, hsurj⟩
  have : IsOpenImmersion f.hom := IsOpenImmersion.of_openCover_source f.hom
    projectiveLineAffineCover hbij.1 hchart
  exact (isIso_iff_isOpenImmersion_and_surjective f.hom).mpr ⟨inferInstance, inferInstance⟩

end Theory.AlgebraicGroup.Bor1.FlagCurve
