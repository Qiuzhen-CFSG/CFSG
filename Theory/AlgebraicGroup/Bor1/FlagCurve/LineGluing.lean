module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.ProjectiveCharts
public import Theory.AlgebraicGroup.Bor1.FlagCurve.OpenChartGluing

/-!
# Gluing reciprocal affine curves on the projective line

Two regular affine-line curves whose values agree for reciprocal nonzero
parameters glue to a morphism from the native projective line. The proof
uses its actual open cover, reduced overlap and closed-point extensionality.
This is the global parametrization step in Borel §13.13.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

noncomputable def projectiveLineAffineCover : (projectiveLine k).toScheme.OpenCover where
  I₀ := Fin 2
  X _ := (polynomialAffineLine k).toScheme
  f i := (projectiveLineChartInclusion (k := k) i).hom
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro x
    have hx : x ∈ ⨆ i : Fin 2, projectiveLineChartOpen k i := by
      rw [iSup_projectiveLineChartOpen_eq_top]
      trivial
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
    refine ⟨i, ?_⟩
    change x ∈ (projectiveLineChartInclusion (k := k) i).hom.opensRange
    rwa [projectiveLineChartInclusion_opensRange]

theorem line_chart_compatibility
    {Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (f : Fin 2 → Morphism (polynomialAffineLine k) Y)
    (h : ∀ a : k, a ≠ 0 → f 0 (affinePoint a) = f 1 (affinePoint a⁻¹))
    (i j : Fin 2) :
    pullback.fst (projectiveLineChartInclusion (k := k) i).hom
      (projectiveLineChartInclusion (k := k) j).hom ≫ (f i).hom =
    pullback.snd (projectiveLineChartInclusion (k := k) i).hom
      (projectiveLineChartInclusion (k := k) j).hom ≫ (f j).hom := by
  apply open_chart_compatible_of_points (projectiveLineChartInclusion i)
    (projectiveLineChartInclusion j) (f i) (f j)
  intro u v huv
  by_cases hij : i = j
  · subst j
    have huv' : u = v := by
      apply Subtype.ext
      exact (cancel_mono (projectiveLineChartInclusion (k := k) i).hom).mp
        (congrArg Subtype.val huv)
    rw [huv']
  · obtain ⟨a, rfl⟩ := affinePoint_surjective u
    obtain ⟨b, rfl⟩ := affinePoint_surjective v
    fin_cases i <;> fin_cases j
    · exact False.elim (hij rfl)
    · obtain ⟨ha, rfl⟩ := projectiveLineChart_coordinates_inverse a b huv
      exact h a ha
    · obtain ⟨hb, rfl⟩ := projectiveLineChart_coordinates_inverse b a huv.symm
      exact (h b hb).symm
    · exact False.elim (hij rfl)

noncomputable def glueProjectiveLine
    {Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (f : Fin 2 → Morphism (polynomialAffineLine k) Y)
    (h : ∀ a : k, a ≠ 0 → f 0 (affinePoint a) = f 1 (affinePoint a⁻¹)) :
    Morphism (projectiveLine k) Y where
  hom := projectiveLineAffineCover.glueMorphisms (fun i => (f i).hom)
    (line_chart_compatibility f h)
  commutes := by
    apply projectiveLineAffineCover.hom_ext
    intro i
    rw [Scheme.Cover.ι_glueMorphisms_assoc]
    exact (f i).commutes.trans (projectiveLineChartInclusion (k := k) i).commutes.symm

theorem glueProjectiveLine_chart
    {Y : Theory.AlgebraicGroup.Variety.Geometric k}
    (f : Fin 2 → Morphism (polynomialAffineLine k) Y)
    (h : ∀ a : k, a ≠ 0 → f 0 (affinePoint a) = f 1 (affinePoint a⁻¹)) (i : Fin 2) :
    (projectiveLineChartInclusion (k := k) i).comp (glueProjectiveLine f h) = f i := by
  apply Morphism.ext
  change (projectiveLineAffineCover (k := k)).f i ≫
    (projectiveLineAffineCover (k := k)).glueMorphisms (fun i => (f i).hom)
      (line_chart_compatibility f h) = (f i).hom
  exact (projectiveLineAffineCover (k := k)).ι_glueMorphisms (fun i => (f i).hom)
    (line_chart_compatibility f h) i

end Theory.AlgebraicGroup.Bor1.FlagCurve
