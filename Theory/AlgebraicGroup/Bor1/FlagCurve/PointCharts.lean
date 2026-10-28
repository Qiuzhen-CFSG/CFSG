module

public import Theory.AlgebraicGroup.Bor1.FlagCurve.ProjectiveCharts
public import Theory.AlgebraicGroup.Variety.GeometricClosedImage

/-!
# Rational points of the two projective-line charts

Every rational point lies in one native affine chart, and nonzero parameters
change by inversion on the overlap. These exact point formulas are used to
prove injectivity of the global normal monomial parametrization.
-/

public noncomputable section

open scoped LinearAlgebra.Projectivization

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Theory.AlgebraicGroup.Variety.Geometric
open Theory.AlgebraicGroup.Variety.Geometric.ProjectivePolynomialCurve
namespace Theory.AlgebraicGroup.Bor1.FlagCurve
universe u
variable {k : Type u} [Field k] [IsAlgClosed k]

theorem projectiveLine_point_chart (p : Point (projectiveLine k)) :
    ∃ i : Fin 2, ∃ a : k, projectiveLineChartInclusion (k := k) i (affinePoint a) = p := by
  have hx : p.1 (IsLocalRing.closedPoint k) ∈ ⨆ i : Fin 2, projectiveLineChartOpen k i := by
    rw [iSup_projectiveLineChartOpen_eq_top]
    trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have hr : p.1 (IsLocalRing.closedPoint k) ∈
      Set.range (projectiveLineChartInclusion (k := k) i).hom := by
    change p.1 (IsLocalRing.closedPoint k) ∈
      (projectiveLineChartInclusion (k := k) i).hom.opensRange
    rwa [projectiveLineChartInclusion_opensRange]
  obtain ⟨q, hq⟩ := ((projectiveLineChartInclusion (k := k) i).point_mem_range_iff_closedPoint_mem_range p).mpr hr
  obtain ⟨a, rfl⟩ := affinePoint_surjective q
  exact ⟨i, a, hq⟩

theorem projectiveLine_chart_reciprocal (a : k) (ha : a ≠ 0) :
    projectiveLineChartInclusion (k := k) 0 (affinePoint a) =
      projectiveLineChartInclusion (k := k) 1 (affinePoint a⁻¹) := by
  rw [projectiveLineChartInclusion_point, projectiveLineChartInclusion_point]
  apply (projectivePointOfVector_eq_iff_mk_eq _ _ _ _).mpr
  apply (Projectivization.mk_eq_mk_iff' k _ _ _ _).mpr
  refine ⟨a, ?_⟩
  funext i
  fin_cases i <;> simp [Pi.smul_apply, smul_eq_mul, ha]

end Theory.AlgebraicGroup.Bor1.FlagCurve
