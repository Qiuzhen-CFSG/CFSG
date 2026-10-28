module

public import CFSG.Quasithin.ChapterG.Section02.LinearThree.Structure.Radical.Geometry.ParabolicCore
public import Theory.SpecificGroups.PSL3.PointRadicalGeneration.FrameGeneration

/-!
# The original marked triple generates L* in G.2.5

The original g and h give three independent lines in the supplied natural
SL₃ model. Their full point radicals therefore generate the matrix group.
The proved parabolic minimality theorem identifies U* with the first radical;
right conjugation transports its two marked conjugates to the radicals at the
inverse-matrix translates. Lifting generation through the literal star quotient
gives I* = L* for the original I = ⟨U,Uᵍ,Uʰ⟩.

Together with the publicly imported `ParabolicCore` results, this completes the
conditional point-radical contract: U* = O₂(N_L(V₁)*), an explicit isomorphism
U* ≃ additive F², |U*| = 2^(2n), and I* = L*. Only U ≤ T, Φ(U) ≤ V₁ and
U* ≤ L* remain as premises. The source assembly discharges the latter separately;
no model generation or minimality premise remains. The argument includes n = 1.

Source: Aschbacher–Smith, G.2.5(1–2), printed pp.335–336 / PDF pp.346–347,
with the full-normalizer argument of G.2.3, printed pp.333–334.
-/

public section
open Subgroup Matrix
open scoped MatrixGroups
namespace CFSG.Quasithin.ChapterG.Section02.LinearThree
open Setup Matrix.PSL3.PointRadicalGeneration
namespace Hypothesis
variable {G : Type*} [Group G] [Finite G]
variable {D : Setup G} {F : Type*} [Field F] [Finite F]
  {n : ℕ} {g h : G} (d : Hypothesis D F n g h)

include d

/-- Generation at the three original marked lines, using inverse matrices for
the source's right conjugation convention. -/
theorem model_pointRadicals_generate :
    (radical d.point ⊔
      radical (conjugatePoint d.point (d.model (starProjection D ⟨g,d.g_mem⟩)))) ⊔
      radical (conjugatePoint d.point (d.model (starProjection D ⟨h,d.h_mem⟩))) = ⊤ := by
  apply radical_sup_sup_eq_top
  · exact d.point_dimension
  · rw [conjugatePoint_finrank]
    exact d.point_dimension
  · rw [conjugatePoint_finrank]
    exact d.point_dimension
  · exact d.model_points_disjoint
  · exact d.model_third_disjoint
  · exact d.model_points_span

/-- The starred generation step of G.2.5(2), with every concrete model premise
discharged and the original g, h and I retained. -/
theorem star_I_eq_star_L_of_linear_image (hUT : D.U ≤ D.T)
    (hf : (frattini D.U).map D.U.subtype ≤ D.V₁)
    (hUL : D.star D.U ≤ D.star D.L) :
    D.star (I D g h) = D.star D.L :=
  d.star_I_eq_star_L_of_point_model_generation hUT hf hUL
    (radical_minimal d.point d.point_dimension) d.model_pointRadicals_generate

end Hypothesis
end CFSG.Quasithin.ChapterG.Section02.LinearThree
