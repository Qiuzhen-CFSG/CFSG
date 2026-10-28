module

public import Theory.SpecificGroups.PSL3.RootPlaneGeometry

/-!
# Properness of the full projective point and line stabilizers

The elementary matrix with a nonzero (2,0) entry moves both the standard
point and the standard line. The exact preimages of the projective
stabilizers therefore show that both full parabolics are proper.
Source: the natural projective geometry of PSL₃; Aschbacher--Smith,
15.3.43(e), printed p.1140.
-/

public section
open scoped MatrixGroups
open Matrix Matrix.PSL3.LinearThree
namespace Matrix.PSL3.RootPlaneGeometry
variable (F : Type*) [Field F] [Finite F]

/-- Both full projective flag parabolics are proper. -/
theorem parabolic_lt_top (point : Bool) : parabolic F point < ⊤ := by
  apply lt_top_iff_ne_top.mpr
  intro h
  let g : SL(3,F) := ⟨!![1,0,0; 0,1,0; 1,0,1], by simp [Matrix.det_fin_three]⟩
  have hg : projection F g ∈ parabolic F point := by rw [h]; trivial
  cases point
  · change g ∈ (lineParabolic F).comap (projection F) at hg
    rw [lineParabolic_comap] at hg
    have hz := ((mem_lineParabolicSL_iff F g).mp hg).1
    simp [g] at hz
  · change g ∈ (pointParabolic F).comap (projection F) at hg
    rw [pointParabolic_comap] at hg
    have hz := ((mem_pointParabolicSL_iff F g).mp hg).2
    simp [g] at hz

end Matrix.PSL3.RootPlaneGeometry
