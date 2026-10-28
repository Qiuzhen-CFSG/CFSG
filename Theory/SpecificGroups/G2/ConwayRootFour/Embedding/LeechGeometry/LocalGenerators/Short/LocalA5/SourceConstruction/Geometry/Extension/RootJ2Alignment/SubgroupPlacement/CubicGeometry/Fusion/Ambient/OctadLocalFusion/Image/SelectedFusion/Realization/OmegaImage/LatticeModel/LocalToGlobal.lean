module

public import Theory.SpecificGroups.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.Short.LocalA5.SourceConstruction.Geometry.Extension.RootJ2Alignment.SubgroupPlacement.CubicGeometry.Fusion.Ambient.OctadLocalFusion.Image.SelectedFusion.Realization.OmegaImage.LatticeModel.Reduction
public import Theory.SpecificGroups.ClassicalOrthogonal.SplitOdd.BinaryEightObstruction.Simplicity.Geometry

/-!
# Recovering the octad orthogonal image from its local action

A subgroup of the split binary orthogonal group is Omega if it is transitive
on nonzero singular vectors and its stabilizer of one such vector is exactly
the Omega stabilizer. The local stabilizer contains every Siegel transformation
with that singular direction; transitivity and covariance give every Siegel
generator. Omega's own transitivity then gives the reverse inclusion.

This is the assembly step for the monomial octad stabilizer and sextet orbit
calculations in Aschbacher, *Sporadic Groups* (1994), 25.5(7), p.134.
No group-order recognition is used.
-/

@[expose] public noncomputable section
open Theory.AlgebraicGroup
open ClassicalOrthogonal ClassicalOrthogonal.Quadratic

namespace Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
namespace Realization.OmegaImage.LatticeModel

private def asIsometry (g : SelectedGeometry.Orthogonal) :
    SelectedGeometry.form.IsometryEquiv SelectedGeometry.form :=
  { g.val with map_app' := (mem_quadraticIsometrySubgroup _ _).mp g.prop }

/-- The local stabilizer and singular orbit determine the literal elementary
subgroup, via the covariance of Siegel generators. -/
theorem eq_omega_of_singular_orbit_and_stabilizer
    (R : Subgroup SelectedGeometry.Orthogonal)
    (v : SelectedGeometry.Space) (hv0 : v ≠ 0) (hv : SelectedGeometry.form v = 0)
    (hOrbit : ∀ w : SelectedGeometry.Space, w ≠ 0 → SelectedGeometry.form w = 0 →
      ∃ g : R, g.val.val v = w)
    (hStabilizer : ∀ g : SelectedGeometry.Orthogonal, g.val v = v →
      (g ∈ R ↔ g ∈ SelectedGeometry.omega)) :
    R = SelectedGeometry.omega := by
  have hle : SelectedGeometry.omega ≤ R := by
    apply (Subgroup.closure_le R).mpr
    rintro a ⟨u, w, hu, huw, rfl⟩
    by_cases hu0 : u = 0
    · subst u
      have he : siegelElement SelectedGeometry.form 0 w hu huw = 1 := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        change siegel SelectedGeometry.form 0 w x = x
        simp [siegel]
      rw [he]
      exact R.one_mem
    · obtain ⟨g, hg⟩ := hOrbit u hu0 hu
      let w' := g.val.val.symm w
      have hperp : SelectedGeometry.form.polarBilin v w' = 0 := by
        have hp := isometry_polar SelectedGeometry.form (asIsometry g.val) v w'
        change SelectedGeometry.form.polarBilin (g.val.val v) (g.val.val w') =
          SelectedGeometry.form.polarBilin v w' at hp
        rw [hg, LinearEquiv.apply_symm_apply] at hp
        exact hp.symm.trans huw
      let s := siegelElement SelectedGeometry.form v w' hv hperp
      have hs : s ∈ R := (hStabilizer s (siegel_fix _ _ _ hv hperp)).mpr
        (siegelElement_mem _ _ _ _ _)
      have hc : g.val * s * g.val⁻¹ = siegelElement SelectedGeometry.form u w hu huw := by
        apply Subtype.ext
        apply LinearEquiv.ext
        intro x
        change g.val.val (siegel SelectedGeometry.form v w' (g.val.val.symm x)) =
          siegel SelectedGeometry.form u w x
        have hh := siegel_covariant SelectedGeometry.form (asIsometry g.val)
          v w' (g.val.val.symm x)
        change g.val.val (siegel SelectedGeometry.form v w' (g.val.val.symm x)) =
          siegel SelectedGeometry.form (g.val.val v) (g.val.val w')
            (g.val.val (g.val.val.symm x)) at hh
        simpa only [hg, w', LinearEquiv.apply_symm_apply] using hh
      rw [← hc]
      exact R.mul_mem (R.mul_mem g.prop hs) (R.inv_mem g.prop)
  apply le_antisymm ?_ hle
  intro g hg
  let p : BinaryEightObstruction.Simplicity.Point := ⟨v, hv0, hv⟩
  let q : BinaryEightObstruction.Simplicity.Point := ⟨g.val v,
    fun h => hv0 (g.val.injective (h.trans (map_zero _).symm)),
    ((asIsometry g).map_app v).trans hv⟩
  let := BinaryEightObstruction.Simplicity.singular_pretransitive
  obtain ⟨a, ha⟩ := MulAction.exists_smul_eq
    (BinaryEightObstruction.Simplicity.E) p q
  have hav : a.val.val v = g.val v := congrArg Subtype.val ha
  have hf : (a.val⁻¹ * g).val v = v := by
    change a.val.val.symm (g.val v) = v
    rw [← hav, LinearEquiv.symm_apply_apply]
  have hh : a.val⁻¹ * g ∈ SelectedGeometry.omega :=
    (hStabilizer _ hf).mp (R.mul_mem (R.inv_mem (hle a.prop)) hg)
  simpa only [mul_inv_cancel_left] using
    SelectedGeometry.omega.mul_mem a.prop hh

end Realization.OmegaImage.LatticeModel
end Atlas.G2.ConwayRootFour.Embedding.LeechGeometry.LocalGenerators.LocalA5.SourceConstruction.CubicFusion.OctadRestriction
