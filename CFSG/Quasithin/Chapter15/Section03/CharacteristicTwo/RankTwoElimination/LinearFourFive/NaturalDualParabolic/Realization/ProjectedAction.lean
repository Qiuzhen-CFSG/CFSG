module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ProjectedAction.Coordinates
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ModelGeometry
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ProjectedAction.ProjectionSupport

/-!
# The projected-centre action in a point parabolic

The two-group S ∩ L fixes a nonzero point of the marked plane. The actual
image of O²(Y₊ ∩ P) is the two-residual of the plane-theta intersection with
that point stabilizer. Its fixed covector space is zero, so the nonzero dual
coordinate of the projected centre forces the ambient commutator to be
nontrivial.

The support calculation retains both choices of Hypothesis 15.3.10 and the
full central supplement. The final theorem discharges both model fixed-space
calculations and the projected support premise. Its remaining explicit inputs
are the earlier local conclusions, the actual natural-plus-dual and plane
markings, and the exact splitting. The subsequent MS-pair assembly remains
with the consumer.

Source: Aschbacher–Smith, combined manuscript (1 March 2004),
15.3.24, printed pp.1129–1130.
-/

@[expose] public section

open Subgroup BinaryLinear.OuterCyclic
open BinaryNaturalDual.VectorStabilizers.Pure
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ProjectedAction
open Preparation
variable {G : Type*} [Group G] {d : LocalData G}

/-- Conditional assembly only: both the model fixed-space calculation and
nonzero dual projection remain premises to be constructed. -/
theorem exists_point_of_dual_support [Finite G] {I : Subgroup G}
    (c : ComponentWitness d I) (h : NaturalDual d c.L)
    (plane : PlaneParabolic d c.L h.model)
    (hYL : d.Yplus ≤ c.L) (hθ : theta (d.MI I) = d.Yplus)
    (hfixed : ∀ x : Space 4, x ∈ plane.plane → x ≠ 0 →
      ∀ f : Module.Dual (ZMod 2) (Space 4),
        (∀ g ∈ Stellmacher.twoResidualAmbient
          (theta (BinaryLinear.parabolic plane.plane) ⊓ pointStabilizer x),
          g.symm.dualMap f = f) → f = 0)
    (hdual : ∃ u : spanCommutator d c.L, (u : G) ∈ projectedCenter d c.L ∧
      (h.coordinates u).toAdd.2 ≠ 0) :
    ∃ x : Space 4, x ≠ 0 ∧ d.S ⊓ c.L ≤ point h x ∧
      ⁅projectedCenter d c.L, Stellmacher.twoResidualAmbient (d.Yplus ⊓ point h x)⁆ ≠ ⊥ := by
  obtain ⟨x, hxW, hx, hS⟩ := exists_plane_point h plane
  refine ⟨x, hx, hS, ?_⟩
  intro hz
  obtain ⟨u, hu, hune⟩ := hdual
  have hf := (commutator_eq_bot_iff_coordinates h inf_le_left
    (show Stellmacher.twoResidualAmbient (d.Yplus ⊓ point h x) ≤ c.L from
      (map_subtype_le _).trans (inf_le_right.trans (point_le h x)))).mp hz u hu
  rw [modelImage_point_residual_plane c h plane hYL hθ x] at hf
  apply hune
  apply hfixed x hxW hx
  intro g hg
  apply LinearMap.ext
  intro v
  have hv := congrArg (fun w => w.2 v) (hf g hg)
  simpa only [BinaryLinear.NaturalDualFlag.action_snd, LinearEquiv.dualMap_apply] using hv

/-- The point-action assertion in the natural-plus-dual paragraph of 15.3.24.
The explicit earlier inputs are elementarity of W_L from 15.3.16(1),
Y₊ ≤ L from 15.3.17(2), θ(M ∩ I) = Y₊ from 15.3.11(6),
O₂(L) ≤ R ≤ C_G(V) from 15.3.12(1) and 15.3.11(5i),
V = ⟨Z^Y⟩ from 15.3.7, and the second-choice normalizer bound from
15.3.11(3). The splitting is the displayed U_L Z = U_L C_{U_L Z}(L)
on p.1129. No fixed-space, moving-vector, or projected-action premise remains. -/
theorem exists_point [Finite G] {I : Subgroup G}
    (c : ComponentWitness d I) (h : NaturalDual d c.L)
    (plane : PlaneParabolic d c.L h.model)
    [IsElementaryAbelian 2 (d.componentSpan c.L)]
    (hYL : d.Yplus ≤ c.L) (hθ : theta (d.MI I) = d.Yplus)
    (hcore : c.L.pCoreIn 2 ≤ d.R) (hR : d.R ≤ centralizer (d.V : Set G))
    (hspan : localSpan d.Z d.Y = d.V)
    (hsplit : spanCommutator d c.L ⊔ d.Z =
      spanCommutator d c.L ⊔ centralSupplement d c.L)
    (hnormalizer : OutsideStructure.SecondChoice d → normalizer (d.V₁ : Set G) ≤ d.M) :
    ∃ x : Space 4, x ≠ 0 ∧ d.S ⊓ c.L ≤ point h x ∧
      ⁅projectedCenter d c.L, Stellmacher.twoResidualAmbient (d.Yplus ⊓ point h x)⁆ ≠ ⊥ := by
  apply exists_point_of_dual_support c h plane hYL hθ
  · exact ModelGeometry.theta_point_residual_dual_fixed_eq_zero plane.plane plane.dimension
  · exact ProjectionSupport.exists_nonzero_dual_support c h plane hYL hθ hcore hR
      hspan hsplit hnormalizer
      (ModelGeometry.theta_naturalDual_fixed_eq_zero plane.plane plane.dimension)

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankTwoElimination.LinearFourFive.NaturalDualParabolic.Realization.ProjectedAction

end
