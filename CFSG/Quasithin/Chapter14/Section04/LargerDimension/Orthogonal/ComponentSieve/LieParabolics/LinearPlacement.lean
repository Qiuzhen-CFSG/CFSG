module

public import CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics.Basic
public import Theory.SpecificGroups.PSL3.LinearThreeFlags.ParabolicResiduals
public import Theory.SpecificGroups.PSL3.CartanActions.BorelQuotient

/-!
# Affine residuals of the actual linear-three parabolics

A maximal subgroup containing a Sylow two-normalizer in SL₃(4) or PSL₃(4)
can be conjugated to a standard Borel overgroup. Borel-overgroup coverage
and maximality identify it with the full point or line parabolic. Its
solvable residual is the corresponding perfect local factor, whose existing
coordinates give the special affine plane F² ⋊ SL₂(F).

The projective case uses the genuine central quotient and its proved
injectivity on the local factors. Finally, an actual ambient isomorphism
transports the embedded residual back to the group in `LinearFamily`.
This supplies the linear placement used by the natural-action obstruction;
the other three Lie families remain with the enclosing assembly.

Source: Aschbacher–Smith, A.3.14(1), printed pp.49–50, and Lemma 14.4.9,
printed p.1010, combined manuscript of 1 March 2004.
-/

public section
open Subgroup
open scoped MatrixGroups

noncomputable section
namespace CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics
open Chapter1.Section02
open Matrix.PSL3.LinearThree Matrix.PSL3.LinearThree.ParabolicResiduals
open Matrix.PSL3.CartanActions.BorelQuotient

private def residualMap {L M : Type*} [Group L] [Group M] [Finite L]
    (P : Subgroup L) (e : L ≃* M) :
    embeddedResidual P ≃* embeddedResidual (P.map e.toMonoidHom) :=
  (e.subgroupMap (embeddedResidual P)).trans
    (MulEquiv.subgroupCongr (embeddedResidual_map P e))

/-- Both classes of maximal parabolics in SL₃(4) have the special affine plane
as their solvable residual, embedded in the original matrix group. -/
theorem linearSL_residual_affine (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 4) (P : Subgroup SL(3,F))
    (hP : LieParabolicTwo P) (hmax : IsCoatom P) :
    Nonempty (embeddedResidual P ≃* Matrix.SL2.Affine F) := by
  obtain ⟨T, hT⟩ := hP
  obtain ⟨g, _, hg⟩ := sylowSL_normalizer_conjugate F (n := 2) (by decide) hF T
  let e := (MulAut.conj g).symm
  have hB : borelSL F ≤ P.map e.toMonoidHom := by
    have h := map_mono (f := e.toMonoidHom) (hg.le.trans hT)
    simpa [e, Subgroup.map_map] using h
  have hm : IsCoatom (P.map e.toMonoidHom) := (OrderIso.isCoatom_iff e.mapSubgroup P).mpr hmax
  rcases coatom_over_borelSL F _ hB hm with hp | hp
  · have hr : embeddedResidual (P.map e.toMonoidHom) = pointLocalSL F := by
      rw [hp]
      exact pointParabolicSL_residual F (by omega)
    exact ⟨(residualMap P e).trans
      ((MulEquiv.subgroupCongr hr).trans (pointLocalAffineEquiv F))⟩
  · have hr : embeddedResidual (P.map e.toMonoidHom) = lineLocalSL F := by
      rw [hp]
      exact lineParabolicSL_residual F (by omega)
    exact ⟨(residualMap P e).trans
      ((MulEquiv.subgroupCongr hr).trans (lineLocalAffineEquiv F))⟩

/-- Both classes of maximal parabolics in PSL₃(4) have the special affine plane
as their solvable residual; only the local factors are lifted injectively. -/
theorem linearPSL_residual_affine (F : Type*) [Field F] [Finite F]
    (hF : Nat.card F = 4) (P : Subgroup PSL(3,F))
    (hP : LieParabolicTwo P) (hmax : IsCoatom P) :
    Nonempty (embeddedResidual P ≃* Matrix.SL2.Affine F) := by
  obtain ⟨T, hT⟩ := hP
  obtain ⟨g, _, hg⟩ := sylow_normalizer_conjugate F (n := 2) (by decide) hF T
  let e := (MulAut.conj g).symm
  have hB : borel F ≤ P.map e.toMonoidHom := by
    have h := map_mono (f := e.toMonoidHom) (hg.le.trans hT)
    simpa [e, Subgroup.map_map] using h
  have hm : IsCoatom (P.map e.toMonoidHom) := (OrderIso.isCoatom_iff e.mapSubgroup P).mpr hmax
  rcases coatom_over_borel F _ hB hm with hp | hp
  · have hr : embeddedResidual (P.map e.toMonoidHom) = pointLocal F := by
      rw [hp]
      exact pointParabolic_residual F (by omega)
    exact ⟨(residualMap P e).trans
      ((MulEquiv.subgroupCongr hr).trans (pointLocalEquivAffine F))⟩
  · have hr : embeddedResidual (P.map e.toMonoidHom) = lineLocal F := by
      rw [hp]
      exact lineParabolic_residual F (by omega)
    exact ⟨(residualMap P e).trans
      ((MulEquiv.subgroupCongr hr).trans (lineLocalEquivAffine F))⟩

/-- The linear-three alternatives of A.3.14(1) give the actual affine-plane
residual, for either class of maximal parabolic. This is the placement input
to the natural-conjugation-action obstruction in Lemma 14.4.9. -/
theorem linearFamily_residual_affine {L : Type*} [Group L] [Finite L]
    (hL : LinearFamily L) (P : Subgroup L)
    (hP : LieParabolicTwo P) (hmax : IsCoatom P) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
      Nonempty (embeddedResidual P ≃* Matrix.SL2.Affine F) := by
  rcases hL with hL | hL
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
    obtain ⟨a⟩ := linearPSL_residual_affine F hF (P.map e.toMonoidHom)
      (parabolic_map hP e) ((OrderIso.isCoatom_iff e.mapSubgroup P).mpr hmax)
    exact ⟨F, inferInstance, inferInstance, hF, ⟨(residualMap P e).trans a⟩⟩
  · obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hL
    obtain ⟨a⟩ := linearSL_residual_affine F hF (P.map e.toMonoidHom)
      (parabolic_map hP e) ((OrderIso.isCoatom_iff e.mapSubgroup P).mpr hmax)
    exact ⟨F, inferInstance, inferInstance, hF, ⟨(residualMap P e).trans a⟩⟩

end CFSG.Quasithin.Chapter14.Section04.LargerDimension.Orthogonal.ComponentSieve.LieParabolics
