module

public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ResidualStructure.OrthogonalImage
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.OrthogonalLocal.Geometry.Transport
public import CFSG.Quasithin.Chapter15.Section03.Preliminaries.ComponentIntersection.Basic

/-!
# Fixed vectors of the orthogonal residual

A cubic matrix acts without nonzero fixed vectors on both binary planes.
It lies in the two-residual, so the full residual fixes only the identity.
The actual vector embedding transports this to C_V(Y).
Source: Aschbacher--Smith 15.3.7 and its use in 15.3.37--38.
-/

public section
open Subgroup Stellmacher

namespace CFSG.Quasithin.Chapter15.Section03

private def fixedCubicPlane : OrthogonalPlaneActor := ⟨!![0, 1; 1, 1], by decide⟩
private def fixedCubicActor : OrthogonalActor := ⟨fun _ => fixedCubicPlane, 1⟩

private theorem fixedCubicActor_cube : fixedCubicActor ^ 3 = 1 := by
  have h : fixedCubicPlane ^ 3 = 1 := by decide +kernel
  apply RegularWreathProduct.ext
  · funext i
    simpa [pow_succ, fixedCubicActor] using h
  · rfl

private theorem fixedCubicActor_mem :
    fixedCubicActor ∈ twoResidualAmbient (⊤ : Subgroup OrthogonalActor) := by
  rw [ComponentIntersection.twoResidualAmbient_eq_map_pResidual]
  refine ⟨⟨fixedCubicActor, mem_top _⟩, ?_, rfl⟩
  apply mem_pResidual_of_orderOf_coprime
  apply (by decide : Nat.Coprime 2 3).of_dvd_right
  exact orderOf_dvd_of_pow_eq_one (Subtype.ext fixedCubicActor_cube)

theorem orthogonalActor_residual_fixedVectors_eq_bot :
    OrthogonalGeometry.fixedVectors (twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) = ⊥ := by
  let _ := FourGroupMatrixCoordinates.naturalAction
  have hp : ∀ v : OrthogonalPlaneVector, fixedCubicPlane • v = v → v = 1 := by decide +kernel
  let _ := orthogonalAction
  apply le_bot_iff.mp
  intro v hv
  apply mem_bot.mpr
  funext i
  apply hp (v i)
  have he := congrFun (hv fixedCubicActor fixedCubicActor_mem) i
  simpa only [fixedCubicActor, RegularWreathProduct.functionModule_smul_apply,
    inv_one, one_mul] using he

theorem NaturalOrthogonalAction.fixedPlane_eq_bot_of_residual_image
    {G : Type*} [Group G] {M V Y : Subgroup G}
    (d : NaturalOrthogonalAction M V) (hYM : Y ≤ M)
    (himage : d.image Y = twoResidualAmbient (⊤ : Subgroup OrthogonalActor)) :
    fixedPlane V Y = ⊥ := by
  rw [d.fixedPlane_eq_map hYM, himage, orthogonalActor_residual_fixedVectors_eq_bot,
    Subgroup.map_bot]

end CFSG.Quasithin.Chapter15.Section03
