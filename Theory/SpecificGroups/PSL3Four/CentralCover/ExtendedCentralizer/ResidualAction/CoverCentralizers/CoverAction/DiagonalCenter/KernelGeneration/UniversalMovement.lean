module

public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.KernelGeneration.ConcreteMovement
public import Theory.SpecificGroups.PSL3Four.CentralCover.ExtendedCentralizer.ResidualAction.CoverCentralizers.CoverAction.DiagonalCenter.KernelGeneration.BinaryCoordinates
/-!
# Transporting the concrete moved class to the canonical universal kernel

The universal comparison onto the proved permutation-matrix cover is
surjective and intertwines the compatible diagonal lifts, by perfectness.
A square displacement in the canonical kernel would therefore give a square
displacement of the concrete distinguished central word. Its checked
permutation coordinate excludes this. All maps use the literal matrix
PSL₃(4) quotient. Source: Aschbacher--Smith 15.3.38, printed p.1136.
-/

public section
open PerfectCentralCovering Subgroup Theory.GroupTheory
namespace Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
open PSL3.ExceptionalFourCover
open KernelModel.DiagonalWords

theorem universal_actor_moves_modulo_squares : ∃ z : (universalProjection PSL).ker,
    ¬ ∃ w : (universalProjection PSL).ker,
      w ^ 2 = universalKernelMap actor z * z⁻¹ := by
  let f := cover_isUniversal.lift realization
  have hf (g : UniversalGroup PSL) : KernelModel.projection (f g) =
      universalProjection PSL g :=
    congrArg (fun c : Covering CoverGroup PSL => c g) (cover_isUniversal.lift_fac realization)
  have hnat : f.toMonoidHom.comp (universalLift actor).toMonoidHom =
      liftedActor.toMonoidHom.comp f.toMonoidHom := by
    apply monoidHom_eq_of_isPerfect_of_comp_eq realization.toMonoidHom realization.ker_le_center
    ext g
    exact (hf _).trans ((universalLift_compatible actor g).trans
      ((congrArg actor (hf g)).symm.trans (liftedActor_compatible (f g)).symm))
  obtain ⟨g, hg⟩ := f.surjective KernelModel.CentralWords.elementA
  change f g = KernelModel.CentralWords.elementA at hg
  have hgker : g ∈ (universalProjection PSL).ker := by
    change universalProjection PSL g = 1
    rw [← hf, hg]
    exact KernelModel.CentralWords.projection_elementA
  refine ⟨⟨g, hgker⟩, ?_⟩
  rintro ⟨w, hw⟩
  apply liftedActor_moves_modulo_squares
  have hwker : f w ∈ KernelModel.projection.ker := by
    change KernelModel.projection (f w) = 1
    rw [hf]
    exact w.property
  refine ⟨⟨f w, hwker⟩, ?_⟩
  have h := congrArg (fun t : (universalProjection PSL).ker => f t) hw
  change f ((w : UniversalGroup PSL) ^ 2) =
    f (universalLift actor g * g⁻¹) at h
  rw [map_pow, map_mul, map_inv] at h
  have hn := DFunLike.congr_fun hnat g
  change f (universalLift actor g) = liftedActor (f g) at hn
  rw [hn, hg] at h
  exact h
end Matrix.PSL3Four.ExtendedCentralizer.CoverCentralizers.DiagonalCenter
