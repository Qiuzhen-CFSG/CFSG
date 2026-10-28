module

public import Theory.Representation.G2BinaryPlaneOrbits
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.CentralCover.BlockModels.Marking

/-!
# The intrinsic Sylow route to the marked G₂ coefficient plane

The lower-layer standard plane is literally the marked plane of the source
block model. The adapter supplies the exact compatible actor and coefficient
maps requested by the G₂ source assembly. The intrinsic Sylow uniqueness and
quotient-plane stabilizer calculations discharge every geometric premise.

Source: Aschbacher–Smith, proof of 15.3.31, printed p.1132 (PDF p.1149),
C.1.30 and B.5.3–6. Only the coefficient marking is imported, so this adapter
can be consumed by the source assembly without an import cycle.
-/

@[expose] public noncomputable section
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly.G2PlaneGeometry
open CentralCover CentralCover.BlockModels
open Atlas.G2.Natural.BinaryPlane

/-- The lower-layer null-plane marking agrees with the source marking. -/
theorem standardPlane_eq_markedPlane : standardPlane = G2.markedPlane := rfl

/-- The exact geometry interface of the source assembly, with the two
independent intrinsic Sylow calculations still explicit. -/
theorem geometry_of_standardSylow
    (uniquePlane : ∀ W : Submodule (ZMod 2) G2.Coefficients,
      Nat.card W = 4 → (standardSylow : Subgroup G2.Actor) ≤
        BlockModels.planeStabilizer G2.action W → W = G2.markedPlane)
    (stabilizerCard : Nat.card (BlockModels.planeStabilizer G2.action G2.markedPlane) = 96)
    (W : Submodule (ZMod 2) G2.Coefficients) (P : Subgroup G2.Actor)
    (hW : Nat.card W = 4) (hP : Nat.card P = 96)
    (hPW : P ≤ BlockModels.planeStabilizer G2.action W) :
    ∃ (f : G2.Actor ≃* G2.Actor) (e : G2.Coefficients ≃ₗ[ZMod 2] G2.Coefficients),
      (∀ a v, e (G2.action a v) = G2.action (f a) (e v)) ∧
      W.map e.toLinearMap = G2.markedPlane ∧
      P.map f.toMonoidHom = BlockModels.planeStabilizer G2.action G2.markedPlane :=
  plane_geometry_of_standardSylow uniquePlane stabilizerCard W P hW hP hPW

/-- The universal intrinsic geometry input of
`MarkedModelAssembly.g2_marked_models_of_plane_geometry`, with no additional
orbit, placement, parabolic, or generation premise. -/
theorem geometry (W : Submodule (ZMod 2) G2.Coefficients) (P : Subgroup G2.Actor)
    (hW : Nat.card W = 4) (hP : Nat.card P = 96)
    (hPW : P ≤ BlockModels.planeStabilizer G2.action W) :
    ∃ (f : G2.Actor ≃* G2.Actor) (e : G2.Coefficients ≃ₗ[ZMod 2] G2.Coefficients),
      (∀ a v, e (G2.action a v) = G2.action (f a) (e v)) ∧
      W.map e.toLinearMap = G2.markedPlane ∧
      P.map f.toMonoidHom = BlockModels.planeStabilizer G2.action G2.markedPlane :=
  plane_geometry W P hW hP hPW

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedModelAssembly.G2PlaneGeometry
