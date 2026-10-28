module
public import CFSG.Quasithin.Chapter15.Section04.Centralizer.InitialSource.BaumannSylow.ResidualLift
public import CFSG.Quasithin.Chapter15.Section04.Configuration.LocalSetup.SylowGeometry.SourceWitnesses.MarkedProduct.AlphaFromAction

/-!
# The two-plane Baumann Sylow application

The original orthogonal action, including its actual residual and Thompson
images, supplies every premise of B.2.18. Its alpha decomposition and the
odd residual image yield the Sylow conclusion of B.6.10. No alpha or
Sylow conclusion is included among the action hypotheses.

Source: Aschbacher--Smith B.6.10 and15.4.11, printed pp.117 and1160.
-/

@[expose] public section
open Subgroup Stellmacher
open OrthogonalFourBinary.TerminalLines
open OrthogonalFourBinary.SylowGeometry
namespace CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
open LocalSetup.SourceWitnesses.MarkedProduct
open FamilySource.ModuleStructure.BaumannPair
open ChapterB
variable {G : Type*} [Group G] [Finite G]

theorem sylow_from_two_planes (R : Sylow 2 G) (W : Subgroup G)
    [W.Normal] [IsElementaryAbelian 2 W] (d : Action W)
    (hWR : W ≤ (R : Subgroup G)) (hk : IsPGroup 2 d.actor.ker)
    (hL : (pResidual 2 G).map d.actor = rotations)
    (hJbase : (elementaryAbelianMaxJ (R : Subgroup G)).map d.actor ≤ base)
    (hJcard : Nat.card ((elementaryAbelianMaxJ (R : Subgroup G)).map d.actor) = 4) :
    Chapter1.IsSylowIn 2 (baumann (R : Subgroup G))
      (pResidual 2 G ⊔ baumann (R : Subgroup G)) := by
  have hp : IsPGroup 3 ((pResidual 2 G).map d.actor) :=
    hL.symm ▸ IsPGroup.of_card (n := 2) Concrete.rotations_card
  exact sylow_of_alpha R W d.actor hk (Action.kernel d) hp
    (alpha_decomposition_from_action R W d hWR hk hL hJbase hJcard)

end CFSG.Quasithin.Chapter15.Section04.InitialSource.BaumannSylow
