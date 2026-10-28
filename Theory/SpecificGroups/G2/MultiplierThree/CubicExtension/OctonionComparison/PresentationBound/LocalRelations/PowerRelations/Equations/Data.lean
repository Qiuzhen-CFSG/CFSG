module

public import Theory.SpecificGroups.G2.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.PowerRelations.Equations.Data13

/-!
# Balanced lookup of the source-equation blocks

Every entry is proved in the subsequent equation blocks.
-/

@[expose] public section
namespace Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.PowerRelations.Certified
open Subgroup.CosetWordCertificate Replay

noncomputable section

def database (i : Nat) : Word Bool × Word Bool :=
  if i < 64 then dataBlock00 i else
  if i < 128 then dataBlock01 i else
  if i < 192 then dataBlock02 i else
  if i < 256 then dataBlock03 i else
  if i < 320 then dataBlock04 i else
  if i < 384 then dataBlock05 i else
  if i < 448 then dataBlock06 i else
  if i < 512 then dataBlock07 i else
  if i < 576 then dataBlock08 i else
  if i < 640 then dataBlock09 i else
  if i < 704 then dataBlock10 i else
  if i < 768 then dataBlock11 i else
  if i < 832 then dataBlock12 i else
  if i < 835 then dataBlock13 i else
  ([], [])

end
end Atlas.G2.FiniteCover.MultiplierThree.CubicExtension.OctonionComparison.PresentationBound.LocalRelations.PowerRelations.Certified
