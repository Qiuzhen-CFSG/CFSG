module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.Setup.Parabolics.Model

/-!
# The finite parabolic identity for reverse displacement

For two distinct parabolics of the same type in the literal binary SL3,
intersect the first core with the second parabolic and join with the second
core. The required index is three. `ModelJoin` specifies this finite
mathematical obligation; it does not assert a constructor.

Its lift is proved in `Selection.Lifting`. The source selection may be
completed only after this remaining finite calculation has been proved.
Source: Meierfrankenfeld--Stellmacher (1993), (4.6.8), claim (1), printed p.905.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.ReverseSelection

/-- The finite same-type parabolic calculation required at the midpoint. -/
def ModelJoin (t : SL) (i : Bool) : Prop :=
  ∀ g : SL, let P := modelParabolic t i
    let P' := P.map (MulAut.conj g).toMonoidHom
    P' ≠ P → ((P.pCoreIn 2 ⊓ P') ⊔ P'.pCoreIn 2).relIndex P' = 3

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.ReverseSelection
