module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.BinaryAuxiliary.Structure.Core.Reductions

/-!
# The midpoint comparison in MS93 (4.6.8)

The comparison uses the actual midpoint conjugation, a flag in its incident
pencil, and the original X_delta0. Its conclusions retain the two distinct
vertex centers and both original core embeddings. They are intermediate
geometric conclusions on p.907, not hypotheses of the source theorem.

`MiddleComparison` has no constructor from the source data here. The cross
commutator assembly must construct it before using the conditional first
and second layer deductions.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), (4.6.8), final two paragraphs of printed p.907.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
variable {M : Type*} [Group M] {L R : Subgroup M}

/-- The genuine comparison of X_delta0 and the midpoint-conjugated X_lambda0.
The two cross-commutator conclusions are not fields of this record. -/
structure MiddleComparison (source : LocalSource L R) (geometry : Geometry R)
    (i : Bool) (p : SourceFlagPreparatoryData source geometry i) where
  transport : MiddleTransport p.middle
  flag : M
  incident : flagIncident source i 1 flag
  crossing : ¬ X source i p.delta0 ≤
    (localFlagKernel source (!i) flag).map transport.conjugation.toMonoidHom
  center_action :
    ⁅Z R (alpha R), (flagParabolic source i).map transport.conjugation.toMonoidHom⁆ ≤
      Z R p.middle
  X_le_original_core :
    (X source i flag).map transport.conjugation.toMonoidHom ≤
      localFlagKernel source (!i) p.delta0
  X_commutator :
    ⁅X source i p.delta0, (X source i flag).map transport.conjugation.toMonoidHom⁆ ≤
      Z R (alpha R)
  center_le_X : Z R (alpha R) ≤ (X source i flag).map transport.conjugation.toMonoidHom

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.BinaryAuxiliary
