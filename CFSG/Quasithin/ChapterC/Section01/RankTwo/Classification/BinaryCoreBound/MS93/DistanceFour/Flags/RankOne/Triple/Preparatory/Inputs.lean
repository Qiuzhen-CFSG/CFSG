module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Critical
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple.Preparatory.Layers

/-!
# Remaining local claims for the preparatory flag configuration

The critical midpoint and endpoint are constructed in `Critical`. The two
remaining mathematical arguments on printed p.906 can be developed separately:
claim (2) propagates a commutator containment from that midpoint, while claims
(3)--(4) select incident flags and prove displacement using that propagation.

`FlagPropagation` states claim (2) for an already constructed critical pair.
`FlagLocalData` records the incident choices and claims (3)--(4), with all
actors and layers from `Triple.Geometry`. Neither has a proof or constructor
here. Their eventual assembly must discharge both obligations before asserting
`FlagPreparatoryData`; in particular, naturality alone is not a constructor.

Source: Meierfrankenfeld--Stellmacher, *Pushing up weak BN-pairs of rank two*
(1993), numbered claims (2)--(4) and the intervening selections, printed p.906.
-/

@[expose] public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
variable {M : Type*} [Group M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R} {i : Bool}

/-- Numbered claim (2), still to be proved using the actual commutator pairing. -/
def FlagPropagation (p : FlagCriticalData source geometry i) : Prop :=
  ⁅Z R p.middle, Q R (alpha R)⁆ ≤ U R (alpha R) →
    ∀ t, nu R geometry (alpha R) t → ⁅Z R t, Q R (alpha R)⁆ ≤ U R (alpha R)

/-- The remaining incident choices and claims (3)--(4), as explicit proof targets.
The displacement proof may take `FlagPropagation p` as an intermediate premise;
final assembly must prove that premise separately. -/
structure FlagLocalData (p : FlagCriticalData source geometry i) where
  delta2 : M
  delta2_neighbor : flagIncident source i 1 delta2
  endpoint_crosses : ¬ Z R p.endpoint ⊓ localFlagKernel source (!i) delta2 ≤ Q R (alpha R)
  second_triple : ¬ ⁅⁅V R (beta R), localFlagKernel source (!i) delta2⁆,
    localFlagResidual source (!i) delta2⁆ ≤ Z R (alpha R)
  delta0 : M
  delta0_neighbor : flagIncident source i 1 delta0
  endpoint_not_le : ¬ Z R p.endpoint ≤ localFlagKernel source (!i) delta0
  intersection_commutator :
    ⁅Z R p.middle ⊓ secondFlagLayer source i delta0, localFlagActor source (!i) delta0⁆ ≤
      localFlagZ source (!i) delta0
  middle_not_le : ¬ Z R p.middle ≤ secondFlagLayer source i delta0
  displacement : 2 ≤ (Q R p.middle).relIndex (secondFlagLayer source i delta0)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne
