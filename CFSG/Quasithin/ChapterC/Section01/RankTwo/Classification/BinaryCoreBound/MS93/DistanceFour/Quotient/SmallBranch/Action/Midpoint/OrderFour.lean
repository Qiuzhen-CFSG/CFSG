module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.SmallBranch.Action.Midpoint.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed.Local.Geometry.Displacement
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Triple

/-!
# The midpoint actor has order four

Move the common neighbor of alpha and the critical midpoint to beta by an
element of the base stabilizer. The existing displacement calculation on
that edge gives order four for the literal projected midpoint radius group.
The actor order is the relative index of Q_alpha in that radius group;
conjugation preserves this index and fixes Q_alpha, giving the result for
the original segment.

The edge calculation uses critical escape, V_middle-prime = U_middle and
the marked flag control. It requires neither the large-intersection nor
the small-intersection branch. The source flag-control theorem constructs
the required control from the early facts already supplied by RadiusFacts,
discharging the remaining premise in `midpointActor_card_four`.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.9), printed p.908, and the opening index calculation of
(4.6.11), printed p.909. The midpoint is alpha+2.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
    (source : LocalSource L R) (geometry : Geometry R)
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)

include common radius in
/-- The marked flag displacement calculation gives order four for every
critical midpoint, independently of the small-intersection branch. -/
theorem midpointActor_card_four_of_flagControl (hb : geometry.b R = 4)
    (s : CriticalSegment geometry) (control : Flags.RankOne.FlagControl source) :
    Nat.card (midpointActor (source := source) s) = 4 := by
  obtain ⟨g, hg, hbc⟩ := LargeBranch.RankOne.exists_segment_on_base_edge s
  let t := LargeBranch.RankOne.translateSegment s g hg
  have ht : Nat.card (midpointActor (source := source) t) = 4 :=
    LargeBranch.RankOne.Seed.midpoint_actor_card common radius hb t hbc control
  rw [midpointActor_card_eq_relIndex source geometry common] at ht ⊢
  have hga : act R g (alpha R) = alpha R := hg
  have hQ : Q R (alpha R) =
      (Q R (alpha R)).map (MulAut.conj g⁻¹).toMonoidHom := by
    rw [← Q_act, hga]
  change (Q R (alpha R)).relIndex (V R (act R g s.middle)) = 4 at ht
  rw [hQ, V_act, relIndex_map_map_of_injective _ _ (MulAut.conj g⁻¹).injective] at ht
  exact ht

include common radius in
/-- The actual midpoint actor has order four, using the source flag-control
theorem to discharge the displacement calculation's remaining premise.
The small-intersection hypothesis is unnecessary for this order calculation. -/
theorem midpointActor_card_four (hb : geometry.b R = 4) (s : CriticalSegment geometry) :
    Nat.card (midpointActor (source := source) s) = 4 := by
  exact midpointActor_card_four_of_flagControl source geometry common radius hb s
    (Flags.RankOne.flagControl source geometry common hb radius.toEarlyFacts)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.SmallBranch
