module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Basic
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Second.Geometry
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Second.FixedSpace
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections.FromFrame.Second.CubicEdge

/-!
# Geometric and fixed-space calculation for MS93's second section

The actual midpoint radius supplements Q_alpha in Q_beta. Its commutator
bounds put the edge displacement in the literal denominator Y, so the edge
kernel acts trivially on the given second linear quotient. Every actual
order-three subgroup of the marked residual moves the whole edge quotient.
The relative three-subgroups argument therefore gives the required
fixed-preimage inclusion, and averaging over that same subgroup gives zero
residual invariants of the literal quotient `(K/Z_alpha)/(Y/Z_alpha)`.

The only additional fixed-space input is the supplied actual subgroup of
order three. Its construction and quotient-surjectivity belong to the
separate residual owner; the FromFrame owner retains the final construction
of both natural sections. None of these calculations needs the large
intersection hypothesis.

Source: Meierfrankenfeld--Stellmacher (1993), (4.6.12)(2), printed p.910.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
open Flags.RankOne

variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}
  (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
  (f : Frame source) (hb : geometry.b R = 4) (s : CriticalSegment geometry)
  (hbc : Adjacent R (beta R) s.middle)

include common radius hb hbc in
/-- Fixed points of any actual cubic subgroup on K/Z_alpha lie in the source denominator Y. -/
theorem cubic_fixedPreimage_le
    (T : Subgroup (flagResidual source f.orientation)) (hT : Nat.card T = 3) :
    commutatorPreimage (intersection s.middle)
      (T.map (flagResidual source f.orientation).subtype) (Z R (alpha R)) ≤
        fixedPreimage s.middle :=
  cubic_fixedPreimage_le_of_edge_movement common radius f hb s hbc T
    (cubic_edge_movement source f T hT)

include hb in
/-- The literal second section has zero residual invariants, by averaging over the supplied cubic subgroup. -/
theorem secondRepresentation_invariants_eq_bot
    (T : Subgroup (flagResidual source f.orientation)) (hT : Nat.card T = 3)
    (d : LayerModule source (V R (alpha R))) :
    Representation.invariants (secondRepresentation common radius f s hbc d) = ⊥ :=
  secondRepresentation_invariants_eq_bot_of_cubic_fixedPreimage common radius f s hbc T hT
    (cubic_fixedPreimage_le common radius f hb s hbc T hT) d

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Sections
