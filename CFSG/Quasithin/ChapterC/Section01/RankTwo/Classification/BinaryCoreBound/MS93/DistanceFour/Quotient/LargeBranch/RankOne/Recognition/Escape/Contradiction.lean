module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Seed
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Sections

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction.Closure
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Quotient.LargeBranch.RankOne.Recognition.Escape.Contradiction.Geometry

/-!
# The remaining moving-neighbor fixation step in second-star escape

Geometry selects the actual moving neighbor, proves the commutator bound
by Z_alpha Z_c, and puts the edge star inside the literal Y preimage.
Closure proves genuine actor generation, the second/full-star identities
modulo the recognized orbit span, and the final whole-radius containment.

The theorem below assembles those proofs once Y is fixed by the full
first rank-one actor. The two remaining source arguments are the moving
neighbor's displacement bound modulo B_mu and the deduction of full-actor
fixation from that bound and the two natural sections. This is a conditional
reduction, not the requested radius_le_midpoint_of_contained_star theorem.
The latter still has to discharge fixation using the supplied marked
SpanQuotient and the original escape hypotheses.

Source: Meierfrankenfeld--Stellmacher, Pushing up weak BN-pairs of rank two
(1993), (4.6.12)(4), printed p.911, using clauses (1)--(3) on pp.910--911.
-/

public section

open Subgroup Stellmacher.PushingUp.AmalgamGraph
open Representation Representation.BinaryOffender
open scoped commutatorElement
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
open Sections
variable {M : Type*} [Group M] [Finite M] {L R : Subgroup M}
  {source : LocalSource L R} {geometry : Geometry R}

/-- All local inclusions and final propagation are proved; only full-actor
fixation of the original Y quotient remains explicit in this reduction. -/
theorem radius_le_midpoint_of_Y_fixed
    (common : CommonFacts R source geometry) (radius : RadiusFacts R geometry)
    (hb : geometry.b R = 4) (s : CriticalSegment geometry)
    (hbc : Adjacent R (beta R) s.middle) (d : LayerModule source (V R (alpha R)))
    (f : Seed.Frame source) (hf : Seed.Compatible f s)
    (hcontained : d.preimage (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ Q R s.middle)
    (hspan : orbitSpan s.middle ≤ Q R s.middle)
    (hmoved : Seed.movedSpace d.representation ((f.residual true).map source.projection)
      (Seed.secondTildeStar (geometry := geometry) d f 1) ≤ d.subspace (orbitSpan s.middle))
    (hY : d.subspace (Sections.fixedPreimage s.middle) ≤
      fixedSpace d.representation ((f.actor false).map source.projection)) :
    V R (alpha R) ≤ Q R s.middle := by
  exact radius_le_midpoint_of_edge_le_second common radius s d f hf hcontained hspan hmoved
    (edgeStar_subspace_le_second_of_Y_fixed common radius hb s hbc d f hY)

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.LargeBranch.RankOne.Escape
