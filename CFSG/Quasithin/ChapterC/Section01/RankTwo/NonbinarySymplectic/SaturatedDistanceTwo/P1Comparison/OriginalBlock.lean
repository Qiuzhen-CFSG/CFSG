module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.NonbinarySymplectic.DistanceTwoRecognition.PairedOrbit

/-!
# Original component recognition from the distance-two source endgame

The replacement distance-two argument already proves shortness and the
natural block model for the original component K. The point-parabolic
endgame supplies its missing degree restriction. Combining them recognizes
K without transporting the replacement two-core to the whole ambient
two-core or requiring a second Frattini bound there.

The actual critical path, both edge markings and all SourceEndgame premises
remain explicit. Source: MS93 (3.6)--(3.7), printed pp.870--877, and
Aschbacher--Smith C.1.32, printed pp.135--136.
-/

public noncomputable section
open Subgroup
open Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison
open Theory.SpecificGroups.SymplecticFour

variable {H F : Type*} [Group H] [Finite H] [Field F] [Finite F] [CharP F 2]
variable {K R : Subgroup H} {n : ℕ} {h : Input K R n F}
variable {d : CharacteristicReduction K R}
variable {a z t : Vertex d.radical} {c : EdgeMarking h d a t} {u : Sp F}

/-- The source endgame recognizes the original component. Its whole
commutator core is handled by the replacement distance-two theorem itself. -/
theorem SourceEndgame.original_block
    (s : SourceEndgame h d (z := z) c u)
    {g : Geometry d.radical} (path : CriticalPath d.radical g a z)
    (hb : g.b d.radical = 2) (hat : Adjacent d.radical a t)
    (hzt : Adjacent d.radical z t) (c' : EdgeMarking h d z t) :
    IsSp4FourBlock K :=
  DistanceTwoRecognition.block_of_degree_two_distance_two h d g hb
    (s.degree_eq_two path hb hat hzt c')

end CFSG.Quasithin.ChapterC.RankTwo.NonbinarySymplectic.SaturatedDistanceTwo.P1Comparison
