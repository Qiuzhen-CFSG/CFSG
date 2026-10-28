module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.EightUnequalFuture
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.LargeImage

/-!
# The unequal second backward step at distance four

For two consecutive backward selections, the original critical path is already
the future path of the first backward path. The first selection's generation
identity and transporter therefore supply all future data in the unequal
full-kernel normalization argument. A strict second selection with unequal
edge movers is impossible. The small critical-image bounds follow from the
proved distance-four large-image exclusion.

The literal three paths, first transporter and both generating edges are
retained, together with both moving covers and every central attachment.
Source: MS93 (5.12)(1), printed pp.924--925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

include e hz hn in
/-- A strict second backward step has equal movers: in the unequal case the
first backward selection supplies the entire future-path contract. -/
theorem eight_unequal_second_backward_strict_false_knownSimple
    (hne₀ : ¬ IsElementaryAbelian 2
      (d.radical.map (SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 8)
    (hb : replacementDistance h d = 4)
    {a z c b : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) a z)
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq2 : q.walk.getVert 2 = a)
    (hgen : Q d.radical (q.walk.getVert 1) ⊔ Z d.radical z = stabilizer d.radical a)
    (g : FreeAmalgam d.radical) (hg : g ∈ stabilizer d.radical a)
    (hgc : act d.radical g (p.walk.getVert 2) = c)
    (r : CriticalPath d.radical (replacementGeometry h d) b a)
    (hr2 : r.walk.getVert 2 = c)
    (hne : EightEdgeComparison.edgeMover (d := d) b (r.walk.getVert 1) ≠
      EightEdgeComparison.edgeMover (d := d) c (r.walk.getVert 1))
    (hrgen : Q d.radical (r.walk.getVert 1) ⊔ Z d.radical (p.walk.getVert 2) =
      stabilizer d.radical c)
    (hrstrict : 2 < (B d.radical c ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical b)) : False := by
  have close := eight_unequal_small_future_strict_false_knownSimple
    (e := e) (hz := hz) (hn := hn) (c := b) (y := z) hne₀ hcard hb q
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb q)
  rw [hq2] at close
  exact close r hr2
    (critical_image_small_at_knownSimple (e := e) (hz := hz) (hn := hn) hb r)
    hne hrgen hrstrict p rfl hgen g hg hgc

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
