module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.AugmentationFixedSixteenUnequal

/-!
# Radius-fixed versus equal-mover alternatives

The controlled backward transport gives equal neighboring small movers whenever
the full radius core is not fixed.  This adapter records the exact dichotomy
needed by the image-sixteen terminal argument.  The fixed-radius branch remains
an explicit conclusion; no radius fixedness or mover equality is inferred from
the selected span alone.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Representation
open scoped commutatorElement Pointwise IsMulCommutative
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
/-- Under the complete controlled-backward hypotheses, either the two
small movers agree or the full radius core is fixed at the starting vertex. -/
theorem sixteen_selected_mover_eq_or_radius_fixed_knownSimple
    (hb : replacementDistance h d = 4)
    (hcard : Nat.card (d.radical.map (SourceReduction.projection h e hz hn d)) = 16)
    {z t c : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hlarge : 4 ≤ (Q d.radical z).relIndex (Z d.radical (alpha d.radical)))
    (W : Subgroup (FreeAmalgam d.radical))
    (q : CriticalPath d.radical (replacementGeometry h d) c (p.walk.getVert 2))
    (hq1 : q.walk.getVert 1 = t) (hq2 : q.walk.getVert 2 = alpha d.radical)
    (hback : 4 ≤ (Q d.radical (p.walk.getVert 2)).relIndex (Z d.radical c))
    (hstrict : 2 < (B d.radical (alpha d.radical)
      ((replacementGeometry h d).Z_normal _)).relIndex (U d.radical c))
    (hgen : Q d.radical t ⊔ W = stabilizer d.radical (alpha d.radical))
    (hfix : ⁅Z d.radical c,Z d.radical (p.walk.getVert 2)⁆ ≤
      centralizer (W : Set (FreeAmalgam d.radical)))
    (htransport : ∃ x ∈ stabilizer d.radical (alpha d.radical),
      act d.radical x (p.walk.getVert 1) = t ∧
      ∃ k ∈ stabilizer d.radical t,
        c = act d.radical k (act d.radical x (p.walk.getVert 2)) ∧
        ∃ g ∈ normalizer (Q d.radical t : Set (FreeAmalgam d.radical)) ⊓
            stabilizer d.radical (alpha d.radical),
          ∀ v ∈ Q d.radical t,
            (MulAut.conj k⁻¹) v = (MulAut.conj g) v) :
    SmallMover.join (U d.radical c) (Q d.radical c) (Q d.radical t) 4 =
        SmallMover.join (U d.radical (alpha d.radical))
          (Q d.radical (alpha d.radical)) (Q d.radical t) 4 ∨
      ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
        fixedCore d.radical (alpha d.radical) := by
  by_cases hnot :
      ¬ ⁅V d.radical (alpha d.radical),Q d.radical (alpha d.radical)⁆ ≤
        fixedCore d.radical (alpha d.radical)
  · left
    exact sixteen_selected_backward_movers_eq_of_radius_not_fixed_knownSimple
      (e := e) (hz := hz) (hn := hn) hb hcard p hlarge W q hq1 hq2 hback
      hstrict hgen hfix htransport hnot
  · right
    by_contra hbad
    exact hnot hbad

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

