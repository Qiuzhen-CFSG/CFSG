module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.ForwardSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore.OppositeGenerated
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightInitialSelection

/-!
# Exclusion of the actual mixed distance-four branch

Strict opposite-slice propagation supplies an external strict neighbor for
a second backward shift. Reversing that selected path preserves the original
start and midpoint while its two interior edge kernels generate the midpoint
stabilizer. The literal marked full-kernel failure is then fixed at that
midpoint, contradicting its trapped or critical noncentrality alternative.

The original initial-selection theorem supplies the strict path. No fixation,
whole residual-core bound, or extra terminal callback is assumed. Both moved
covers and every central attachment remain in the original replacement.

Source: MS93 (5.12), printed pp.924--927, with the compatible forward
selection recorded on p.925.
-/

public noncomputable section
open Subgroup Theory.GroupTheory
open scoped commutatorElement Pointwise IsMulCommutative
open CFSG.Quasithin.ChapterB.Offenders CFSG.Quasithin.ChapterB.Offenders.Six
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  {h : SmallMSPair KnownSimple.IsKnownSimple L R} {e : CentralMarking L}
  {hz : center (L ⧸ pCore 2 L) = ⊥} {hn : InitialNatural h e hz}
  {d : Replacement L R}

/-- A strict mixed source slice is impossible on the original alpha-based
critical path; the compatible forward endpoint is constructed internally. -/
theorem strict_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom)
    {z : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) z)
    (hstrict : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (p.walk.getVert 2))) : False := by
  obtain ⟨w,q,hmid,hgen⟩ := strict_generated_forward_path_knownSimple hb u him p hstrict
  have hs : 2 < (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
      (U d.radical (q.walk.getVert 2)) := by rwa [hmid]
  exact strict_generated_path_false_knownSimple hb u him q hs hgen

/-- The full radical mixed-plane branch cannot have critical distance four.
Initial nonabelian strict-slice selection is supplied by the original graph. -/
theorem distance_four_false_knownSimple
    (hb : replacementDistance h d = 4) (u : Equiv.Perm (Fin 6))
    (him : d.radical.map (SourceReduction.projection h e hz hn d) =
      plus.map (MulAut.conj u).toMonoidHom) : False := by
  obtain ⟨z,p,_,hstrict⟩ := EightInitialSelection.initial_selection_all_knownSimple
    (e := e) (hz := hz) (hn := hn) hb
  exact strict_false_knownSimple hb u him p hstrict

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.Terminal.MixedWholeCore
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
