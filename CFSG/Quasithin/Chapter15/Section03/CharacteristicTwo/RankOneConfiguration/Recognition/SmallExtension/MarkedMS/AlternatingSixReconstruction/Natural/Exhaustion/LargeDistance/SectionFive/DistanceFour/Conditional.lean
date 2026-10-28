module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour.EightInitialSelection
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Inputs

/-!
# Conditional assembly of the natural A6 distance-four exclusion

The image and cover analysis in `DistanceFour.EightInitialSelection` supplies a
nonabelian selected critical path at distance four.  The independently owned
selected-terminal argument consumes exactly that path together with its large
Baumann slice.  This small adapter records that interface and assembles the
literal `DistanceFourInput`; no point-core equality, Sylow identification, or
other replacement hypothesis is added.

The terminal premise is kept as an explicit function so that its source owner
can be built independently and then supplied without changing this assembly.
-/

public section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceEight.PathCentrality
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
universe u

/-- The exact selected-terminal premise used by the distance-four assembly.

It retains the full symmetric action, the all-distance central layer, the
literal replacement distance, and the selected path's nonabelian span and
large Baumann slice.  In particular, it contains no point-image or whole-core
equality premise.
-/
@[expose] def SelectedTerminalInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (_s : FullSymmetricAction h e hz hn d)
    (_hc : DistanceTwo.CentralLayer d)
    (_hb : replacementDistance h d = 4)
    {a' : Vertex d.radical}
    (p : CriticalPath d.radical (replacementGeometry h d) (alpha d.radical) a')
    (_hnon : ⁅localZSpan d.radical (p.walk.getVert 2) (alpha d.radical),
      localZSpan d.radical (p.walk.getVert 2) (alpha d.radical)⁆ ≠ ⊥)
    (_hlarge : 2 <
      (B d.radical (alpha d.radical) ((replacementGeometry h d).Z_normal _)).relIndex
        (U d.radical (p.walk.getVert 2))),
    False

/-- A selected-terminal contradiction discharges the complete natural
distance-four input on the literal characteristic replacement. -/
theorem distanceFourInput_of_selectedTerminal
    (hterminal : SelectedTerminalInput.{u}) :
    DistanceFourInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz hn d s hc hb
  obtain ⟨a', p, hnon, hlarge⟩ :=
    EightInitialSelection.initial_selection_all_knownSimple
      (e := e) (hz := hz) (hn := hn) hb
  exact hterminal G L R h e hz hn d s hc hb p hnon hlarge

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.DistanceFour
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
