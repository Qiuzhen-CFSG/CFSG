module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.Setup

/-!
# The remaining MS93 distance arguments for alternating six

Both implications use the actual minimum characteristic replacement of the
original MS2(a) radical. The first excludes critical distance greater than two;
positivity and evenness are already proved in Setup. The second is the
distance-two reconstruction, expressed as containment in the original moved
layer through the literal subgroup and amalgam maps. It must retain the
possible central fixed line. Neither input is an established source theorem.

Source: MS93 (3.6), Section 5 and Section 7, printed pp.870--872, 913--927
and 932--933; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion
universe u

/-- Section 5 excludes large distance on the minimum characteristic pair. -/
def LargeDistanceInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, replacementDistance h d ≤ 2

/-- The (3.6) branch, retaining the original moved layer and both embeddings. -/
def DistanceTwoInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, replacementDistance h d = 2 →
        core d.radical (alpha d.radical) ≤ (replacementMoved d).map (embedM d.radical)

end AlternatingSixReconstruction.Natural.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
