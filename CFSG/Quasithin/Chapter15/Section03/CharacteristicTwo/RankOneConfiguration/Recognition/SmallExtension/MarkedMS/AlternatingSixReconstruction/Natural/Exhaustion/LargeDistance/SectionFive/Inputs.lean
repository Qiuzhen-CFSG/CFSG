module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Graph
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Inputs

/-!
# The two distance branches of MS93 Section 5

The source proves the upper bound four in (5.11), then excludes equality in
(5.12). These independent contracts keep the original characteristic
replacement, its entire central cover, and the given full symmetric marking.
They take the earlier graph-layer identification as an explicit premise,
whose existing producer is independent of both distance branches. They impose
no point-radical image or splitting condition.

Both contracts remain source obligations of
qt-e-ms-small-a6-exhaustion-large-distance. The all-distance CentralLayer
producer is now owned by qt-e-ms-small-a6-exhaustion-distance-two. `SectionFive.Source` assembles them
using the already proved parity of the actual critical distance.
Source: MS93 (5.0)--(5.12), printed pp.912--927, and Section 7, pp.932--933.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
universe u

/-- The source-(5.11) branch, for the literal replacement and central cover. -/
def BeyondFourInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R), FullSymmetricAction h e hz hn d → DistanceTwo.CentralLayer d →
      4 < replacementDistance h d → False

/-- The source-(5.12) terminal branch, independent of the bound in (5.11). -/
def DistanceFourInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R), FullSymmetricAction h e hz hn d → DistanceTwo.CentralLayer d →
      replacementDistance h d = 4 → False

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
