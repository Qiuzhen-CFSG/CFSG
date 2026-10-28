module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Orbit

/-!
# Source obligations for the central-attachment distance-two argument

The replacement moving-layer calculation, the paired critical-orbit geometry,
and recognition of its canonical fixed quotient are separate implications.
The latter two may use the earlier conclusions as explicit hypotheses, so
their proofs can proceed independently. Their final assembly must construct
every premise. No input asserts that the whole original core is elementary,
or requires a natural subgroup complement to its central attachment.

Source: MS93 (3.2), (3.3), and (3.6), printed pp.863--871.
-/

@[expose] public section
open Subgroup
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
universe u

/-- Identify the replacement's moving X and Z layers with the original whole
moved subgroup. The replacement two-core itself can be smaller. -/
def CentralLayerInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, CentralLayer d

/-- Construct the actual paired orbit in the non-Frattini source branch. -/
def OrbitGeometryInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, CentralLayer d → replacementDistance h d = 2 →
        (¬ core d.radical (alpha d.radical) ≤
          (frattini (Q d.radical (alpha d.radical))).map
            (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) →
        Nonempty (PairedOrbit (pResidual 2 d.overgroup) d.radical (replacementGeometry h d))

/-- Recognize the fixed quotient and its kernel displacement for the same
selected literal orbit. Geometry remains an explicit independent premise. -/
def OrbitRecognitionInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, CentralLayer d → replacementDistance h d = 2 →
        (¬ core d.radical (alpha d.radical) ≤
          (frattini (Q d.radical (alpha d.radical))).map
            (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) →
        ∀ o : PairedOrbit (pResidual 2 d.overgroup) d.radical (replacementGeometry h d),
          o.Recognized

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
