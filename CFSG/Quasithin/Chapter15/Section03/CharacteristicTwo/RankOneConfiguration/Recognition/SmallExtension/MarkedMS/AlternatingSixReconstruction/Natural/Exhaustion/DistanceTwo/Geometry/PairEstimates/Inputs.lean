module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Images
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates.Commutator
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Inputs

/-!
# Remaining plane and central-attachment calculations

The strict action calculation supplies both orbit indices and, from the
existing abelian-radical input, both full edge images. The independent plane
calculation may take that image equality and the local-image data explicitly. The paired exponent
calculation may use the plane implication and both full images, but must
retain the actual reversed orbit and its central attachment.

These are obligations, not assertions that the original source results have
been proved. Final PairEstimateInput assembly remains in this task.
Source: MS93 (3.3), (3.6), printed pp.866--871.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open scoped commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
universe u
/-- Move the actual critical plane once the literal orbit fills the edge quotient. -/
def PlaneMovementInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, CentralLayer d → replacementDistance h d = 2 →
        (¬ core d.radical (alpha d.radical) ≤
          (frattini (Q d.radical (alpha d.radical))).map
            (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) →
        LocalCalculations d.radical (replacementGeometry h d) →
        LocalImageData h d →
        ∀ (c b : Vertex d.radical),
          CriticalPair d.radical (alpha d.radical) c
            ((replacementGeometry h d).exists_critical _ rfl) →
          Adjacent d.radical (alpha d.radical) b → Adjacent d.radical c b →
          criticalOrbit d.radical c b ⊔ Q d.radical c = Q d.radical b →
          criticalPlane d.radical c b ≤
            ⁅criticalOrbit d.radical c b,stabilizer d.radical (alpha d.radical)⁆ ⊔
              Z d.radical (alpha d.radical)

/-- Square-one generators for the paired commutator, allowing central attachments.
The plane implication is an independent premise, to be discharged in assembly. -/
def PairedExponentInput (κ : GroupClass.{u}) : Prop :=
  PlaneMovementInput κ →
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, CentralLayer d → replacementDistance h d = 2 →
        (¬ core d.radical (alpha d.radical) ≤
          (frattini (Q d.radical (alpha d.radical))).map
            (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) →
        LocalCalculations d.radical (replacementGeometry h d) →
        LocalImageData h d →
        ∀ (c b : Vertex d.radical) (B : Subgroup (FreeAmalgam d.radical)),
          CriticalPair d.radical (alpha d.radical) c
            ((replacementGeometry h d).exists_critical _ rfl) →
          Adjacent d.radical (alpha d.radical) b → Adjacent d.radical c b →
          RebasedOrbit d.radical (replacementGeometry h d) c b B →
          2 * (commutatorPreimage (criticalOrbit d.radical c b) B
            (Z d.radical (alpha d.radical))).relIndex (criticalOrbit d.radical c b) ≤
              (Q d.radical c).relIndex (criticalOrbit d.radical c b) →
          (Q d.radical c).relIndex (criticalOrbit d.radical c b) ≤
            (Q d.radical (alpha d.radical)).relIndex B →
          criticalOrbit d.radical c b ⊔ Q d.radical c = Q d.radical b →
          B ⊔ Q d.radical (alpha d.radical) = Q d.radical b →
          ∀ a ∈ criticalOrbit d.radical c b, ∀ x ∈ B, ⁅a,x⁆ ^ 2 = 1

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.PairEstimates
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
