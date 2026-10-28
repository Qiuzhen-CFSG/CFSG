module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.Structure.Preparation

/-!
# Remaining central-quotient calculations for distance two

Normal generation and the edge-centralizer condition are already proved.
The two remaining source branches are the abelian radical and critical-image
calculation, and the opposite-layer intersection bound. The latter may use
the former's order-two critical images; final assembly must discharge both.

All inputs retain the original pair, its characteristic replacement and the
whole central moved cover. In particular they assert no natural subgroup,
full point-core image, or whole-core reconstruction.
Source: MS93 (3.3)(ii), (3.6), printed pp.866--871.
-/

@[expose] public section
open Subgroup Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.BinaryMS.MS93
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- The actual edge quotient is abelian, and each critical opposite image
has order two. These are conclusions to prove from the source hypotheses. -/
structure LocalImageData (h : SmallMSPair κ L R) (d : Replacement L R) : Prop where
  radical_derived : ⁅d.radical,d.radical⁆ ≤ pCore 2 d.overgroup
  image_two : ∀ c, CriticalPair d.radical (alpha d.radical) c
    ((replacementGeometry h d).exists_critical _ rfl) →
      (Q d.radical c).relIndex (Z d.radical (alpha d.radical)) = 2

/-- The central-quotient action branch, on the literal replacement. -/
def LocalImageInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, CentralLayer d → replacementDistance h d = 2 →
        (¬ core d.radical (alpha d.radical) ≤
          (frattini (Q d.radical (alpha d.radical))).map
            (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) →
        LocalImageData h d

/-- The plane branch may consume the local quotient calculations explicitly.
It must prove the commutator bound for the entire opposite layer, including
its possible central attachment. -/
def PlaneIntersectionInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ∀ d : Replacement L R, CentralLayer d → replacementDistance h d = 2 →
        (¬ core d.radical (alpha d.radical) ≤
          (frattini (Q d.radical (alpha d.radical))).map
            (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) →
        LocalImageData h d →
        ∀ c b, CriticalPair d.radical (alpha d.radical) c
          ((replacementGeometry h d).exists_critical _ rfl) →
          Adjacent d.radical (alpha d.radical) b → Adjacent d.radical c b →
          ⁅Q d.radical (alpha d.radical),
            Z d.radical c ⊓ Q d.radical (alpha d.radical)⁆ ≤ Z d.radical b

end AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
