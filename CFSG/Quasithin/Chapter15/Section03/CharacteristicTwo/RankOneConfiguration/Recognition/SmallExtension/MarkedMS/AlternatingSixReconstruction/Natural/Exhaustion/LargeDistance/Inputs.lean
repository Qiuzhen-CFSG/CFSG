module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Layer

/-!
# Source obligations for large distance with a central natural cover

MS93 (3.8) excludes the derived-only A₆ actor when b > 2. Its surviving
symplectic case has the full S₆ action on the natural central quotient.
The independent Section 5 argument excludes b > 2 in that case, retaining
the possibly nonsplit central attachment of the actual moved subgroup.

Neither implication below is proved here. Their assembly must discharge both;
a natural subgroup of order sixteen or a full point-radical image may not be
substituted for the stated quotient action.
Source: MS93 (3.8), (5.0)--(5.12), Section 7, pp.877--879, 913--927, 932--933.
-/

@[expose] public section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
universe u
variable {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}

/-- One surjective S₆ marking realizes the actual action on the original
natural central quotient. It says nothing about splitting the moved subgroup. -/
structure FullSymmetricAction
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) where
  projection : d.overgroup →* Equiv.Perm (Fin 6)
  surjective : Function.Surjective projection
  action : ∀ g v, replacementAction h e hz hn d g v =
    BinaryPermutation.naturalRepresentation (Fin 6) (projection g) v

/-- The nontrivial source-(3.8) reduction on the literal replacement. -/
def SourceReductionInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R), 2 < replacementDistance h d →
      Nonempty (FullSymmetricAction h e hz hn d)

/-- Section 5 for the full symmetric natural quotient, with its actual
central cover and original minimum characteristic radical retained. -/
def SectionFiveInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R), FullSymmetricAction h e hz hn d →
      replacementDistance h d ≤ 2

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

