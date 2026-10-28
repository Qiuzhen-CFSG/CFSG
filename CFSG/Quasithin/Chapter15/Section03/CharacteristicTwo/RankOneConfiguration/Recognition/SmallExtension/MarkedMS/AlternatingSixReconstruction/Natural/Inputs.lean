module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Layer

/-!
# The two source steps for the natural whole core

Initial recognition concerns only the canonical central-omega moved section.
Exhaustion is the subsequent MS93 graph argument: [O₂(M),K] = [Ω₁Z(O₂(M)),K].
The latter may use the former, so both implications can be proved independently.
Neither input assumes a natural subgroup of order sixteen or a Sylow radical.
These are outstanding source obligations, not proved classification results.

Source: MS93 (3.2)(vi), (3.6), Section 5 and Section 7, printed
pp.863--864, 870--872, 913--927 and 932--933.
-/

@[expose] public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural
universe u

/-- Recognition of the initial moved/fixed section, before whole-core exhaustion. -/
def InitialRecognitionInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz

/-- MS93's whole-core equality, conditional only on the initial natural section.
Its producer must handle arbitrary MS2(a) radicals and the nonsplit central cover. -/
def CoreExhaustionInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥), InitialNatural h e hz →
      ⁅pCore 2 (L ⊔ R : Subgroup G), L.subgroupOf (L ⊔ R)⁆ =
        ⁅centralOmega L R, L.subgroupOf (L ⊔ R)⁆

end AlternatingSixReconstruction.Natural
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
