module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Critical

/-!
# The remaining two source-(3.8) arguments

The first obligation supplies the A₆ commutator estimates on the actual
replacement. The second carries out the radius-two contradiction after
the critical-path reduction. The latter can be proved with its displayed
geometric premises while the former is developed independently. Neither
obligation is established by declaring these predicates.

Both retain the original MS2(a) radical, the possibly nonsplit central moved
cover and the literal quotient action. Source: MS93 (3.8), pp.877--879,
with the characteristic reduction of Section 7, pp.932--933.
-/

@[expose] public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
universe u

/-- Source (3.8), first paragraph: the A₆-specific estimates (2.3)(c,d).
These are not supplied by the normalizer calculation or by a binary source. -/
def EstimatesInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R), 2 < replacementDistance h d →
      (projection h e hz hn d).range = alternatingGroup (Fin 6) → CriticalEstimates h d

/-- The radius-two group argument on pp.878--879, after the critical-path
reduction. It retains the entire central cover and the literal replacement. -/
def RadiusContradictionInput (κ : GroupClass.{u}) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R),
      (projection h e hz hn d).range = alternatingGroup (Fin 6) → FourGeometry h d → False

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
