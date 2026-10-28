module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.LocalControl.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.Comparison.Source

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.G2Reconstruction.DistanceTwo.Midpoint

/-!
# Conditional assembly of the G₂ distance-two argument

Positive even distance and the proved critical-pair criterion reduce the
target to the radius-two calculation recorded in `DistanceFourExclusionInput`.
The local-control producer is now proved. Supplying the remaining exclusion
produces the unchanged `DistanceTwoInput` and its actual Frattini-small
application; the unconditional distance-two theorem is still outstanding.

Source: MS93 (3.8), pp.877--879; Aschbacher--Smith C.1.31--32, pp.135--136.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace G2Reconstruction
universe u

/-- Assembly retains both independent source obligations until their proofs
are available; neither input is an assumption of the original MS pair. -/
theorem distanceTwo_of_local_inputs
    (hloc : DistanceTwo.LocalControlInput.{u})
    (hfour : DistanceTwo.DistanceFourExclusionInput.{u}) : DistanceTwoInput.{u} := by
  intro J _ _ L R h e
  have hlo := distance_ge_two h e
  apply Nat.le_antisymm _ hlo
  by_contra hgt
  have hb : 2 < (geometry h).b (R.subgroupOf (L ⊔ R)) := Nat.lt_of_not_ge hgt
  have hs := hloc J L R h e hb
  exact hfour J L R h e (DistanceTwo.distance_four_of_localControl h e hb hs) hs

/-- The original whole-core consumer, with the independently produced
distance-two comparison and the two earlier distance calculations explicit. -/
theorem frattini_small_of_local_distance_inputs
    (hloc : DistanceTwo.LocalControlInput.{u})
    (hfour : DistanceTwo.DistanceFourExclusionInput.{u})
    (hc : DistanceTwoComparisonInput.{u})
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    FrattiniSmall L R :=
  frattini_small_of_distance_inputs h e (distanceTwo_of_local_inputs hloc hfour) hc

/-- Local control is proved; the remaining source obligation excludes distance four. -/
theorem distanceTwo_of_distanceFourExclusion
    (hfour : DistanceTwo.DistanceFourExclusionInput.{u}) : DistanceTwoInput.{u} :=
  distanceTwo_of_local_inputs DistanceTwo.localControl_knownSimple hfour

/-- The original Frattini containment with only the radius-two exclusion explicit. -/
theorem frattini_small_of_distanceFourExclusion
    (hfour : DistanceTwo.DistanceFourExclusionInput.{u})
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (e : (L ⧸ centralPreimage (pCore 2 L)) ≃* commutator (Atlas.G2.Model (ZMod 2))) :
    FrattiniSmall L R :=
  frattini_small_of_distance_inputs h e (distanceTwo_of_distanceFourExclusion hfour)
    Comparison.distanceTwoComparison_knownSimple

end G2Reconstruction
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
