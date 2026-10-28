module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.DistanceTwoComplete
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Exceptional.Exhaustion.LargeDistance.FaithfulComplete

/-!
# Uniform exceptional assembly after the completed branches

The faithful initial-kernel branch and the cubic critical-distance-two branch
already give the literal whole-core equality. The only exceptional source
premise still needed for a uniform reconstruction is the cubic branch at
larger critical distance. We expose that premise at its exact carrier,
retaining the original cubic covering kernel and the actual source distance.
The adapter below then performs the finite case split and feeds the existing
recognition and C.1.32 consumers.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
open ChapterC AlternatingSixReconstruction
namespace AlternatingSixReconstruction.Exceptional
open Exhaustion
open Exhaustion.LargeDistance
universe u

/-- The sole remaining exceptional source obligation: exhaust the original
intrinsic core in the cubic initial-kernel case above critical distance two.
The kernel is the actual odd central extension `extensionKernel h`; no Sylow
or splitting hypothesis is included. -/
def CubicLargeDistanceInput : Prop :=
  ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
    (h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (_e : CentralMarking L)
    (_hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (_hk : layerKernel L R = extensionKernel h),
    2 < sourceDistance h → CoreExhaustion L R

/-- The faithful and distance-two branches reduce the uniform exceptional
whole-core conclusion to `CubicLargeDistanceInput`. -/
theorem coreExhaustion_knownSimple_of_cubic_largeDistance
    (hc : CubicLargeDistanceInput.{u}) :
    ∀ (G : Type u) [Group G] [Finite G] (L R : Subgroup G)
      (_h : SmallMSPair KnownSimple.IsKnownSimple L R)
      (_e : CentralMarking L)
      (_hz : Nat.card (center (L ⧸ pCore 2 L)) = 3), CoreExhaustion L R := by
  intro G _ _ L R h e hz
  rcases centralOmega_centralizer_cases h e hz with hf | hk
  · exact coreExhaustion_of_faithful h e hz hf
  · by_cases hle : sourceDistance h ≤ 2
    · exact coreExhaustion_of_distanceTwo h e hz (sourceDistance_eq_two h hle)
    · have hgt : 2 < sourceDistance h := by
        have hp := sourceDistance_pos h
        have he := sourceDistance_even h
        rw [Nat.even_iff] at he
        omega
      exact hc G L R h e hz hk hgt

/-- The exact exceptional whole-core clauses follow from the one cubic
larger-distance source premise. -/
theorem exceptionalCore_knownSimple_of_cubic_largeDistance
    (hc : CubicLargeDistanceInput.{u}) :
    ExceptionalCoreInput.{u} KnownSimple.IsKnownSimple := by
  intro G _ _ L R h e hz
  exact core_facts_of_exhaustion h e hz
    (coreExhaustion_knownSimple_of_cubic_largeDistance hc G L R h e hz)

/-- Literal C.1.32 application for the uniform exceptional branch, retaining
the original marking and odd-index radical. -/
theorem rankTwo_of_cubic_largeDistance
    {G : Type u} [Group G] [Finite G]
    {L R : Subgroup G}
    (_h : SmallMSPair KnownSimple.IsKnownSimple L R)
    (_e : CentralMarking L)
    (_hz : Nat.card (center (L ⧸ pCore 2 L)) = 3)
    (hc : CubicLargeDistanceInput.{u}) :
    RankTwoAlternatives L R := by
  exact rankTwo_of_exhaustion _h _e _hz
    (coreExhaustion_knownSimple_of_cubic_largeDistance hc G L R _h _e _hz)

end AlternatingSixReconstruction.Exceptional
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
