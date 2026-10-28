module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Inputs
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Estimates.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Radius.Source

/-!
# The full symmetric action on the original replacement

The normalizer construction leaves A₆ or S₆ as the exact image. The proved
critical estimates and radius contradiction exclude A₆ whenever the actual
distance exceeds two. The surviving surjective map realizes the unchanged
action on the natural central quotient, retaining the entire central cover.
The known-simple export discharges both earlier source inputs; the generic
conditional interfaces are preserved.

Source: MS93 (3.8), pp.877--879, and Section 7, pp.932--933.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
universe u
open SourceReduction

/-- The exact source-(3.8) action on this replacement, conditional only on
the two separately identified earlier-source arguments. -/
noncomputable def fullSymmetricAction_of_source_inputs
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
    (he : EstimatesInput κ) (hr : RadiusContradictionInput κ)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : 2 < replacementDistance h d) :
    FullSymmetricAction h e hz hn d := by
  apply SourceReduction.fullSymmetricAction h e hz hn d
  intro himage
  exact hr G L R h e hz hn d himage
    (fourGeometry h e hz hn d himage hb (he G L R h e hz hn d hb himage))

/-- Final source-reduction assembly; the full source theorem still requires
unconditional producers of both inputs. -/
theorem sourceReduction_of_inputs {κ : GroupClass.{u}}
    (he : EstimatesInput κ) (hr : RadiusContradictionInput κ) : SourceReductionInput κ := by
  intro G _ _ L R h e hz hn d hb
  exact ⟨fullSymmetricAction_of_source_inputs he hr h e hz hn d hb⟩

/-- The actual full action after the radius-two argument; the critical
estimates are supplied by their proved original-replacement construction. -/
noncomputable def fullSymmetricAction_of_radius
    {G : Type u} [Group G] [Finite G] {κ : GroupClass.{u}} {L R : Subgroup G}
    (hr : RadiusContradictionInput κ)
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : 2 < replacementDistance h d) :
    FullSymmetricAction h e hz hn d :=
  fullSymmetricAction_of_source_inputs estimates hr h e hz hn d hb

/-- Only the radius-two source argument remains in the derived-image reduction.
The final owner must discharge it before claiming the full source theorem. -/
theorem sourceReduction_of_radius {κ : GroupClass.{u}}
    (hr : RadiusContradictionInput κ) : SourceReductionInput κ :=
  sourceReduction_of_inputs estimates hr

/-- The exact source-(3.8) reduction, with the derived-action branch excluded. -/
theorem sourceReduction_knownSimple : SourceReductionInput.{u} KnownSimple.IsKnownSimple :=
  sourceReduction_of_radius Radius.radiusContradiction_knownSimple

/-- The full S₆ marking of this literal characteristic replacement, using
its original natural central-quotient action. -/
noncomputable def fullSymmetricAction_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : 2 < replacementDistance h d) :
    FullSymmetricAction h e hz hn d :=
  fullSymmetricAction_of_radius Radius.radiusContradiction_knownSimple h e hz hn d hb

end AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
