module

public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.Marking
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SourceReduction.Source
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.LargeDistance.SectionFive.Source

/-!
# Assembly of the two large-distance source arguments

The source-(3.8) reduction produces the full symmetric quotient action
whenever the distance exceeds two. Section 5 then contradicts that strict
inequality. The existing positivity and evenness force the literal distance
to equal two, without any input from distance-two core reconstruction.

The critical estimates, derived radius contradiction, full symmetric action,
all-distance central layer and complete source-(5.11) bound are proved.
The final known-simple assembly retains only the independent source-(5.12)
distance-four exclusion.
The order-sixteen, full-point-radical specialization is discharged below;
the remaining-case theorem retains both other radical images and the possible
order-thirty-two cover.
Source: MS93 (3.8), (5.12), and Section 7, pp.877--879, 924--927, 932--933.
-/

public noncomputable section
open Subgroup
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS
namespace AlternatingSixReconstruction.Natural.Exhaustion
universe u

/-- Conditional assembly; both source obligations must be independently discharged. -/
theorem largeDistance_of_source_inputs {κ : GroupClass.{u}}
    (hr : LargeDistance.SourceReductionInput κ) (hs : LargeDistance.SectionFiveInput κ) :
    LargeDistanceInput κ := by
  intro G _ _ L R h e hz hn d
  by_contra! hb
  obtain ⟨s⟩ := hr G L R h e hz hn d hb
  exact (not_lt_of_ge (hs G L R h e hz hn d s)) hb

/-- Actual replacement-distance application using its proved positivity and evenness. -/
theorem replacementDistance_eq_two_of_source_inputs {κ : GroupClass.{u}}
    (hr : LargeDistance.SourceReductionInput κ) (hs : LargeDistance.SectionFiveInput κ)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair κ L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) : replacementDistance h d = 2 :=
  replacementDistance_eq_two h d (largeDistance_of_source_inputs hr hs G L R h e hz hn d)

/-- Preserved conditional assembly with the derived contradiction explicit.
The specialized assembly below supplies its proved known-simple producer. -/
theorem largeDistance_knownSimple_of_remaining_inputs
    (hr : LargeDistance.SourceReduction.RadiusContradictionInput.{u} KnownSimple.IsKnownSimple)
    (hlarge : LargeDistance.SectionFive.BeyondFourInput.{u} KnownSimple.IsKnownSimple)
    (hfour : LargeDistance.SectionFive.DistanceFourInput.{u} KnownSimple.IsKnownSimple) :
    LargeDistanceInput.{u} KnownSimple.IsKnownSimple :=
  largeDistance_of_source_inputs (LargeDistance.sourceReduction_of_radius hr)
    (LargeDistance.SectionFive.sectionFive_knownSimple_of_distance_inputs hlarge hfour)

/-- Literal distance-two application of the assembled remaining source arguments. -/
theorem replacementDistance_eq_two_knownSimple_of_remaining_inputs
    (hr : LargeDistance.SourceReduction.RadiusContradictionInput.{u} KnownSimple.IsKnownSimple)
    (hlarge : LargeDistance.SectionFive.BeyondFourInput.{u} KnownSimple.IsKnownSimple)
    (hfour : LargeDistance.SectionFive.DistanceFourInput.{u} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) : replacementDistance h d = 2 :=
  replacementDistance_eq_two h d
    (largeDistance_knownSimple_of_remaining_inputs hr hlarge hfour G L R h e hz hn d)

/-- Only the full-symmetric Section 5 distance branches remain. The complete
source-(3.8) action reduction and central-layer premise are discharged. -/
theorem largeDistance_knownSimple_of_sectionFive_inputs
    (hlarge : LargeDistance.SectionFive.BeyondFourInput.{u} KnownSimple.IsKnownSimple)
    (hfour : LargeDistance.SectionFive.DistanceFourInput.{u} KnownSimple.IsKnownSimple) :
    LargeDistanceInput.{u} KnownSimple.IsKnownSimple :=
  largeDistance_of_source_inputs LargeDistance.sourceReduction_knownSimple
    (LargeDistance.SectionFive.sectionFive_knownSimple_of_distance_inputs hlarge hfour)

/-- The literal distance-two application with no derived-action callback. -/
theorem replacementDistance_eq_two_knownSimple_of_sectionFive_inputs
    (hlarge : LargeDistance.SectionFive.BeyondFourInput.{u} KnownSimple.IsKnownSimple)
    (hfour : LargeDistance.SectionFive.DistanceFourInput.{u} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) : replacementDistance h d = 2 :=
  replacementDistance_eq_two h d
    (largeDistance_knownSimple_of_sectionFive_inputs hlarge hfour G L R h e hz hn d)

/-- The complete beyond-four argument discharges source (5.11). Only the
independent general source-(5.12) exclusion remains in the final assembly. -/
theorem largeDistance_knownSimple_of_distanceFour_input
    (hfour : LargeDistance.SectionFive.DistanceFourInput.{u} KnownSimple.IsKnownSimple) :
    LargeDistanceInput.{u} KnownSimple.IsKnownSimple :=
  largeDistance_knownSimple_of_sectionFive_inputs
    LargeDistance.SectionFive.EightTerminal.beyondFour_knownSimple hfour

/-- Literal replacement-distance application of the completed beyond-four
argument, with only the independent distance-four source input remaining. -/
theorem replacementDistance_eq_two_knownSimple_of_distanceFour_input
    (hfour : LargeDistance.SectionFive.DistanceFourInput.{u} KnownSimple.IsKnownSimple)
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) : replacementDistance h d = 2 :=
  replacementDistance_eq_two h d
    (largeDistance_knownSimple_of_distanceFour_input hfour G L R h e hz hn d)

/-- The actual replacement has distance two whenever its canonical radical
image is a full point core, retaining both possible moving-cover orders. -/
theorem replacementDistance_eq_two_knownSimple_of_full_point_image
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (t : Equiv.Perm (Fin 6))
    (hpoint : d.radical.map (LargeDistance.SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj t).toMonoidHom) :
    replacementDistance h d = 2 :=
  LargeDistance.SectionFive.full_point_distance_two_knownSimple t hpoint

/-- A nonelementary canonical radical image of order eight forces the literal
replacement distance to be two, for either moving cover. -/
theorem replacementDistance_eq_two_knownSimple_of_nonelementary_eight_image
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R)
    (hne : ¬ IsElementaryAbelian 2
      (d.radical.map (LargeDistance.SourceReduction.projection h e hz hn d)))
    (hcard : Nat.card
      (d.radical.map (LargeDistance.SourceReduction.projection h e hz hn d)) = 8) :
    replacementDistance h d = 2 :=
  LargeDistance.SectionFive.nonelementary_eight_distance_two_knownSimple hne hcard

/-- The actual original replacement has distance two whenever its whole
moved layer is natural and its canonical radical image is a full point core. -/
theorem replacementDistance_eq_two_knownSimple_of_natural_point_image
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hnat : Nat.card (replacementMoved d) = 16)
    (t : Equiv.Perm (Fin 6))
    (hpoint : d.radical.map (LargeDistance.SourceReduction.projection h e hz hn d) =
      Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
        (MulAut.conj t).toMonoidHom) :
    replacementDistance h d = 2 := by
  by_cases hb : 2 < replacementDistance h d
  · let s := LargeDistance.fullSymmetricAction_knownSimple h e hz hn d hb
    apply LargeDistance.SectionFive.distance_eq_two_of_natural_full_point s hnat t
    rwa [LargeDistance.SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s]
  · exact replacementDistance_eq_two h d (Nat.le_of_not_gt hb)

/-- After source (3.8), the original large-distance problem retains precisely
these unexcluded cover and radical-image cases, using the canonical action. -/
theorem largeDistance_remaining_cases_knownSimple
    {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
    (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
    (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
    (d : Replacement L R) (hb : 2 < replacementDistance h d) :
    Nat.card (replacementMoved d) = 32 ∨
      (Nat.card (replacementMoved d) = 16 ∧ ∀ t : Equiv.Perm (Fin 6),
        d.radical.map (LargeDistance.SourceReduction.projection h e hz hn d) ≠
          Theory.SpecificGroups.SymmetricSix.BinaryFlags.pointCore.map
            (MulAut.conj t).toMonoidHom) := by
  let s := LargeDistance.fullSymmetricAction_knownSimple h e hz hn d hb
  have hs := LargeDistance.SectionFive.large_distance_remaining_cases s hb
  rwa [LargeDistance.SourceReduction.fullSymmetricAction_projection_unique h e hz hn d s] at hs

end AlternatingSixReconstruction.Natural.Exhaustion
end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS

