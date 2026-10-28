module
public import CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.Recognition.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages.CriticalTransposition

/-!
# Whole-cover and selected-orbit applications of the critical line

The original non-Frattini branch now supplies full symmetric-six coordinates
on the whole moved cover before local orbit calculations. For the literal
ordered orbit it supplies the critical commutator's exact order and its
trivial intersection with the opposite component-fixed attachment.

Radical-derived containment, the opposite-plane bound and paired exponent two
remain with qt-e-ms-small-a6-exhaustion-distance-two. These applications do
not assert completion of MS93 (3.6), printed pp.870--871.
-/

public noncomputable section
open Subgroup Representation Representation.BinaryOffender BinaryPermutation
open scoped IsMulCommutative commutatorElement
open CFSG.Quasithin.ChapterC.BinaryMS.MS93 Stellmacher.PushingUp.AmalgamGraph
open CFSG.Quasithin.ChapterC.NaturalSixControl.SymplecticDistanceTwo
namespace CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
open LargeDistance PlaneMovement
universe u
variable {G : Type u} [Group G] [Finite G] {L R : Subgroup G}
  (h : SmallMSPair KnownSimple.IsKnownSimple L R) (e : CentralMarking L)
  (hz : center (L ⧸ pCore 2 L) = ⊥) (hn : InitialNatural h e hz)
  (d : Replacement L R)

include h e hz hn in
/-- The original non-Frattini distance-two hypotheses give whole-cover
coordinates before any LocalCalculations, image-abelianness or paired-square
input. The source projection and both possible orders are unchanged. -/
theorem whole_cover_model_of_nonfrattini
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    letI := replacementMoved_normal h d
    letI := moved_elementary h d
    let q := Recognition.sourceProjection h e hz hn d
    let hq := sourceProjection_surjective_of_nonfrattini h e hz hn d hb hlarge
    let hk := (Recognition.sourceProjection_kernel h e hz hn d).trans
      (moved_centralizer h e hz hn d).symm
    SixCover.IsNaturalOrCore
      (NormalElementaryQuotient.representation (replacementMoved d) q hq hk)
      (MonoidHom.id (Equiv.Perm (Fin 6))) :=
  moved_cover_model h e hz hn d
    (sourceProjection_surjective_of_nonfrattini h e hz hn d hb hlarge)

include h e hz hn in
/-- Apply the new line calculation to the literal ordered orbit selected
for the paired estimate. Its rebased opposite and both index inequalities
are exactly those constructed by exists_orderedOrbit. -/
theorem exists_orderedOrbit_with_critical_line
    (hl : LocalCalculations d.radical (replacementGeometry h d))
    (hb : replacementDistance h d = 2)
    (hlarge : ¬ core d.radical (alpha d.radical) ≤
      (frattini (Q d.radical (alpha d.radical))).map
        (Q d.radical (alpha d.radical)).subtype ⊔ X d.radical (alpha d.radical)) :
    ∃ o : OrderedOrbit (replacementGeometry h d),
      Nat.card (⁅Z d.radical (alpha d.radical),Z d.radical o.c⁆ :
        Subgroup (FreeAmalgam d.radical)) = 2 ∧
      ⁅Z d.radical (alpha d.radical),Z d.radical o.c⁆ ⊓
        centralizer (Ltilde d.radical o.c : Set (FreeAmalgam d.radical)) = ⊥ := by
  obtain ⟨o⟩ := exists_orderedOrbit (replacementGeometry h d)
    (replacement_radical_isPGroup h d) (replacement_core_le_radical h d) hl hb
  exact ⟨o, critical_commutator_card_two h e hz hn d hb hlarge o.critical,
    critical_commutator_inf_opposite_fixed_eq_bot h e hz hn d hb hlarge o.critical⟩

end CFSG.Quasithin.Chapter15.Section03.CharacteristicTwo.RankOneConfiguration.SmallExtension.MarkedMS.AlternatingSixReconstruction.Natural.Exhaustion.DistanceTwo.Geometry.LocalImages
