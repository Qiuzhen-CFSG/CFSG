module
public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceEight.OriginalCharacteristicFour
public import Theory.GroupTheory.FourGroupDisplacement
/-!
# The possible original-core displacement of the source four-group

The source four-group is the third lower-central subgroup of the original
commutator core. Since the component and the two-core are characteristic in
J, this four-group is characteristic in J. A two-group action on a four-group
is quadratic, so its displacement by O2(J) centralizes O2(J). It also lies
in the four-group and hence centralizes L. As O2(J)L = J, the displacement
is central in J, and a nontrivial displacement has order two.

The displacement is characteristic in J. MS3 shows that a nontrivial one
cannot be characteristic in the original radical R. Excluding this residual
action, rather than confusing these two characteristicity statements, remains
with qt-rank-two-ms93. The literal SmallMSPair application is in
`LinearThree.DistanceEightDisplacement`; no fixed-factor equality is needed
for the statements about the source four-group here.

Source: MS93 (4.4)--(4.5), printed pp.890--900, and Section 7, pp.932--933;
Aschbacher--Smith C.1.34(4), printed pp.136--137.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
universe u
variable {J : Type u} [Group J] [Finite J] {κ : GroupClass.{u}}
  {L R : Subgroup J} {h : Input κ L R} (t : InputSetup h)
  (common : CommonFacts t.reduction.radical t.source t.geometry)
  (earlier : DistanceEight.CoreFactors.Earlier t.reduction.radical t.geometry)

include common earlier

/-- The four-group is characteristic in the original group, not only normal in the replacement. -/
theorem reducedCentralFour_characteristic : t.reducedCentralFour.Characteristic := by
  let := h.component_characteristic
  rw [t.reducedCentralFour_eq_third_commutator common earlier]
  infer_instance

/-- Any remaining displacement of the source four by the original two-core
is central in the original group. -/
theorem reducedCentralFour_core_displacement_central :
    ⁅t.reducedCentralFour,pCore 2 J⁆ ≤ center J := by
  let := t.reducedCentralFour_characteristic common earlier
  have hcore : ⁅t.reducedCentralFour,pCore 2 J⁆ ≤ centralizer (pCore 2 J : Set J) :=
    commutator_four_le_centralizer t.reducedCentralFour (pCore 2 J)
      (by rw [normalizer_eq_top]; exact le_top) pCore_isPGroup
      (t.reducedCentralFour_card common earlier)
  have hL : ⁅t.reducedCentralFour,pCore 2 J⁆ ≤ centralizer (L : Set J) :=
    (commutator_le_left _ _).trans (t.reducedCentralFour_centralizes_component earlier)
  apply centralizer_eq_top_iff_subset.mp
  apply top_unique
  rw [← h.core_sup_component]
  exact sup_le (le_centralizer_iff.mp hcore) (le_centralizer_iff.mp hL)

/-- A nontrivial original action has displacement exactly a central line. -/
theorem reducedCentralFour_core_displacement_card
    (hne : ⁅t.reducedCentralFour,pCore 2 J⁆ ≠ ⊥) :
    Nat.card (⁅t.reducedCentralFour,pCore 2 J⁆ : Subgroup J) = 2 := by
  let := t.reducedCentralFour_characteristic common earlier
  exact commutator_four_card_of_ne_bot t.reducedCentralFour (pCore 2 J)
    (by rw [normalizer_eq_top]; exact le_top) pCore_isPGroup
    (t.reducedCentralFour_card common earlier) hne

/-- The displacement itself is characteristic in the original group. -/
theorem reducedCentralFour_core_displacement_characteristic :
    (⁅t.reducedCentralFour,pCore 2 J⁆).Characteristic := by
  let := t.reducedCentralFour_characteristic common earlier
  infer_instance

/-- MS3 makes a surviving central displacement line fail characteristicity
in the original radical. Ambient characteristicity alone is insufficient. -/
theorem reducedCentralFour_core_displacement_not_characteristic_radical
    (hne : ⁅t.reducedCentralFour,pCore 2 J⁆ ≠ ⊥) :
    ¬ ((⁅t.reducedCentralFour,pCore 2 J⁆).subgroupOf R).Characteristic := by
  intro hchar
  let := hchar
  let D := ⁅t.reducedCentralFour,pCore 2 J⁆
  have hDR : D ≤ R := (commutator_le_right _ _).trans h.radical.twoCore_le
  let := t.reducedCentralFour_core_displacement_characteristic common earlier
  have hnorm : ((D.subgroupOf R).map R.subtype).Normal := by
    rw [map_subgroupOf_eq_of_le hDR]
    infer_instance
  have hbot := h.characteristic.eq_bot_of_normal (D.subgroupOf R) hnorm
  have hm := congrArg (map R.subtype) hbot
  rw [map_subgroupOf_eq_of_le hDR,Subgroup.map_bot] at hm
  exact hne hm
end CFSG.Quasithin.ChapterC.BinaryMS.MS93.InputSetup
