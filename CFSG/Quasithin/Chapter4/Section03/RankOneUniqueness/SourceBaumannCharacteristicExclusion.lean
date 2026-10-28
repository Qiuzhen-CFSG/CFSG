module

public import CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness.Configuration
public import CFSG.Quasithin.ChapterB.Section02.Thompson
public import Stellmacher.BaumannNormalizer

/-!
# The original crossing excludes a normal characteristic Baumann subgroup

The crossing element normalizes the actual Sylow intersection and hence its
Baumann subgroup and every characteristic subgroup of it. If the selected
component also normalizes a nonzero such subgroup, the strict-overgroup
uniqueness clause places its normalizer in N(L), contradicting component
escape. This discharges the normal-characteristic exit of C.1.24 before
shortness or any block-module identification has been established.

Source: Aschbacher--Smith, original 4.3.3--7 and C.1.24(a), printed
pp.614--616 and130--131.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

/-- The selected component cannot normalize a nonzero characteristic subgroup
of the Baumann subgroup of the original Sylow intersection. -/
theorem SourceConfiguration.no_component_normalized_characteristic_baumann
    (c : SourceConfiguration T L)
    (A : Subgroup (ChapterB.baumann ((T : Subgroup G) ⊓ c.H)))
    [A.Characteristic] (hne : A ≠ ⊥)
    (hn : c.K.map c.H.subtype ≤ normalizer
      (A.map (ChapterB.baumann ((T : Subgroup G) ⊓ c.H)).subtype : Set G)) : False := by
  let S := (T : Subgroup G) ⊓ c.H
  let B := ChapterB.baumann S
  let U := A.map B.subtype
  have hU : U ≠ ⊥ := fun h => hne ((A.map_eq_bot_iff_of_injective B.subtype_injective).mp h)
  have hUS : U ≤ S := (map_subtype_le A).trans inf_le_left
  have hp : IsPGroup 2 U := T.isPGroup'.to_le (hUS.trans inf_le_left)
  have hcontrol : normalizer (S : Set G) ≤ normalizer (U : Set G) :=
    (Stellmacher.normalizer_le_normalizer_baumann S).trans
      (normalizer_le_normalizer_characteristic_image B A)
  have hnorm : L ⊔ (S ⊔ zpowers c.t) ≤ normalizer (U : Set G) :=
    sup_le (c.le_component.trans hn)
      (sup_le (S.le_normalizer.trans hcontrol)
        (zpowers_le.mpr (hcontrol c.crossing_normalizes)))
  exact c.component_outside (hn.trans (c.crossing_normalizer_control hp hU hnorm))

end CFSG.Quasithin.Chapter4.Section03.RankOneUniqueness
