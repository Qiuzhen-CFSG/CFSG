module

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroups

public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.Recognition
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelations
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsCommutator
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalRelationsLabels
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.MathieuRadiusThree.LocalGroupsCore
public import CFSG.Quasithin.ChapterF.Section06.SourceAssembly.SmallAmalgams.Goldschmidt.CanonicalLabelCenter

/-!
# Assembly of the radius-three source branch

The local-action and six-arc calculation is proved in `LocalRelations`.
The generated endpoint groups are identified from the original source
hypotheses in `LocalGroups`. Together with the overlap compatibility proved
in `Recognition`, these calculations supply the exact unconditional
`RadiusThreeMarkedInput` used by `marked_base_of_source_cuts`.

Source: Goldschmidt, *Automorphisms of trivalent graphs* (1980),
(6.12), pp.403--406.
-/

public section
namespace CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
universe u

theorem radiusThreeMarkedInput_of_local_relations
    (relations : LocalRelationsInput.{u}) (groups : LocalGroupsInput.{u}) :
    RadiusThreeMarkedInput.{u} := by
  intro G _ F s h d hr
  exact marked_of_endpointTypes h d
    (groups G F s h d hr (relations G F s h d hr))

/-- Actual consumer application, retaining only the independently owned
source calculations and the earlier label/radius/radius-two branches. -/
theorem marked_base_of_mathieu_source_cuts
    (labels : CanonicalLabelsInput.{u}) (radius : CanonicalRadiusInput.{u})
    (two : RadiusTwoMarkedInput.{u})
    (relations : LocalRelationsInput.{u}) (groups : LocalGroupsInput.{u})
    {G : Type u} [Group G] {F : Bool → Subgroup G} {s : ℕ}
    (h : LargeTreeSource F s) : DerivedMarkedBase F ∨ MathieuMarkedBase F :=
  marked_base_of_source_cuts labels radius two
    (radiusThreeMarkedInput_of_local_relations relations groups) h

/-- The radius-three source assembly now retains only the independently
owned recognition of the two generated endpoint groups. -/
theorem radiusThreeMarkedInput_of_local_groups (groups : LocalGroupsInput.{u}) :
    RadiusThreeMarkedInput.{u} :=
  radiusThreeMarkedInput_of_local_relations localRelationsInput groups

/-- Source-cut consumer with the local relations discharged from the original
large tree action and radius-three hypotheses. -/
theorem marked_base_of_mathieu_local_groups
    (labels : CanonicalLabelsInput.{u}) (radius : CanonicalRadiusInput.{u})
    (two : RadiusTwoMarkedInput.{u}) (groups : LocalGroupsInput.{u})
    {G : Type u} [Group G] {F : Bool → Subgroup G} {s : ℕ}
    (h : LargeTreeSource F s) : DerivedMarkedBase F ∨ MathieuMarkedBase F :=
  marked_base_of_source_cuts labels radius two
    (radiusThreeMarkedInput_of_local_groups groups) h


/-- Goldschmidt's radius-three recognition, including its original endpoint
carriers and compatible marking of their actual intersection. -/
theorem radiusThreeMarkedInput : RadiusThreeMarkedInput.{u} :=
  radiusThreeMarkedInput_of_local_groups localGroupsInput

/-- The literal source-cut consumer, with the radius-three local relations,
endpoint recognition and overlap compatibility all discharged. -/
theorem marked_base_of_mathieu_source
    (labels : CanonicalLabelsInput.{u}) (radius : CanonicalRadiusInput.{u})
    (two : RadiusTwoMarkedInput.{u})
    {G : Type u} [Group G] {F : Bool → Subgroup G} {s : ℕ}
    (h : LargeTreeSource F s) : DerivedMarkedBase F ∨ MathieuMarkedBase F :=
  marked_base_of_source_cuts labels radius two radiusThreeMarkedInput h


end CFSG.Quasithin.ChapterF.SourceAssembly.Goldschmidt.MathieuRadiusThree
