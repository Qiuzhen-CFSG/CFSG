module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.Centerless.Source
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Assembly

/-!
# Applying the completed HS local source theorem

The proved centerlessness theorem discharges the independent action theorem's
premise; together they construct LocalStructure on the actual flag. Applying
that result to the HS1--HS2 assembly removes both local action and centerlessness
from the parent consumer. OvergroupStructure and I.4.8 recognition are the
independently owned remaining HS premises.

This application retains the original universal earlier-source interfaces.
The separate At assembly shows the final consumer needs only their values at
G,T, but the source proof still needs localization before the final guarded D
producers can supply those values. No universal record is inferred from At.
Source: Aschbacher--Smith 14.3.31--33 and I.4.8, pp.1002--1005,418.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}
variable (d : Counterexample T L) (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222 KnownSimple.IsKnownSimple.{u})
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1)
include d earlier hq chosen structural alternatives hne classification hZ

/-- The original source theorem supplies LocalStructure to the literal
HS1--HS2 assembly; no independent local action premise remains. -/
theorem type_of_source_and_overgroup (overgroup : OvergroupStructure L F) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V :=
  type_of_local_and_overgroup_at d (earlier G T) hq chosen (alternatives.at T) F
    (Centerless.source_localStructure d earlier hq chosen structural alternatives
      F hne classification hZ) overgroup

/-- The completed local source theorem feeds the actual HS isomorphism,
retaining precisely the parent's overgroup and I.4.8 premises. -/
theorem recognition_of_source_and_overgroup (overgroup : OvergroupStructure L F)
    (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z, _, hz⟩ := type_of_source_and_overgroup d earlier hq chosen structural
    alternatives F hne classification hZ overgroup
  exact recognition G ⟨z, V, hz⟩

/-- The recognized HS carrier gives its literal exceptional Theorem-D row. -/
theorem theoremDModel_of_source_and_overgroup (overgroup : OvergroupStructure L F)
    (recognition : HigmanSims.Recognition.{u}) : ClassificationModels.IsTheoremDModel G :=
  .exceptional (.sporadic .hs (by simp)
    (recognition_of_source_and_overgroup d earlier hq chosen structural alternatives
      F hne classification hZ overgroup recognition))

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
