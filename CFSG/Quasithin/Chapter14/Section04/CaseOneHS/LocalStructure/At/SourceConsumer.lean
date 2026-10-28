module

public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Source
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.Assembly

/-!
# The guarded HS local source theorem in the classification consumer

The earlier source implications are used only at the original G,T.
The proved source_localStructure_at supplies centerlessness, the embedded
central product, the natural action and its component to HS1--HS2 for the
same point and seed. The resulting isomorphism supplies the literal HS row
of Theorem D.

The independent original 14.3.33 overgroup/transfer proof remains with
qt-d-14414-hs-source; I.4.8 remains with qt-i48-hs-recognition. The final
D owner qt-d-14414-source retains discharge of the authorized earlier
structural, naturality and faithful-classification inputs.
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
variable (d : Counterexample T L) (earlier : Earlier1332CaseOneAt T)
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (hne : ¬ IsMulCommutative F.U)
    (classification : LargerDimension.LocalAction.Components.EarlierFaithfulClassification G T)
    (hZ : F.ZU ≠ F.Vi 1)
include d earlier hq chosen structural alternatives hne classification hZ

/-- The original source theorem supplies LocalStructure to the literal
HS1--HS2 assembly; no independent local action premise remains. -/
theorem type_of_source_and_overgroup_at (overgroup : OvergroupStructure L F) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V :=
  type_of_local_and_overgroup_at d earlier hq chosen alternatives F
    (Centerless.source_localStructure_at d earlier hq chosen structural alternatives
      F hne classification hZ) overgroup

/-- The completed local source theorem feeds the actual HS isomorphism,
retaining precisely the parent's overgroup and I.4.8 premises. -/
theorem recognition_of_source_and_overgroup_at (overgroup : OvergroupStructure L F)
    (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) := by
  obtain ⟨z, _, hz⟩ := type_of_source_and_overgroup_at d earlier hq chosen structural
    alternatives F hne classification hZ overgroup
  exact recognition G ⟨z, V, hz⟩

/-- The recognized HS carrier gives its literal exceptional Theorem-D row. -/
theorem theoremDModel_of_source_and_overgroup_at (overgroup : OvergroupStructure L F)
    (recognition : HigmanSims.Recognition.{u}) : ClassificationModels.IsTheoremDModel G :=
  .exceptional (.sporadic .hs (by simp)
    (recognition_of_source_and_overgroup_at d earlier hq chosen structural alternatives
      F hne classification hZ overgroup recognition))

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
