module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.Source
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.LocalStructure.At.SourceConsumer

/-!
# The original HS source branch at G,T

The guarded source proof supplies LocalStructure, and original 14.3.33
now constructs OvergroupStructure on precisely the same flag. Thus both
local inputs of HS1--HS2 are discharged. The isomorphism with the actual
HS carrier and its Theorem-D row retain only the independent I.4.8
recognition premise in addition to the genuine earlier source inputs.

This extension sits above the CaseOneHS umbrella because the guarded
local source already imports that umbrella. Final earlier-source discharge
remains with the original 14.4.14 assembly; I.4.8 remains with its
independent producer.
Source: Aschbacher--Smith, 14.3.26 and 14.3.31--33, printed pp.1001--1005,
and I.4.8, printed p.418.
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

/-- The original guarded hypotheses construct all of 14.3.33's overgroup
output; the local structure is supplied by its completed source proof. -/
theorem source_overgroupStructure_at : OvergroupStructure L F :=
  source_overgroupStructure (SourceAssembly.At.higherRankHypothesis d earlier hq chosen)
    structural alternatives F
    (Centerless.source_localStructure_at d earlier hq chosen structural alternatives
      F hne classification hZ) hne

/-- HS1--HS2 with both original local source structures discharged. -/
theorem type_of_source_at :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V :=
  type_of_source_and_overgroup_at d earlier hq chosen structural alternatives F hne classification hZ
    (source_overgroupStructure_at d earlier hq chosen structural alternatives F hne classification hZ)

/-- The separately conditional original nonextraspecial HS conclusion.
The independent recognition theorem I.4.8 remains explicit. -/
theorem recognition_of_source_at (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) :=
  recognition_of_source_and_overgroup_at d earlier hq chosen structural alternatives F hne classification hZ
    (source_overgroupStructure_at d earlier hq chosen structural alternatives F hne classification hZ)
    recognition

/-- The literal HS row for the parent's Theorem-D assembly, conditional only
on I.4.8 and its genuine earlier source inputs. -/
theorem theoremDModel_of_source_at (recognition : HigmanSims.Recognition.{u}) :
    ClassificationModels.IsTheoremDModel G :=
  theoremDModel_of_source_and_overgroup_at d earlier hq chosen structural alternatives F hne classification hZ
    (source_overgroupStructure_at d earlier hq chosen structural alternatives F hne classification hZ)
    recognition

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
