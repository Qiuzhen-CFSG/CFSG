module
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.Consumer
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS.Overgroup.OuterExclusion

/-!
# Original 14.3.33 and the conditional HS recognition application

The source point-core equality, obtained by excluding the order-eight
cubic centralizer with extremal transfer, closes every overgroup field.
Together with the homocyclic core construction it gives the literal
normalizers N_G(V)=N_G(L)=L and the original HS1--HS2 configuration.
I.4.8 remains an explicit recognition premise in the separately named
isomorphism application.

Source: Aschbacher--Smith, 14.3.33 and the final paragraph of 14.3,
printed pp.1004--1005; I.4.8, printed p.418.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- Original 14.3.33 from the supplied natural setup and explicit 14.3.32.
No core, normalizer, transfer or homocyclic conclusion remains an input. -/
theorem source_overgroupStructure
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) : OvergroupStructure L F :=
  overgroupStructure_of_closure_core h structural alternatives F localData hne
    (Overgroup.source_closure_core h structural alternatives F localData hne)

/-- The completed overgroup construction supplies the exact HS type at the
original point and seed, under the earlier local-structure premise. -/
theorem type_of_higherRank_local
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V :=
  type_of_higherRank_local_and_overgroup h alternatives F localData
    (source_overgroupStructure h structural alternatives F localData hne)

/-- Conditional I.4.8 application after the complete original overgroup proof. -/
theorem recognition_of_higherRank_local
    (h : HigherRankHypothesis KnownSimple.IsKnownSimple T L V 3)
    (structural : Structural1222At KnownSimple.IsKnownSimple T)
    (alternatives : Theorem12213At KnownSimple.IsKnownSimple T)
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (hne : ¬ IsMulCommutative F.U) (recognition : HigmanSims.Recognition.{u}) :
    Nonempty (G ≃* Sporadic.LeechRelated.HS.Carrier) :=
  recognition_of_higherRank_local_and_overgroup h alternatives F localData
    (source_overgroupStructure h structural alternatives F localData hne) recognition

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
