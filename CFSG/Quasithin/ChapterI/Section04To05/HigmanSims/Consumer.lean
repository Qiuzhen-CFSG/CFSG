module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Reduction
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS

/-!
# The original Chapter 14 consumer of the type-HS reduction

The source local and overgroup constructions give the literal HS1--HS2
configuration. We apply the local core calculation to those actual subgroups,
and expose the independent action-construction and permutation-uniqueness
inputs at the existing recognition consumer. The latter application remains
conditional until `qt-i48-hs-recognition` discharges both inputs. The earlier
Chapter 14 source premises remain with `qt-d-14414-hs-source`.

Source: Aschbacher--Smith, printed pp.418 and 1005.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Subgroup Theory.GroupTheory
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
open Sporadic.LeechRelated.HS
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The original flag has the two characteristic-two local groups of orders
7680 and 10752. This applies the intrinsic calculations to the actual source
centralizer and normalizer, without an additional local-model premise. -/
theorem local_cores_of_local_and_overgroup (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ HigmanSims.TypeAt z V ∧
      Nat.card (HigmanSims.involutionCentralizer z) = 7680 ∧
      Nat.card (normalizer (V : Set G)) = 10752 ∧
      HigmanSims.localCore z = pCore 2 (HigmanSims.involutionCentralizer z) ∧
      generalizedFitting (normalizer (V : Set G)) = pCore 2 (normalizer (V : Set G)) := by
  obtain ⟨z, hz, ht⟩ := type_of_local_and_overgroup d earlier hq chosen
    alternatives F localData overgroup
  exact ⟨z, hz, ht, ht.centralizer_card, ht.normalizer_card,
    ht.centralizer_fitting, ht.normalizer_fitting⟩

/-- Conditional application of the two independent recognition steps to the
existing source consumer. Final assembly must prove both inputs. -/
theorem recognition_of_rank_three_inputs (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F)
    (construct : ∀ (X : Type u) [Group X] [Finite X],
      HigmanSims.IsType X → HasRankThreeAction X)
    (recognize : ∀ P : Subgroup (Equiv.Perm (Fin 100)),
      RankThreeData P → Nonempty (P ≃* Carrier)) : Nonempty (G ≃* Carrier) :=
  recognition_of_local_and_overgroup d earlier hq chosen alternatives F localData
    overgroup (HigmanSims.recognition_of_rank_three construct recognize)

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
