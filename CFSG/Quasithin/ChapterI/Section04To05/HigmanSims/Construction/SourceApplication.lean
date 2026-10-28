module

public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.SeedGeometry
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.AmbientControl
public import CFSG.Quasithin.ChapterI.Section04To05.HigmanSims.Construction.MathieuCosets
public import CFSG.Quasithin.Chapter14.Section04.CaseOneHS

/-!
# Seed geometry on the original Chapter 14 subgroups

The original local and overgroup structures supply HS1--HS2. Applying the
seed-action and overlap theorems proves the centralizer equality, full
automorphism action, and common local Sylow arrangement for the same V and L.
No additional action or fusion hypothesis is needed.
The ambient-control application also supplies a common ambient Sylow subgroup
of order 512 and the vanishing of both ambient normal cores.

The earlier Chapter 14 structures remain the inputs owned by
`qt-d-14414-hs-source`. These applications do not construct the M₂₂ subgroup.
The final adapters prove faithfulness and turn an actual index-100
Mathieu subgroup with the specified suborbits into the degree-100 action.
The subgroup, index and orbit clauses remain with the construction owner.

Source: Aschbacher--Smith, printed pp.418 and 1005.
-/

public section
namespace CFSG.Quasithin.Chapter14.Section04.CaseOneHS
open Subgroup Theory.GroupTheory
open Chapter12.Section02 Chapter12.Section08 Chapter12.Section08.InvariantFlag
open Chapter14.Section03.CaseOneSource
open Chapter13.Section08.TransvectionRecognition.Component.ModelExtension
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L V : Subgroup G}

/-- The full seed action and compatible local Sylows follow on the actual
Chapter 14 subgroups, without an extra local-fusion premise. -/
theorem seed_geometry_of_local_and_overgroup (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F) :
    ∃ z : G, F.Vi 1 = zpowers z ∧ z ∈ V ∧
      centralizer (V : Set G) = (pCore 2 L).map L.subtype ∧
      Function.Surjective V.normalizerMonoidHom ∧
      Nat.card (HigmanSims.involutionCentralizer z ⊓ L : Subgroup G) = 1536 ∧
      ∃ (S : Sylow 2 (HigmanSims.involutionCentralizer z)) (P : Sylow 2 L),
        (S : Subgroup (HigmanSims.involutionCentralizer z)).map
          (HigmanSims.involutionCentralizer z).subtype =
          (P : Subgroup L).map L.subtype ∧ Nat.card S = 512 := by
  obtain ⟨z, hz, ht⟩ := type_of_local_and_overgroup d earlier hq chosen
    alternatives F localData overgroup
  have hc := ht.seed_centralizer
  have hi := ht.local_intersection_card
  have hs := ht.exists_common_local_sylow
  rw [overgroup.seed_normalizer] at hc hi hs
  exact ⟨z, hz, ht.involution_mem_seed, hc, ht.seed_action_surjective, hi, hs⟩

/-- Ambient Sylow control and trivial two- and odd cores hold for the original
Chapter 14 configuration, with its literal seed normalizer L. -/
theorem ambient_control_of_local_and_overgroup (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F) :
    pCore 2 G = ⊥ ∧ pPrimeCore 2 G = ⊥ ∧
      ∃ z : G, F.Vi 1 = zpowers z ∧
        ∃ S : Sylow 2 G, (S : Subgroup G) ≤ HigmanSims.involutionCentralizer z ⊓ L ∧
          Nat.card S = 512 := by
  obtain ⟨z, hz, ht⟩ := type_of_local_and_overgroup d earlier hq chosen
    alternatives F localData overgroup
  have hs := ht.exists_common_ambient_sylow
  rw [overgroup.seed_normalizer] at hs
  exact ⟨ht.ambient_twoCore_eq_bot, ht.ambient_oddCore_eq_bot, z, hz, hs⟩

/-- Faithfulness of an actual Mathieu coset action on the original Chapter 14
configuration follows from the supplied local and overgroup structures. -/
theorem mathieu_coset_faithful_of_local_and_overgroup (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F) (K : Subgroup G)
    (eK : K ≃* Sporadic.Mathieu.M22) :
    Function.Injective (MulAction.toPermHom G (G ⧸ K)) := by
  obtain ⟨z, _, ht⟩ := type_of_local_and_overgroup d earlier hq chosen
    alternatives F localData overgroup
  exact ht.m22_coset_faithful K eK

/-- The actual subgroup index and suborbits discharge the degree-100 action
premise, with no ambient simplicity or order input. Their construction remains
with the type-HS construction owner. -/
theorem rank_three_action_of_local_and_overgroup_cosets (d : Counterexample T L)
    (earlier : Earlier1332CaseOne.{u})
    (hq : ClassicalGroup.IsPSL (L ⧸ pCore 2 L) 3 2) (chosen : ChosenModule T L V)
    (alternatives : Theorem12213 KnownSimple.IsKnownSimple.{u})
    (F : InvariantFlag T V 3) (localData : LocalStructure L F)
    (overgroup : OvergroupStructure L F) (K : Subgroup G)
    (eK : K ≃* Sporadic.Mathieu.M22) (hi : K.index = 100)
    (hrank : Nat.card (MulAction.orbitRel.Quotient K (G ⧸ K)) = 3)
    (hsub : ∃ x : G ⧸ K, Nat.card (MulAction.orbit K x) = 22) :
    Sporadic.LeechRelated.HS.HasRankThreeAction G := by
  obtain ⟨z, _, ht⟩ := type_of_local_and_overgroup d earlier hq chosen
    alternatives F localData overgroup
  exact ht.rank_three_action_of_mathieu_cosets K eK hi hrank hsub

end CFSG.Quasithin.Chapter14.Section04.CaseOneHS
