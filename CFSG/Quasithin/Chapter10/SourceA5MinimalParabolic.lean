module
public import CFSG.Quasithin.Chapter10.SourceParabolicAction
public import Theory.SpecificGroups.Alternating.FiveSylowMaximal
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.CComponent.A5PairSylowMaximal

/-!
# The original A₅ minimal parabolic in Chapter 10

The nonnormal local component has two Sylow conjugates. Modulo the literal
local two-core these are commuting simple A₅ factors. Borel uniqueness in
each factor and the Sylow element exchanging them give a unique maximal
overgroup of the prescribed Sylow subgroup. The A₅ image also excludes
normality of that Sylow subgroup. Lifting through the two-core proves the
minimal-parabolic premise in the original common-normal and E.2.3 consumers.

Source: Aschbacher–Smith, 10.1.2(6) and 10.2.1, printed pp.742–743.
The full/local module equality and later symmetric-five elimination remain
separate earlier-module and subsequent-local arguments.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
open Theory.SpecificGroups.Alternating.FiveSylowMaximal
variable {G : Type*} [Group G] [Finite G]

private theorem a5_sylow_not_normal
    (S : Sylow 2 G) (A : Subgroup G) (hA : A.IsCComponent)
    (e : (A ⧸ pCore 2 A) ≃* alternatingGroup (Fin 5)) :
    ¬ (S : Subgroup G).Normal := by
  intro hn
  let := hn
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hA.subnormal
  let : (P : Subgroup A).Normal := by rw [hP]; infer_instance
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hf
  have hQ : (Q : Subgroup (alternatingGroup (Fin 5))).Normal :=
    (inferInstance : (P : Subgroup A).Normal).map f hf
  have he : normalizer (Q : Set (alternatingGroup (Fin 5))) = ⊤ :=
    @normalizer_eq_top _ _ (Q : Subgroup (alternatingGroup (Fin 5))) hQ
  exact (sylow_normalizer_isCoatom Q).ne_top he

variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
include D e

private theorem source_a5_internal :
    (L.subgroupOf (localJoin T L)).IsCComponent ∧
    Nonempty (((L.subgroupOf (localJoin T L)) ⧸ pCore 2 (L.subgroupOf (localJoin T L)))
      ≃* alternatingGroup (Fin 5)) ∧
    L.subgroupOf (localJoin T L) ⊔
      ((T.subtype (show (T : Subgroup G) ≤ localJoin T L from le_sup_right) :
        Sylow 2 (localJoin T L)) : Subgroup (localJoin T L)) = ⊤ := by
  let H := localJoin T L
  have hLH : L ≤ H := (le_componentOrbit L T).trans le_sup_left
  have hA : (L.subgroupOf H).IsCComponent := by
    change (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔ (T : Subgroup G))).IsCComponent
    rw [componentOrbit_sup]
    exact D.maximal.1.1
  let a := subgroupOfEquivOfLe hLH
  let b := a.toMonoidHom.pCoreQuotientEquiv (p := 2) a.surjective
    (by rw [a.toMonoidHom.ker_eq_bot a.injective]; exact IsPGroup.of_bot)
  refine ⟨hA, ⟨b.trans e⟩, ?_⟩
  change L.subgroupOf H ⊔ (T : Subgroup G).subgroupOf H = ⊤
  rw [← subgroupOf_sup hLH (show (T : Subgroup G) ≤ H from le_sup_right)]
  have hh : L ⊔ (T : Subgroup G) = H := (componentOrbit_sup L (T : Subgroup G)).symm
  rw [hh, subgroupOf_self]

omit e in
private theorem source_a5_nonnormal_index
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (normalizer (L.subgroupOf (localJoin T L) : Set (localJoin T L))).index = 2 := by
  have hi := source_nonnormal_normalizer_index D.simpleQTKE D.maximal.1 hn
  change (normalizer (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔
    (T : Subgroup G)) : Set (componentOrbit L (T : Subgroup G) ⊔
    (T : Subgroup G) : Subgroup G))).index = 2
  rw [componentOrbit_sup]
  exact hi

/-- The original nonnormal A₅ branch is a minimal parabolic on its actual
local join and prescribed Sylow subgroup. -/
theorem source_a5_minimal_parabolic
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ChapterB.IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤
      localJoin T L from le_sup_right)) ⊤ := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let A := L.subgroupOf H
  obtain ⟨hA, ⟨eA⟩, hgen⟩ := source_a5_internal D e
  have hu := hA.a5_pair_sylow_unique S A eA (source_a5_nonnormal_index D hn) hgen
  apply (ChapterB.isMinimalParabolicOver_top_iff S).mpr
  obtain ⟨B,hB,huniq⟩ := hu.2
  exact ⟨⟨B,⟨hB.2.isCoatom,hB.1⟩,fun K hK => huniq K ⟨hK.2,hK.1.covBy_top⟩⟩,
    a5_sylow_not_normal S A hA eA⟩

/-- The A₅ case of common-normal control retains no minimal-parabolic
premise: 10.1.2(6) is discharged on the original join. -/
theorem source_a5_normalizer_le_of_orbit_sylow
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (R : Subgroup G) (hne : R ≠ ⊥) (hRT : R ≤ (T : Subgroup G))
    (hR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hs : Chapter1.IsSylowIn 2 R (localOrbit T L ⊔ R)) :
    normalizer (R : Set G) ≤ D.maximalLocal := by
  have hp := source_a5_minimal_parabolic D e hn
  have hu := hasUniqueMaximalOver_map_subtype
    ((ChapterB.isMinimalParabolicOver_iff _ ⊤).mp hp).1
  have he : (((T : Subgroup G).subgroupOf (localJoin T L)).map
      (localJoin T L).subtype) = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)
  have hu' : Order.HasUniqueMaximalOver (T : Subgroup G) (localJoin T L) := he ▸ hu
  exact source_normalizer_le_of_orbit_sylow D hu' R hne hRT hR hs

/-- In the actual A₅ branch of 10.2.1, only the earlier full-module equality
remains before the proved E.2.3 alternatives apply. -/
theorem source_a5_baumann_normalizer_or_five_action
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (hfull : D.fullModule = D.moduleSubgroup) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal ∨
      SourceFiveAction D :=
  source_baumann_normalizer_or_five_action D (source_a5_minimal_parabolic D e hn) hfull

end CFSG.Quasithin.Chapter10
