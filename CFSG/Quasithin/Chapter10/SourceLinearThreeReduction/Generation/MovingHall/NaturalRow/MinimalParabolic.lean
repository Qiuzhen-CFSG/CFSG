module
public import CFSG.Quasithin.Chapter10.SourceParabolicAction
public import Theory.SpecificGroups.SL2.SylowUniqueMaximal
public import Theory.SpecificGroups.SL2.SylowConsequences
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.MovingHall.NaturalRow.Quotient
public import Theory.GroupTheory.SylowSubnormalIntersection
public import Theory.GroupTheory.CComponent.SimplePairSylowMaximal

/-!
# The original minimal parabolic in the general even-field row

The original component quotient SL₂(F) has a unique maximal overgroup of
each Sylow two-subgroup. The paired C-component theorem lifts this property
to L₀T, and a nonnormal Sylow in the same quotient excludes Sylow normality.
Thus the original local join is a minimal parabolic without a field-four
restriction. The common-normal theorem applies to that literal join.

Source: Aschbacher–Smith 10.1.2(6) and 10.2.1, printed pp.742–743.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10.MovingHall
open Chapter3.Section02
open scoped MatrixGroups
variable {G F : Type*} [Group G] [Finite G] [Field F] [Finite F] [CharP F 2]

private theorem natural_sylow_not_normal
    (S : Sylow 2 G) (A : Subgroup G) (hA : A.IsCComponent)
    (e : (A ⧸ pCore 2 A) ≃* SL(2,F)) :
    ¬ (S : Subgroup G).Normal := by
  intro hn
  let := hn
  obtain ⟨P, hP⟩ := S.exists_subgroupOf_eq_of_subnormal A hA.subnormal
  let : (P : Subgroup A).Normal := by rw [hP]; infer_instance
  let f := e.toMonoidHom.comp (QuotientGroup.mk' (pCore 2 A))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let Q := P.mapSurjective hf
  have hQ : (Q : Subgroup (SL(2,F))).Normal :=
    (inferInstance : (P : Subgroup A).Normal).map f hf
  exact Matrix.SpecialLinearGroup.no_normal_sylow F 2 Q hQ

variable {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
  (e : (L ⧸ pCore 2 L) ≃* SL(2,F))
include D e

omit [Finite F] [CharP F 2] in
private theorem source_natural_internal :
    (L.subgroupOf (localJoin T L)).IsCComponent ∧
    Nonempty (((L.subgroupOf (localJoin T L)) ⧸ pCore 2 (L.subgroupOf (localJoin T L)))
      ≃* SL(2,F)) ∧
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
private theorem source_natural_nonnormal_index
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    (normalizer (L.subgroupOf (localJoin T L) : Set (localJoin T L))).index = 2 := by
  have hi := source_nonnormal_normalizer_index D.simpleQTKE D.maximal.1 hn
  change (normalizer (L.subgroupOf (componentOrbit L (T : Subgroup G) ⊔
    (T : Subgroup G)) : Set (componentOrbit L (T : Subgroup G) ⊔
    (T : Subgroup G) : Subgroup G))).index = 2
  rw [componentOrbit_sup]
  exact hi

/-- The original nonnormal natural row is a minimal parabolic on its actual
local join and prescribed Sylow subgroup. -/
theorem source_natural_minimal_parabolic
    (n : ℕ) (hnfield : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G)) :
    ChapterB.IsMinimalParabolicOver (T.subtype (show (T : Subgroup G) ≤
      localJoin T L from le_sup_right)) ⊤ := by
  let H := localJoin T L
  let S := T.subtype (show (T : Subgroup G) ≤ H from le_sup_right)
  let A := L.subgroupOf H
  obtain ⟨hA, ⟨eA⟩, hgen⟩ := source_natural_internal D e
  have hlarge : 4 ≤ Nat.card F := by
    rw [hF]
    exact pow_le_pow_right₀ (by decide : 1 ≤ (2:ℕ)) (by omega : 2 ≤ n)
  let : IsSimpleGroup PSL(2,F) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hlarge
  let : IsSimpleGroup SL(2,F) := (Atlas.RankOneFieldAutomorphisms.slEquivPSL (F := F)).isSimpleGroup
  have hu := hA.simple_pair_sylow_unique (fun P => ⟨
    Matrix.SpecialLinearGroup.sylow_hasUniqueMaximalOver 2 P, by
      intro he
      apply Matrix.SpecialLinearGroup.no_normal_sylow F 2 P
      rw [he]
      infer_instance⟩) S A eA (source_natural_nonnormal_index D hn) hgen
  apply (ChapterB.isMinimalParabolicOver_top_iff S).mpr
  obtain ⟨B,hB,huniq⟩ := hu.2
  exact ⟨⟨B,⟨hB.2.isCoatom,hB.1⟩,fun K hK => huniq K ⟨hK.2,hK.1.covBy_top⟩⟩,
    natural_sylow_not_normal S A hA eA⟩

/-- The general-field case of common-normal control retains no minimal-parabolic
premise: 10.1.2(6) is discharged on the original join. -/
theorem source_natural_normalizer_le_of_orbit_sylow
    (n : ℕ) (hnfield : 1 < n) (hF : Nat.card F = 2 ^ n)
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (R : Subgroup G) (hne : R ≠ ⊥) (hRT : R ≤ (T : Subgroup G))
    (hR : (T : Subgroup G) ≤ normalizer (R : Set G))
    (hs : Chapter1.IsSylowIn 2 R (localOrbit T L ⊔ R)) :
    normalizer (R : Set G) ≤ D.maximalLocal := by
  have hp := source_natural_minimal_parabolic D e n hnfield hF hn
  have hu := hasUniqueMaximalOver_map_subtype
    ((ChapterB.isMinimalParabolicOver_iff _ ⊤).mp hp).1
  have he : (((T : Subgroup G).subgroupOf (localJoin T L)).map
      (localJoin T L).subtype) = (T : Subgroup G) :=
    map_subgroupOf_eq_of_le (show (T : Subgroup G) ≤ localJoin T L from le_sup_right)
  have hu' : Order.HasUniqueMaximalOver (T : Subgroup G) (localJoin T L) := he ▸ hu
  exact source_normalizer_le_of_orbit_sylow D hu' R hne hRT hR hs

end CFSG.Quasithin.Chapter10.MovingHall
