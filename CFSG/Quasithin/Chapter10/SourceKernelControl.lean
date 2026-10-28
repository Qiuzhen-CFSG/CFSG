module
public import CFSG.Quasithin.Chapter10.SourceSetup
public import CFSG.Quasithin.Chapter3.Section02.LocalCentralizer
public import CFSG.Quasithin.Chapter3.Section02.CenterObstruction
public import Theory.GroupTheory.MaximalTwoLocalOvergroups
public import Theory.GroupTheory.ElementaryThompsonRelative

/-!
# Normalizer control for the original full-module Sylow kernel

The full orbit V_M contains the local module V_T, whose Sylow centralizer
is O₂(L₀T). Therefore C_T(V_M)=O₂(L₀T)∩C_G(V_M) is normal in L₀T.
The nonzero elementary V_M lies in this kernel. Source uniqueness for
L₀T consequently controls the normalizer of the kernel and of its
nonzero Thompson subgroup, giving both literal unique-overgroup assertions.

These are the normality and uniqueness clauses of10.1.2(3), including the
exceptional module row. The source row-specific equality with O₂(L₀T)
requires the separate module classification and is not asserted here.
The actual weak-closure consumer discharges the earlier1.2.7 premise.
Source: Aschbacher–Smith, combined manuscript of1 March2004,
10.1.2(3), printed p.742, and E.3.36(1), printed p.239.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {K : GroupClass.{u}}
  {T : Sylow 2 G} {L : Subgroup G} (D : FundamentalSetup K T L)
  (h127 : Chapter1.Section02.NonsolvableUniquenessConclusion T L)

include h127

/-- The centralizer in T of the full original orbit module is the intersection
of the original local core and the full-module centralizer. -/
theorem source_full_sylow_centralizer_eq :
    (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) =
      (localJoin T L).pCoreIn 2 ⊓ centralizer (D.fullModule : Set G) := by
  apply le_antisymm
  · refine le_inf ?_ inf_le_right
    rw [← D.sylow_centralizer_module h127]
    exact inf_le_inf_left _ (centralizer_le (le_componentOrbit D.moduleSubgroup D.maximalLocal))
  · apply inf_le_inf_right
    simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le le_sup_right] using
      pCoreIn_le_sylow (localJoin T L) (T.subtype le_sup_right)

/-- Source10.1.2(3)'s normality conclusion, including its exceptional row. -/
theorem source_join_normalizes_full_sylow_centralizer :
    localJoin T L ≤ normalizer
      ((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) : Set G) := by
  have he := congrArg (fun R : Subgroup G => normalizer (R : Set G))
    (source_full_sylow_centralizer_eq D h127)
  apply le_trans ?_ he.ge
  exact (le_inf ((localJoin T L).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image (localJoin T L) (pCore 2 (localJoin T L))))
    ((D.lemma_3_2_3_uniqueness h127).2.1.trans
      (D.maximalLocal_normalizes_fullModule.trans (normalizer_le_normalizer_centralizer _)))).trans
        inf_normalizer_le_normalizer_inf

/-- The same kernel is nonzero: it contains the nonzero elementary full module. -/
theorem source_full_sylow_centralizer_ne_bot :
    (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) ≠ ⊥ := by
  let := D.fullModule_elementary h127
  have hv : D.fullModule ≤ (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) :=
    le_inf (D.fullModule_le_sylow h127) (le_centralizer _)
  intro he
  exact D.module_ne_bot (bot_unique
    (((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans hv).trans_eq he))

/-- The ambient normalizer of the actual C_T(V_M) is contained in M. -/
theorem source_full_sylow_centralizer_normalizer_le :
    normalizer ((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) : Set G) ≤
      D.maximalLocal :=
  normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness h127).2.2
    (T.isPGroup'.to_le inf_le_left) (source_full_sylow_centralizer_ne_bot D h127)
    (source_join_normalizes_full_sylow_centralizer D h127)

/-- Source10.1.2(3)'s analogous normalizer bound for J(C_T(V_M)). -/
theorem source_kernel_thompson_normalizer_le :
    normalizer (elementaryAbelianMaxJ
      ((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G)) : Set G) ≤ D.maximalLocal := by
  let R := (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G)
  have hp : IsPGroup 2 R := T.isPGroup'.to_le inf_le_left
  exact normalizer_le_of_unique_maximalTwoLocal (D.lemma_3_2_3_uniqueness h127).2.2
    (hp.to_le (show elementaryAbelianMaxJ R ≤ R from sSup_le fun _ hA => hA.1))
    (elementaryAbelianMaxJ_ne_bot_of_finite_pGroup R hp
      (source_full_sylow_centralizer_ne_bot D h127))
    ((source_join_normalizes_full_sylow_centralizer D h127).trans
      (normalizer_le_normalizer_elementaryAbelianMaxJ R))

/-- The first exact uniqueness equality in source10.1.2(3). -/
theorem source_full_sylow_centralizer_unique :
    maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) : Subgroup G) : Set G)) =
      {D.maximalLocal} := by
  ext M
  constructor
  · rintro ⟨hm, hle⟩
    exact Set.mem_singleton_iff.mpr ((D.lemma_3_2_3_uniqueness h127).2.2 M hm
      ((source_join_normalizes_full_sylow_centralizer D h127).trans hle))
  · intro hm
    rw [Set.mem_singleton_iff] at hm
    subst M
    exact ⟨(D.lemma_3_2_3_uniqueness h127).1,
      source_full_sylow_centralizer_normalizer_le D h127⟩

/-- The second exact uniqueness equality in source10.1.2(3). -/
theorem source_kernel_thompson_unique :
    maximalTwoLocalOvergroups (normalizer (elementaryAbelianMaxJ
      ((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G)) : Set G)) =
      {D.maximalLocal} := by
  ext M
  constructor
  · rintro ⟨hm, hle⟩
    exact Set.mem_singleton_iff.mpr ((D.lemma_3_2_3_uniqueness h127).2.2 M hm
      (((source_join_normalizes_full_sylow_centralizer D h127).trans
        (normalizer_le_normalizer_elementaryAbelianMaxJ
          ((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G)))).trans hle))
  · intro hm
    rw [Set.mem_singleton_iff] at hm
    subst M
    exact ⟨(D.lemma_3_2_3_uniqueness h127).1,
      source_kernel_thompson_normalizer_le D h127⟩

end CFSG.Quasithin.Chapter10
