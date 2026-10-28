module
public import CFSG.Quasithin.Chapter10.SourceKernelControl
public import CFSG.Quasithin.ChapterE.Section03.SourceContainment

/-!
# Weak-closure bounds for the original Chapter 10 full module

The source Fundamental Setup gives the elementary full orbit V_M and its
normalizer M. The original local-centralizer theorem makes C_T(V_M) normal
in L₀T, so the source uniqueness theorem gives exactly the singleton
maximal-overgroup hypothesis used by E.3.35. The centralizer of V_M is
already contained in M and the overgroup Sylow is the original T.

Consequently every solvable Sylow overgroup outside M forces min(w,r)≤1;
the attained positive generation-parameter branch gives min(w,r)≤n(H).
These are numerical inputs for the original argument in 10.2–10.3. The
independent marked-module and parameter bounds needed for 10.2.13 remain
separate source obligations. All earlier uniqueness premises are discharged
here by the proved source A and C theorems.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
10.1.2(3), printed p.742; E.3.35–36, pp.238–239; 10.3.3, p.769.
-/

public noncomputable section
open Subgroup Theory.GroupTheory Stellmacher
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

include D

private theorem source_uniqueness :
    Chapter1.Section02.NonsolvableUniquenessConclusion T L :=
  Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal

/-- The actual original full orbit supplies E.3.22 without a local setup premise. -/
theorem source_fullModule_weakClosure_hypotheses [IsElementaryAbelian 2 D.fullModule] :
    ChapterE.HypothesisE322 D.fullModule T := by
  refine ⟨?_, D.fullModule_le_sylow (source_uniqueness D),
    (le_normalizer_componentOrbit L T).trans D.maximalLocal_normalizes_fullModule⟩
  intro he
  exact D.module_ne_bot (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans_eq he))

/-- E.3.36(1) for the original Chapter10 module, with its earlier uniqueness
premise discharged by the proved source A and C theorems. -/
theorem source_fullModule_kernel_unique :
    maximalTwoLocalOvergroups (normalizer
      (((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) : Subgroup G) : Set G)) =
      {D.maximalLocal} :=
  source_full_sylow_centralizer_unique D (source_uniqueness D)

/-- The original zeroth weak closure has its full ambient normalizer in M
whenever the source weak-closure parameter is positive. -/
theorem source_weakClosure_zero_normalizer
    (hw : 0 < ChapterE.globalW D.fullModule (T : Subgroup G)) :
    normalizer (ChapterE.indexedWeakClosure D.fullModule (T : Subgroup G) 0 : Set G) ≤
      D.maximalLocal := by
  let := D.fullModule_elementary (source_uniqueness D)
  exact ChapterE.SourceContainment.normalizer_weakClosure_zero_le
    (source_fullModule_weakClosure_hypotheses D) hw (source_fullModule_kernel_unique D)

/-- A solvable Sylow overgroup outside M forces one of the literal original
weak-closure parameters to be at most one. This is the solved E.3.35 branch
used in the opening of source10.3.3, before the remaining parameter bounds. -/
theorem source_solvable_overgroup_weakClosure_bound
    {H : Subgroup G} [Group.IsSolvable H] (hTH : (T : Subgroup G) ≤ H)
    (hHM : ¬ H ≤ D.maximalLocal) :
    min (ChapterE.globalW D.fullModule (T : Subgroup G))
      (ChapterE.globalR D.fullModule) ≤ 1 := by
  let := D.fullModule_elementary (source_uniqueness D)
  apply le_of_not_gt
  intro hwr
  apply hHM
  apply ChapterE.SourceContainment.le_of_solvable
    (source_fullModule_weakClosure_hypotheses D) (T.subtype hTH)
    (source_fullModule_kernel_unique D)
  · exact inf_le_right.trans ((centralizer_le_normalizer (D.fullModule : Set G)).trans
      (source_fullModule_normalizer D).le)
  · simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      (inf_le_left : (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) ≤ T)
  · exact hwr

/-- The general attained E-generation branch also retains the original module
and overgroup, with the uniqueness and centralizer hypotheses discharged. -/
theorem source_overgroup_generation_bound
    {H : Subgroup G} (hTH : (T : Subgroup G) ≤ H) (hHM : ¬ H ≤ D.maximalLocal)
    (hpos : 0 < ChapterE.generationParameter H) :
    min (ChapterE.globalW D.fullModule (T : Subgroup G))
      (ChapterE.globalR D.fullModule) ≤ (ChapterE.generationParameter H : ℕ∞) := by
  let := D.fullModule_elementary (source_uniqueness D)
  apply le_of_not_gt
  intro hn
  apply hHM
  apply ChapterE.SourceContainment.le_of_generationParameter_pos
    (source_fullModule_weakClosure_hypotheses D) (T.subtype hTH)
    (source_fullModule_kernel_unique D)
  · exact inf_le_right.trans ((centralizer_le_normalizer (D.fullModule : Set G)).trans
      (source_fullModule_normalizer D).le)
  · simpa only [Sylow.coe_subtype, map_subgroupOf_eq_of_le hTH] using
      (inf_le_left : (T : Subgroup G) ⊓ centralizer (D.fullModule : Set G) ≤ T)
  · exact hpos
  · exact hn

end CFSG.Quasithin.Chapter10
