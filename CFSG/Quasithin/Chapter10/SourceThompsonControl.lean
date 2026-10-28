module
public import CFSG.Quasithin.Chapter10.SourceWeakClosure
public import CFSG.Quasithin.ChapterB.Section02.UniqueOffender
public import Stellmacher.ElementaryAbelianMaxJWeakClosure
public import CFSG.Quasithin.Chapter3.Section02.SourceBaumann
public import CFSG.Quasithin.Chapter3.Section01.CommonNormalKnownSimple
public import CFSG.Quasithin.Chapter3.Section01.StandingGuard

/-!
# Thompson control in the original Fundamental Setup

If J(T) centralizes the full source module, its Thompson kernel is J(T).
Source uniqueness therefore controls N_G(J(T)). Weak closure and Thompson
heredity then give J(S)=J(T) and N_G(S)≤M for every two-subgroup containing
J(T), including the actual Baumann subgroup of T.

The original outside-maximal guard supplies an H* comparison subgroup.
The completed common-normal theorem 3.1.1 discharges the earlier callback
in the source E.2.3 argument: nonzero fixed vectors in V_M force J(T) to
move V_T. This gives both the commutator equality and the FF-module clause
of 3.2.2(6). In the centralized case the full fixed layer is consequently
zero. All groups and action maps remain those of the original FSU.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
3.2.2(6) and 3.2.10(1,8), printed pp.579,583; the first branch of
10.2.1 and the fixed-space step in 10.1.2(4), printed p.742.
-/

public section
open scoped IsMulCommutative
open Subgroup Theory.GroupTheory Stellmacher
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02
universe u
variable {G : Type u} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}

private theorem sylow_thompson_eq_of_two_overgroup (S : Subgroup G)
    (hp : IsPGroup 2 S) (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ S) :
    elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) := by
  obtain ⟨R, hSR⟩ := hp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R T
  let e : G ≃* G := MulAut.conj g
  have hRmap : (R : Subgroup G).map e.toMonoidHom = (T : Subgroup G) := by
    have hsub := congrArg Sylow.toSubgroup hg
    rw [Sylow.coe_subgroup_smul] at hsub
    exact hsub
  have hstable : (elementaryAbelianMaxJ (T : Subgroup G)).map e.toMonoidHom =
      elementaryAbelianMaxJ (T : Subgroup G) :=
    elementaryAbelianMaxJ_map_eq_of_le (T : Subgroup G) e
      ((map_mono (hJ.trans hSR)).trans_eq hRmap)
  have he : elementaryAbelianMaxJ (R : Subgroup G) =
      elementaryAbelianMaxJ (T : Subgroup G) := by
    apply map_injective (f := e.toMonoidHom) e.injective
    rw [← elementaryAbelianMaxJ_map_equiv e (R : Subgroup G), hRmap, hstable]
  exact (elementaryAbelianMaxJ_eq_of_intermediate (R : Subgroup G) S (he.symm ▸ hJ) hSR).trans he

variable (D : FundamentalSetup KnownSimple.IsKnownSimple T L)
include D

/-- Original 3.2.10(1), with the full-module kernel uniqueness discharged. -/
theorem source_thompson_normalizer_le_of_centralizes
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    normalizer (elementaryAbelianMaxJ (T : Subgroup G) : Set G) ≤ D.maximalLocal := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have he := elementaryAbelianMaxJ_eq_of_intermediate (T : Subgroup G)
    ((T : Subgroup G) ⊓ centralizer (D.fullModule : Set G))
    (le_inf (sSup_le fun _ hA => hA.1) hJ) inf_le_left
  rw [← he]
  exact source_kernel_thompson_normalizer_le D hu

/-- Original 3.2.10(8), preserving an arbitrary ambient two-subgroup S. -/
theorem source_two_overgroup_normalizer_le_of_centralizes
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G))
    (S : Subgroup G) (hp : IsPGroup 2 S)
    (hJS : elementaryAbelianMaxJ (T : Subgroup G) ≤ S) :
    elementaryAbelianMaxJ S = elementaryAbelianMaxJ (T : Subgroup G) ∧
      normalizer (S : Set G) ≤ D.maximalLocal := by
  have he := sylow_thompson_eq_of_two_overgroup S hp hJS
  refine ⟨he, ?_⟩
  exact (normalizer_le_normalizer_elementaryAbelianMaxJ S).trans
    (he.symm ▸ source_thompson_normalizer_le_of_centralizes D hJ)

/-- The centralizing-Thompson branch of original 10.2.1. -/
theorem source_baumann_normalizer_le_of_centralizes
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.fullModule : Set G)) :
    normalizer (ChapterB.baumann (T : Subgroup G) : Set G) ≤ D.maximalLocal := by
  apply (source_two_overgroup_normalizer_le_of_centralizes D hJ _
    (T.isPGroup'.to_le inf_le_left) (ChapterB.elementaryAbelianMaxJ_le_baumann _)).2

/-- Centralization of the original local module annihilates the full fixed
layer. The actual outside maximal local supplies the comparison subgroup. -/
theorem source_fullModule_fixed_eq_bot_of_centralizes
    (houtside : Chapter3.HasMaximalOutside T D.maximalLocal)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
  by_contra hfix
  obtain ⟨H, hH⟩ := Chapter3.exists_HStar_of_hasMaximalOutside houtside
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hh := D.lemma_3_2_3_uniqueness hu
  have hm := source_reduced_seed_thompson_moves_of_overgroup T (localOrbit T L) D.maximalLocal
    (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
    D.simpleQTKE hh.1 D.internal_actor_residual D.internal_actor_cases
    D.seedSpace D.homogeneous.isIrrPlus
    (Chapter3.source_common_normal_knownSimple D.simpleQTKE T) hh.2.2
    (by change componentOrbit D.seed D.maximalLocal ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥; rwa [← D.fullModule_eq_seed_orbit]) hH
  exact hm hJ



/-- The numerical standing hypothesis supplies the outside-maximal witness. -/
theorem source_fullModule_fixed_eq_bot_of_many
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G)) :
    D.fullModule ⊓ centralizer (localOrbit T L : Set G) = ⊥ := by
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  have hout : Chapter3.HasMaximalOutside T D.maximalLocal := by
    obtain ⟨A,hA,B,hB,hne⟩ := (Set.one_lt_ncard_iff_nontrivial_and_finite.mp hmany).1
    by_cases hAM : A = D.maximalLocal
    · exact Chapter3.hasMaximalOutside_of_two_distinct hu.normalizer_maximal hB.1
        (le_normalizer_componentOrbit L T) hB.2 (fun he => hne (hAM.trans he.symm))
    · exact Chapter3.hasMaximalOutside_of_two_distinct hu.normalizer_maximal hA.1
        (le_normalizer_componentOrbit L T) hA.2 hAM
  exact source_fullModule_fixed_eq_bot_of_centralizes D hout hJ



/-- The movement assertion of original 3.2.2(6), without an earlier
common-normal callback or a comparison-subgroup choice. -/
theorem source_thompson_moves_of_full_fixed
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    ¬ elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (D.moduleSubgroup : Set G) :=
  fun hJ => hfix (source_fullModule_fixed_eq_bot_of_many D hmany hJ)

/-- Both original conclusions of 3.2.2(6) on the literal FSU action. -/
theorem source_full_fixed_conclusions
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hfix : D.fullModule ⊓ centralizer (localOrbit T L : Set G) ≠ ⊥) :
    letI := D.module_elementary
    localOrbit T L = ⁅localOrbit T L, elementaryAbelianMaxJ (T : Subgroup G)⁆ ∧
      Representation.BinaryOffender.IsFFModule
        (ChapterD.UniqueFactor.imageRepresentation (localJoin T L) D.moduleSubgroup
          D.join_normalizes_module) := by
  let := D.module_elementary
  have hJ := source_thompson_moves_of_full_fixed D hmany hfix
  refine ⟨?_, D.module_isFF_of_thompson_not_centralizes hJ⟩
  have hu := Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
    (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
    D.simpleQTKE T D.maximal
  exact source_reduced_seed_thompson_commutator T (localOrbit T L) D.maximalLocal
    (localOrbit T L).le_normalizer (le_normalizer_componentOrbit L T)
    D.simpleQTKE (D.lemma_3_2_3_uniqueness hu).1
    D.internal_actor_residual D.internal_actor_cases D.seedSpace D.homogeneous.isIrrPlus hJ

end CFSG.Quasithin.Chapter10

