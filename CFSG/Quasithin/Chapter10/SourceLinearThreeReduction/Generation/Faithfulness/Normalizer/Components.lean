module
public import CFSG.Quasithin.Chapter10.SourceLinearThreeReduction.Generation.Faithfulness.Normalizer.OddCore
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.OddNormalizerReduction

/-!
# Component detection in a nonnormal odd-kernel normalizer

The original full module lies in the two-core of M intersect N_G(B) and
centralizes the odd core of N_G(B). If the latter normalizer has trivial
two-core, generalized-Fitting detection gives an ordinary component outside
M moved by the module. Quasithinness makes both the perfect fixed residual
and its commutator module normalize that same component. No A₅ marking is
used. The two-core premise is retained for the C.4.8 step of the assembly.

Source: Aschbacher--Smith, 4.4.8--10, printed pp.620--621, applied in
10.2.3(2), p.745 (combined manuscript of 1 March 2004).
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Detect the literal moved component once the two-core branch is excluded.
Its quotient belongs to the original known-simple class. -/
theorem source_nonnormal_oddNormalizer_moved_component_of_twoCore
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hBC : B ≤ sectionCentralizer (localOrbit T L)) (hodd : Odd (Nat.card B))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hc : pCore 2 (normalizer (B : Set G)) = ⊥) :
    ∃ K : Subgroup (normalizer (B : Set G)),
      IsComponent (normalizer (B : Set G)) K ∧
      ⁅K,D.fullModule.subgroupOf (normalizer (B : Set G))⁆ = K ∧
      ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal ∧
      pCore 2 K = ⊥ ∧ IsQuasithin K ∧ KnownSimple.IsKnownSimple (K ⧸ center K) ∧
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf (normalizer (B : Set G)) ≤
        normalizer (K : Set (normalizer (B : Set G))) ∧
      D.fullModule.subgroupOf (normalizer (B : Set G)) ≤
        normalizer (K : Set (normalizer (B : Set G))) := by
  let N := normalizer (B : Set G)
  let F := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let Y := D.maximalLocal.subgroupOf N
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  have hFN : F ≤ N := ((map_subtype_le (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G))).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hvcore := source_fullModule_le_oddNormalizer_overlap_core D B hBC hodd hBV
  have hk : IsPGroup 2 N.subtype.ker := by
    rw [N.subtype.ker_eq_bot N.subtype_injective]
    exact IsPGroup.of_bot
  have hvY : D.fullModule.subgroupOf N ≤ Y.pCoreIn 2 := by
    apply (Subgroup.map_le_map_iff_of_injective N.subtype_injective).mp
    rw [map_subgroupOf_eq_of_le hVN,map_pCoreIn_of_ker_isPGroup N.subtype hk]
    simpa only [Y,subgroupOf_map_subtype,N] using hvcore
  have hvne : D.fullModule.subgroupOf N ≠ ⊥ := by
    intro hb
    have hh := congrArg (map N.subtype) hb
    rw [map_subgroupOf_eq_of_le hVN,Subgroup.map_bot] at hh
    exact D.module_ne_bot (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans_eq hh))
  have hvo : ⁅D.fullModule.subgroupOf N,pPrimeCore 2 N⁆ = ⊥ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVN,Subgroup.map_bot]
    exact (source_nonnormal_oddNormalizer_oddCore D hn B hBC hodd hBV).1
  let := D.fullModule_elementary (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
    (fun _ _ _ => ChapterA.Section02.theoremA_knownSimple)
    (fun _ _ _ => ChapterA.Section02.theoremC_knownSimple) D.simpleQTKE T D.maximal)
  have hvp : IsPGroup 2 (D.fullModule.subgroupOf N) :=
    (IsElementaryAbelian.isPGroup 2 D.fullModule).comap_subtype
  obtain ⟨K,hK,hm,ho⟩ := exists_component_moved_outside_of_centralizes_oddCore
    (D.fullModule.subgroupOf N) Y hvp hvne hc hvo hvY
  have houtK : ¬ K.map N.subtype ≤ D.maximalLocal := fun he => ho (map_le_iff_le_comap.mp he)
  have hKc : pCore 2 K = ⊥ := by
    rw [pCore_subnormal_eq_comap 2 hK.1,hc,MonoidHom.comap_bot]
    exact K.subtype.ker_eq_bot K.subtype_injective
  obtain ⟨_,hqt,hkg⟩ := oddNormalizer_properQTK D.simpleQTKE B hne
  let : IsQuasisimple K := hK.2
  let : IsSimpleGroup (K ⧸ center K) := IsQuasisimple.simple
  let : Nontrivial K := (QuotientGroup.mk'_surjective (center K)).nontrivial
  have heven : 2 ∣ Nat.card K := by
    by_contra hnot
    exact Group.IsPerfect.not_isSolvable K
      (_root_.odd_order_theorem K (Nat.not_even_iff_odd.mp (by
        simpa only [even_iff_two_dvd] using hnot)))
  let : Group.IsPerfect F := Group.IsPerfect.map (localOrbit T L ⊓ centralizer (B : Set G)).subtype
  let : Group.IsPerfect (F.subgroupOf N) := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFN).symm.toMonoidHom) (subgroupOfEquivOfLe hFN).symm.surjective
  have heV : D.fullModule.subgroupOf N = ⁅D.fullModule.subgroupOf N,F.subgroupOf N⁆ := by
    apply map_injective N.subtype_injective
    rw [map_commutator,map_subgroupOf_eq_of_le hVN,map_subgroupOf_eq_of_le hFN]
    exact (source_fullModule_oddActor_cover D B hBC hodd hBV).2.1
  obtain ⟨hFK,hVK⟩ := hK.perfect_commutator_normalizes_of_quasithin hqt heven
    (F.subgroupOf N) (D.fullModule.subgroupOf N) heV
  exact ⟨K,hK,hK.commutator_eq_self_of_normalizes hVK hm,houtK,hKc,hqt.subgroup K,
    hkg.simple_quotient K (center K),hFK,hVK⟩
end CFSG.Quasithin.Chapter10
