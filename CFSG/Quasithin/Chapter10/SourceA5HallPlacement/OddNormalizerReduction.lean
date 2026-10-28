module
public import CFSG.Quasithin.Chapter10.SourceA5CoveringUniqueness
public import CFSG.Quasithin.Chapter10.SourceNonnormalOddActorCounterexample
public import CFSG.Quasithin.Chapter4.Section04.OddActorReduction
public import Theory.GroupTheory.GeneralizedFitting.MovedComponentOutside
public import Theory.Quasithin.ComponentPerfectAction
public import FeitThompson.FinalTheorem

/-!
# The original odd-kernel normalizer after covering uniqueness

For a prime-primary odd actor fixing both the original orbit quotient and
full module, the actual fixed residual together with N_T(B) has unique
maximal two-local overgroup M. An escaping N_G(B) consequently has trivial
two-core. The same module lies in O₂(M ∩ N_G(B)) and centralizes the odd
core, so it moves an ordinary component outside M. The perfect fixed
residual and its commutator module normalize that component.

Source: Aschbacher–Smith 4.4.6–10, printed pp.620–621, as used in
10.2.3, p.745. The remaining component inspection is not asserted here.
-/
public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- Covering uniqueness applies to the actual fixed residual and prime-actor normalizer. -/
theorem source_a5_oddPrimeNormalizer_covering_uniqueness
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G)) :
    UniqueMaximalOvergroup
      ((solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))) D.maximalLocal := by
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,hn⟩ := hB.exists_card_eq
    rw [hn]
    exact hp.pow
  obtain ⟨hIM,_,hcover,hcore⟩ := source_oddActor_normalizerJoin_input D B hBC hodd hBV
  apply source_a5_covering_uniqueness D e hn hIM hcover hcore
  apply le_antisymm
  · exact iSup_conjugates_le_of_le_normalizer _ _ _ (le_componentOrbit L T) hIM
  · apply (source_oddPrimeActor_normalizer_orbit D hp B hB hBC hperm).symm.le.trans
    let I := (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
        ((T : Subgroup G) ⊓ normalizer (B : Set G))
    exact iSup_le fun t => le_iSup_of_le
      (⟨t,(show (T : Subgroup G) ⊓ normalizer (B : Set G) ≤ I from le_sup_right) t.property⟩ : I) le_rfl

/-- The literal escaping odd-prime normalizer has trivial two-core. -/
theorem source_a5_oddPrimeNormalizer_twoCore_eq_bot
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (hout : ¬ normalizer (B : Set G) ≤ D.maximalLocal) :
    pCore 2 (normalizer (B : Set G)) = ⊥ := by
  have hu := source_a5_oddPrimeNormalizer_covering_uniqueness D e hn hp B hB hBC hBV hperm
  have hIN : (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ⊔
      ((T : Subgroup G) ⊓ normalizer (B : Set G)) ≤ normalizer (B : Set G) :=
    sup_le (((map_subtype_le (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G))).trans inf_le_right).trans
      (Subgroup.centralizer_le_normalizer _)) inf_le_right
  have hh := twoCore_sup_eq_bot_of_unique_maximalTwoLocal_overgroup _
    (normalizer (B : Set G)) D.maximalLocal hu.2.2 hout
  rwa [sup_eq_right.mpr hIN] at hh

/-- The full original module lies in the two-core of the actual normalizer overlap. -/
theorem source_fullModule_le_oddNormalizer_overlap_core
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G)) :
    D.fullModule ≤ (D.maximalLocal ⊓ normalizer (B : Set G)).pCoreIn 2 := by
  obtain ⟨_,_,hc⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
  have hF : (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype ≤ D.maximalLocal ⊓ normalizer (B : Set G) :=
    le_inf (((map_subtype_le (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G))).trans inf_le_left).trans (localOrbit T L).le_normalizer)
      (((map_subtype_le (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G))).trans inf_le_right).trans (Subgroup.centralizer_le_normalizer _))
  exact hc.trans (pCoreIn_mono_of_normalizes hF (by
    exact ((le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer B))).trans
      inf_normalizer_le_normalizer_inf).trans
        (normalizer_le_normalizer_characteristic_image
          (localOrbit T L ⊓ centralizer (B : Set G))
          (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)))))

/-- A hypothetical escaping odd kernel supplies an actual ordinary component,
with the original full module and fixed residual retained on N_G(B). -/
theorem source_a5_oddPrimeNormalizer_moved_component
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    [IsMulCommutative B] (hne : B ≠ ⊥)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (hout : ¬ normalizer (B : Set G) ≤ D.maximalLocal) :
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
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,hn⟩ := hB.exists_card_eq
    rw [hn]
    exact hp.pow
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  have hFN : F ≤ N := ((map_subtype_le (solvableResidual (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G))).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hc : pCore 2 N = ⊥ := source_a5_oddPrimeNormalizer_twoCore_eq_bot
    D e hn hp B hB hBC hBV hperm hout
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
    exact (source_a5_oddNormalizer_oddCore D e B hBC hodd hBV).1
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
