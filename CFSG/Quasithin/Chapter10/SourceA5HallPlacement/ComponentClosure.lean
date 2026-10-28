module
public import CFSG.Quasithin.Chapter10.SourceA5HallPlacement.OrbitCentralizer
public import Theory.GroupTheory.GeneralizedFitting.OddComponentCentralizer
public import Theory.GroupTheory.PCoreInRestriction
public import Theory.GroupTheory.SubgroupTransport
public import Theory.ElementaryAbelian.Injective

/-!
# Placement and marked local geometry of the original Hall residual

When the overlap normalizes the selected component and the original
perfect residual acts by inner automorphisms, the full module lies in
that component. The original covering uniqueness, with both F and N_T(B),
then makes the component centralizer odd. The component is normal, its
centralizer is the odd core, and the whole fixed residual lies inside it.

The final theorem records the literal residual and module as subgroups of
that component. It retains the exact module normalizer, perfect residual,
nontrivial moved elementary two-subgroup, and A5 times A5 two-core quotient.
Inner action remains explicit; the full Theorem B outer argument must
supply it for normal components. No ambient SQTK assumption is added.
Source: Aschbacher--Smith4.4.10--12, printed pp.621--622, specialized to the
original nonnormal A5 pair in10.2.3, printed p.745.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter10
open Chapter3.Section02 Chapter4 Chapter4.Section04
variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {L : Subgroup G}
  (D : FundamentalSetup KnownSimple.IsKnownSimple T L)

/-- The original full module lies in an overlap-invariant component when
the fixed residual acts innerly on it. -/
theorem source_a5_oddNormalizer_fullModule_le_component_of_overlap_normalizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))))
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    D.fullModule ≤ K.map (normalizer (B : Set G)).subtype := by
  let N := normalizer (B : Set G)
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let Y := D.maximalLocal.subgroupOf N
  let J := K.map N.subtype
  let A := Y.map N.subtype
  let I := F ⊔ ((T : Subgroup G) ⊓ N)
  have hodd : Odd (Nat.card B) := by
    obtain ⟨n,he⟩ := hB.exists_card_eq
    rw [he]
    exact hp.pow
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hi : F ≤ J ⊔ centralizer (J : Set G) := by
    have hh := map_mono (f := N.subtype) hinner
    rw [map_subgroupOf_eq_of_le hFN,Subgroup.map_sup] at hh
    exact hh.trans (sup_le_sup le_rfl (map_centralizer_le_centralizer_image _ _))
  obtain ⟨_,_,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
  have hV : IsPGroup 2 D.fullModule := (isPGroup_pCoreIn 2 F).to_le hVF
  have hAJ : A ≤ normalizer (J : Set G) :=
    (map_mono hYK).trans (K.le_normalizer_map N.subtype)
  have hAV : A ≤ normalizer (D.fullModule : Set G) := by
    rw [source_fullModule_normalizer D]
    rintro x ⟨y,hy,rfl⟩
    exact hy
  obtain ⟨hIM,hIN,_,_⟩ := source_oddActor_normalizerJoin_input D B hBC hodd hBV
  have hIA : I ≤ A := by
    intro x hx
    exact ⟨⟨x,hIN hx⟩,hIM hx,rfl⟩
  exact binary_subgroup_le_of_normalized_inner_product_uniqueness J D.fullModule A I
    D.maximalLocal hV (hVF.trans ((pCoreIn_le 2 F).trans hi)) hAJ hAV hIA
    (source_a5_oddPrimeNormalizer_covering_uniqueness D e hn hp B hB hBC hBV hperm).2.2 houtK

/-- The actual uniqueness actor closes component placement and identifies
its centralizer, retaining the independent inner-action premise. -/
theorem source_a5_oddNormalizer_component_closure_of_overlap_normalizes
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    {p : ℕ} [Fact p.Prime] (hp : Odd p) (B : Subgroup G)
    (hB : IsPGroup p B) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hBV : B ≤ centralizer (D.fullModule : Set G))
    (hperm : (B : Set G) * (T : Set G) = (T : Set G) * (B : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hK : IsComponent (normalizer (B : Set G)) K)
    (houtK : ¬ K.map (normalizer (B : Set G)).subtype ≤ D.maximalLocal)
    (hYK : D.maximalLocal.subgroupOf (normalizer (B : Set G)) ≤
      normalizer (K : Set (normalizer (B : Set G))))
    (hinner : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K ⊔ centralizer (K : Set (normalizer (B : Set G)))) :
    K.Normal ∧
    D.fullModule.subgroupOf (normalizer (B : Set G)) ≤ K ∧
    centralizer (K : Set (normalizer (B : Set G))) =
      pPrimeCore 2 (normalizer (B : Set G)) ∧
    ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K := by
  let N := normalizer (B : Set G)
  let F := ((solvableResidual
    (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
      (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
  have hvG := source_a5_oddNormalizer_fullModule_le_component_of_overlap_normalizes
    D e hn hp B hB hBC hBV hperm K houtK hYK hinner
  have hv : D.fullModule.subgroupOf N ≤ K := by
    intro v hv
    obtain ⟨w,hw,he⟩ := hvG hv
    exact (Subtype.ext he : w = v) ▸ hw
  have houtN : ¬ N ≤ D.maximalLocal := fun he => houtK ((map_subtype_le K).trans he)
  have hcore := hK.centralizer_pCore_eq_bot_of_pCore_eq_bot 2
    (source_a5_oddPrimeNormalizer_twoCore_eq_bot D e hn hp B hB hBC hBV hperm houtN)
  have ho := source_a5_oddNormalizer_centralizer_odd_of_module_le
    D e hn hp B hB hBC hBV hperm K hYK houtK hv hcore
  let := source_oddNormalizer_residual_perfect (T := T) (L := L) B
  exact ⟨hK.normal_of_odd_centralizer ho,hv,
    hK.centralizer_eq_oddCore_of_odd_centralizer ho,
    hK.perfect_actor_le_of_odd_centralizer ho F hinner⟩

/-- The literal residual and full module inside a containing component form
an actual two-local marking with the original A5 times A5 quotient. -/
theorem source_a5_oddNormalizer_component_local_marking_of_residual_le
    (e : (L ⧸ pCore 2 L) ≃* alternatingGroup (Fin 5))
    (hn : ¬ (T : Subgroup G) ≤ normalizer (L : Set G))
    (B : Subgroup G) (hBC : B ≤ sectionCentralizer (localOrbit T L))
    (hodd : Odd (Nat.card B)) (hBV : B ≤ centralizer (D.fullModule : Set G))
    (K : Subgroup (normalizer (B : Set G)))
    (hFK : ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf
          (normalizer (B : Set G)) ≤ K) :
    let N := normalizer (B : Set G)
    let F := ((solvableResidual
      (localOrbit T L ⊓ centralizer (B : Set G) : Subgroup G)).map
        (localOrbit T L ⊓ centralizer (B : Set G)).subtype).subgroupOf N
    let P := F.subgroupOf K
    let W := (D.fullModule.subgroupOf N).subgroupOf K
    let MK := (D.maximalLocal.subgroupOf N).subgroupOf K
    Group.IsPerfect P ∧ P ≤ MK ∧ MK ≤ normalizer (P : Set K) ∧
      W ≠ ⊥ ∧ IsElementaryAbelian 2 W ∧ W ≤ P.pCoreIn 2 ∧
      W = ⁅W,P⁆ ∧ normalizer (W : Set K) = MK ∧
      Nonempty ((P ⧸ pCore 2 P) ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) ∧
      primeRank 3 P = 2 ∧ primeRank 5 P = 2 := by
  let N := normalizer (B : Set G)
  let C := localOrbit T L ⊓ centralizer (B : Set G)
  let F := (solvableResidual C).map C.subtype
  let F0 := F.subgroupOf N
  let P := F0.subgroupOf K
  let U := D.fullModule.subgroupOf N
  let W := U.subgroupOf K
  let Y := D.maximalLocal.subgroupOf N
  let MK := Y.subgroupOf K
  have hFN : F ≤ N := ((map_subtype_le _).trans inf_le_right).trans
    (Subgroup.centralizer_le_normalizer _)
  have hVN : D.fullModule ≤ N := (le_centralizer_iff.mp hBV).trans
    (Subgroup.centralizer_le_normalizer _)
  obtain ⟨_,hm,hVF⟩ := source_fullModule_oddActor_cover D B hBC hodd hBV
  have hUF : U ≤ F0 := subgroupOf_mono N (hVF.trans (pCoreIn_le 2 F))
  have hUK : U ≤ K := hUF.trans hFK
  let a : P ≃* F := (subgroupOfEquivOfLe hFK).trans (subgroupOfEquivOfLe hFN)
  let := source_oddNormalizer_residual_perfect (T := T) (L := L) B
  let : Group.IsPerfect P := Group.IsPerfect.ofSurjective
    (f := (subgroupOfEquivOfLe hFK).symm.toMonoidHom)
    (subgroupOfEquivOfLe hFK).symm.surjective
  have hFY : F ≤ D.maximalLocal :=
    ((map_subtype_le _).trans inf_le_left).trans (localOrbit T L).le_normalizer
  have hYF : Y ≤ normalizer (F0 : Set N) := by
    have hnorm : D.maximalLocal ⊓ N ≤ normalizer (F : Set G) :=
      ((le_inf inf_le_left (inf_le_right.trans (normalizer_le_normalizer_centralizer B))).trans
        inf_normalizer_le_normalizer_inf).trans
          (normalizer_le_normalizer_characteristic_image C (solvableResidual C))
    intro y hy f
    exact hnorm ⟨hy,y.property⟩ (f : G)
  have hMP : MK ≤ normalizer (P : Set K) := by
    rw [←subgroupOf_normalizer_eq hFK]
    exact subgroupOf_mono K hYF
  have hW : W ≠ ⊥ := by
    intro hb
    have hbV : D.fullModule = ⊥ := by
      apply le_bot_iff.mp
      intro v hv
      have hw : (⟨⟨v,hVN hv⟩,hUK hv⟩ : K) ∈ W := hv
      have he := mem_bot.mp (hb ▸ hw)
      exact mem_bot.mpr (congrArg (fun x : K => x.val.val) he)
    exact D.module_ne_bot
      (bot_unique ((le_componentOrbit D.moduleSubgroup D.maximalLocal).trans hbV.le))
  have heW : IsElementaryAbelian 2 W := by
    let := D.fullModule_elementary (Chapter1.Section02.nonsolvable_uniqueness_of_theoremsAC
      (fun X _ _ => ChapterA.Section02.theoremA_knownSimple (G := X))
      (fun X _ _ => ChapterA.Section02.theoremC_knownSimple (G := X))
      D.simpleQTKE T D.maximal)
    let : IsElementaryAbelian 2 U := IsElementaryAbelian.comap_of_injective (p := 2)
      N.subtype N.subtype_injective D.fullModule
    exact IsElementaryAbelian.comap_of_injective (p := 2) K.subtype K.subtype_injective U
  have hWP : W ≤ P.pCoreIn 2 := by
    rw [pCoreIn_subgroupOf 2 F0 K hFK,pCoreIn_subgroupOf 2 F N hFN]
    exact subgroupOf_mono K (subgroupOf_mono N hVF)
  have hmove : W = ⁅W,P⁆ := by
    change U.subgroupOf K = ⁅U.subgroupOf K,F0.subgroupOf K⁆
    rw [←SubgroupTransport.subgroupOf_commutator U F0 hUK hFK,
      ←SubgroupTransport.subgroupOf_commutator D.fullModule F hVN hFN,←hm]
  have hnormal : normalizer (W : Set K) = MK := by
    rw [←subgroupOf_normalizer_eq hUK,←subgroupOf_normalizer_eq hVN,
      source_fullModule_normalizer D]
  obtain ⟨q⟩ := source_a5_oddActorResidual_quotient_equiv D e hn B hBC hodd
  refine ⟨inferInstance,subgroupOf_mono K (subgroupOf_mono N hFY),hMP,hW,heW,hWP,
    hmove,hnormal,⟨(QuotientGroup.congr _ _ a (pCore_map_iso 2 a)).trans q⟩,?_,?_⟩
  · rw [primeRank_congr 3 a]
    exact source_a5_oddActorResidual_primeRank D e hn B hBC hodd (Or.inl rfl)
  · rw [primeRank_congr 5 a]
    exact source_a5_oddActorResidual_primeRank D e hn B hBC hodd (Or.inr rfl)

end CFSG.Quasithin.Chapter10
