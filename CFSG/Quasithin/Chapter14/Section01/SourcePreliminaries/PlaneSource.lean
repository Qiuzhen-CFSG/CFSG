module
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.PlaneGeometry
public import CFSG.Quasithin.Chapter14.Section01.SourcePreliminaries.ResidualSplitting
public import Theory.GroupTheory.PrimeRankProduct
public import Theory.Quasithin.CoprimeRank
/-!
# Full original14.1.18 for the natural-plane branch

The preceding source geometry gives the noncentral intersection core and
its exact intersection with the module centralizer. The literal residual
splitting now supplies the cyclic bar image, the two-core identity and the
internal S₃ direct factor modulo O₂(M). The complementary centralizer has
three-rank at most one by additivity of prime rank and quasithinness.

The residual–Sylow supplement covers the original local action, so A.5.7
makes M the unique maximal local above YT. Together with PlaneGeometry,
this proves all seven source clauses from |V(M)|=4 and the actual S₃
centralizer quotient. No extra core, commutator, splitting, rank or
maximal-overgroup premise remains. The separate theorem records the
literal set products of clause (2).
Source: Aschbacher--Smith14.1.18, printed pp.980--981.
-/
public section
open scoped Pointwise
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.SourcePreliminaries
open Chapter15.Section03 Chapter15.Section03.InitialSource
open Chapter15.Section03.InitialSource.UniformControl ChapterA.Section05To06
variable {G : Type*} [Group G] [Finite G]

private theorem symmetric_three_rank_pos : 1 ≤ primeRank 3 (Equiv.Perm (Fin 3)) := by
  let A := alternatingGroup (Fin 3)
  have hc : Nat.card A = 3 := by
    change Nat.card (alternatingGroup (Fin 3)) = 3
    rw [nat_card_alternatingGroup]
    norm_num
  let : IsCyclic A := isCyclic_of_prime_card hc
  let : CommGroup A := IsMulCommutative.instCommGroup
  exact primeRank_ge_of_elementary_embedding
    (fun a : A => by simpa only [hc] using (pow_card_eq_one' (x := a))) (by simpa using hc)
    A.subtype A.subtype_injective

private theorem plane_centralizer_rank
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) {M : Subgroup G}
    (hM : M ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (e : (M ⧸ pCore 2 M) ≃* Equiv.Perm (Fin 3) ×
      ((centralizer (localModule T M : Set G)).subgroupOf M ⧸
        (pCore 2 M).subgroupOf ((centralizer (localModule T M : Set G)).subgroupOf M))) :
    primeRank 3 (M ⊓ centralizer (localModule T M : Set G) : Subgroup G) ≤ 1 := by
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  have hr := (hG.twoLocal_sqtk hM.1.1).stronglyQuasithin 3 Nat.prime_three (by decide)
  have he := Theory.GroupTheory.primeRank_equiv 3 e
  rw [primeRank_prod_eq_add,
    primeRank_quotient_eq_of_isTwoGroup 3 (by decide) (pCore 2 M) pCore_isPGroup,
    primeRank_quotient_eq_of_isTwoGroup 3 (by decide) ((pCore 2 M).subgroupOf C)
      pCore_isPGroup.comap_subtype] at he
  have hpos := symmetric_three_rank_pos
  have hC : C.map M.subtype = M ⊓ centralizer (localModule T M : Set G) := by
    rw [subgroupOf_map_subtype,inf_comm]
  have heC := Theory.GroupTheory.primeRank_equiv 3
    ((C.equivMapOfInjective M.subtype M.subtype_injective).trans (MulEquiv.subgroupCongr hC))
  omega

omit [Finite G] in
private theorem plane_residual_unique
    (T : Sylow 2 G) {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hfac : M = (sourceResidual M Mc ⊔ (T : Subgroup G)) ⊔
      (M ⊓ centralizer (localModule T M : Set G))) :
    maximalTwoLocalOvergroups (sourceResidual M Mc ⊔ (T : Subgroup G)) = {M} := by
  let X := sourceResidual M Mc ⊔ (T : Subgroup G)
  let C := (centralizer (localModule T M : Set G)).subgroupOf M
  have hXM : X ≤ M := sup_le (sourceResidual_le _ _) hM.1.2
  have hXC : X.subgroupOf M ⊔ C = ⊤ := by
    apply map_injective M.subtype_injective
    rw [Subgroup.map_sup,map_subgroupOf_eq_of_le hXM,
      show C.map M.subtype = M ⊓ centralizer (localModule T M : Set G) by
        rw [subgroupOf_map_subtype,inf_comm],
      ←hfac,←MonoidHom.range_eq_map,range_subtype]
  have hord : OrderingLE T M X := by
    intro m hm
    have hx : (⟨m,hm⟩ : M) ∈ X.subgroupOf M ⊔ C := by rw [hXC]; exact mem_top _
    obtain ⟨x,hx,c,hc,he⟩ := mem_sup_of_normal_right.mp hx
    exact ⟨x,⟨x.property,hx⟩,c,⟨c.property,hc⟩,congrArg M.subtype he⟩
  ext K
  constructor
  · intro hK
    exact Set.mem_singleton_iff.mpr ((lemma_A_5_7_1 hM le_sup_right hXM hord K hK.1).mp hK.2)
  · intro hK
    rw [Set.mem_singleton_iff] at hK
    subst K
    exact ⟨hM.1.1,hXM⟩

/-- Original14.1.18, on the actual module, core and residual. -/
theorem source_lemma_14_1_18
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3)) :
    let V := localModule T M
    let C := (centralizer (V : Set G)).subgroupOf M
    let D := ((M ⊓ Mc).pCoreIn 2).subgroupOf M
    let Y := (sourceResidual M Mc).subgroupOf M
    let q := QuotientGroup.mk' (pCore 2 M)
    let B := Y.map q ⊔ D.map q
    (∀ N, IsOrderingMaximal T N → N = M) ∧
      (T : Subgroup G) = (M ⊓ Mc).pCoreIn 2 ⊔ ((T : Subgroup G) ⊓ centralizer (V : Set G)) ∧
      M ⊓ Mc = (M ⊓ centralizer (V : Set G)) ⊔ (M ⊓ Mc).pCoreIn 2 ∧
      Y.map (QuotientGroup.mk' C) = twoResidualAmbient (⊤ : Subgroup (M ⧸ C)) ∧
      Nonempty ((Y.map (QuotientGroup.mk' C)) ≃* Multiplicative (ZMod 3)) ∧
      (sourceResidual M Mc).pCoreIn 2 = sourceResidual M Mc ⊓ centralizer (V : Set G) ∧
      maximalTwoLocalOvergroups (sourceResidual M Mc ⊔ (T : Subgroup G)) = {M} ∧
      Nonempty (B ≃* Equiv.Perm (Fin 3)) ∧
      B ⊔ C.map q = ⊤ ∧ Disjoint B (C.map q) ∧ ⁅B,C.map q⁆ = ⊥ ∧
      primeRank 3 (M ⊓ centralizer (V : Set G) : Subgroup G) ≤ 1 ∧
      Nat.card (centralInvolutions T) = 2 ∧ Mc = centralizer (centralInvolutions T : Set G) ∧
      maximalTwoLocalOvergroups (T : Subgroup G) = {M,Mc} := by
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨hmax,hne,hMc,hfam⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  obtain ⟨hmeet,hnoncentral,hcomm⟩ := plane_intersection_core_inputs hG T hempty hM.1 hu hmany hZ hne
  have hMcC : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    apply hMcC.2
    intro z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hCMc : M ⊓ centralizer (localModule T M : Set G) ≤ Mc :=
    inf_le_right.trans (localModule_centralizer_le_partner T M hu)
  have hMMc : ¬ M ≤ Mc := fun h => hne (hM.1.1.eq_of_le hMcC.1.1 h)
  obtain ⟨hT,hI⟩ := intersectionCore_factorizations M Mc (localModule T M) T hM.1.2 hTMc
    ⟨e⟩ hnoncentral hCMc hMMc
  obtain ⟨hbar,_,_,hebar,hY,heB,hBC,hd,hc,heprod,_⟩ :=
    sourceResidual_splitting M Mc (localModule T M) e hmeet hnoncentral hcomm
  obtain ⟨eprod⟩ := heprod
  exact ⟨hmax,hT,hI,hbar,hebar,hY,
    plane_residual_unique T hM (decomposition_of_intersectionCore_not_centralizing
      M Mc (localModule T M) T hM.1.2 ⟨e⟩ hnoncentral),
    heB,hBC,hd,hc,plane_centralizer_rank hG T hM.1 eprod,hZ,hMc,hfam⟩

/-- The literal products in original14.1.18(2). -/
theorem source_lemma_14_1_18_products
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃*
      Equiv.Perm (Fin 3)) :
    (T : Set G) = ((M ⊓ Mc).pCoreIn 2 : Set G) *
        ((T : Subgroup G) ⊓ centralizer (localModule T M : Set G) : Subgroup G) ∧
      (M ⊓ Mc : Subgroup G) = (M ⊓ centralizer (localModule T M : Set G) : Subgroup G) *
        ((M ⊓ Mc).pCoreIn 2 : Set G) := by
  obtain ⟨_,hT,hI,rest⟩ := source_lemma_14_1_18 hG T hempty hM hu hmany hcard e
  have hMcC : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    apply hMcC.2
    intro z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hRn : M ⊓ Mc ≤ normalizer ((M ⊓ Mc).pCoreIn 2 : Set G) :=
    (M ⊓ Mc).le_normalizer.trans
      (normalizer_le_normalizer_characteristic_image _ (pCore 2 (M ⊓ Mc : Subgroup G)))
  have hCn : M ≤ normalizer (M ⊓ centralizer (localModule T M : Set G) : Subgroup G) :=
    (le_inf M.le_normalizer ((le_normalizer_conjugateSpanBy _ _).trans
      (normalizer_le_normalizer_centralizer _))).trans inf_normalizer_le_normalizer_inf
  exact ⟨(congrArg (fun H : Subgroup G => (H : Set G)) hT).trans
      (coe_mul_of_right_le_normalizer_left _ _
        (inf_le_left.trans ((le_inf hM.1.2 hTMc).trans hRn))),
    (congrArg (fun H : Subgroup G => (H : Set G)) hI).trans
      (coe_mul_of_right_le_normalizer_left _ _ ((pCoreIn_le 2 _).trans (inf_le_left.trans hCn)))⟩

end CFSG.Quasithin.Chapter14.SourcePreliminaries
