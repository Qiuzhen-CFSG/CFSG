module

public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.OmegaIntersection
public import CFSG.Quasithin.Chapter15.Section01.SourceCentralizing.SourceResidualSelectionExtraspecialModelSource
public import Theory.GroupTheory.SylowIndexThreeQuotient

/-!
# The original third-local action in the extraspecial row

The actual action of a maximal two-local distinct from the centralizer
partner cannot have trivial Sylow image. Otherwise its own elementary local
module is contained in the original central seed, and the local normalizer
identity places the entire seed centralizer in this maximal local. The
singleton centralizer-overgroup condition then identifies it with the partner.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory Representation Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter15.Section01
open Section03 Section03.InitialSource ChapterA.Section05To06 ChapterD ChapterD.UniqueFactor
variable {G : Type*} [Group G] [Finite G]

private theorem maximal_local_action_twoCore
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {N : Subgroup G} (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) :
    pCore 2 (internalActionImage N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)) = ⊥ := by
  let V := localModule T N
  let f := actionHom N V (le_normalizer_conjugateSpanBy (centralInvolutions T) N)
  have hred := localModule_reduced_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
  let := hred.normal
  have hk : f.ker = centralizer (V.subgroupOf N : Set N) := by
    rw [show f.ker = (centralizer (_ : Set G)).subgroupOf N from actionHom_ker N _ _]
    ext n
    constructor
    · intro hn v hv
      exact Subtype.ext (hn v hv)
    · intro hn v hv
      exact congrArg N.subtype (hn ⟨v,localModule_le T hN.2 hv⟩ hv)
  let e := (QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivRange f)
  change pCore 2 f.range = ⊥
  rw [←pCore_map_iso 2 e,hred.quotient_pCore_eq_bot,Subgroup.map_bot]

private theorem maximal_local_action_not_twoGroup
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {N Mc : Subgroup G} (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : N ≠ Mc) :
    ¬ IsPGroup 2 (internalActionImage N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)) := by
  let f := (actionHom N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).rangeRestrict
  intro hp
  have hcore := maximal_local_action_twoCore hG T hN
  have ht : (⊤ : Subgroup (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N))) ≤ pCore 2 _ :=
    le_sSup ⟨inferInstance,hp.of_injective (⊤ : Subgroup _).subtype (Subgroup.subtype_injective _)⟩
  have hi (x : N) : f x = 1 := ht.trans hcore.le (mem_top _)
  have hle : N ≤ Mc := by
    intro x hx
    have hh : (⟨x,hx⟩ : N) ∈ (actionHom N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).ker := congrArg Subtype.val (hi ⟨x,hx⟩)
    have hc : (⟨x,hx⟩ : N) ∈ (centralizer (localModule T N : Set G)).subgroupOf N :=
      (actionHom_ker N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)) ▸ hh
    exact localModule_centralizer_le_partner T N hu hc
  have hMc : Mc ∈ maximalTwoLocalOvergroups
      (centralizer (centralInvolutions T : Set G)) := hu ▸ Set.mem_singleton Mc
  exact hne (le_antisymm hle (hN.1.2 hMc.1.1 hle))

private theorem maximal_local_action_sylow_ne_bot
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    {N Mc : Subgroup G} (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hne : N ≠ Mc)
    (P : Sylow 2 (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N))) :
    (P : Subgroup (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N))) ≠ ⊥ := by
  let V := localModule T N
  let hn : N ≤ normalizer (V : Set G) := le_normalizer_conjugateSpanBy (centralInvolutions T) N
  let D := internalActionImage N V hn
  let f : N →* D := (actionHom N V hn).rangeRestrict
  let Q := (T.subtype hN.2).mapSurjective
    (f := f) (actionHom N V hn).rangeRestrict_surjective
  intro hP
  have hQc : Nat.card Q = 1 := by
    have hcP : Nat.card P = 1 := by
      rw [hP,card_bot]
    exact Q.card_eq_multiplicity.trans (P.card_eq_multiplicity.symm.trans hcP)
  have hQ : (Q : Subgroup D) = ⊥ := card_eq_one.mp hQc
  have hTV : (T : Subgroup G) ≤ centralizer (V : Set G) := by
    intro t ht
    have hf : f ⟨t,hN.2 ht⟩ = 1 := by
      have hh : f ⟨t,hN.2 ht⟩ ∈ (Q : Subgroup D) :=
        mem_map_of_mem f ht
      rw [hQ] at hh
      exact hh
    have hk : (⟨t,hN.2 ht⟩ : N) ∈ (actionHom N V hn).ker :=
      congrArg Subtype.val hf
    rwa [actionHom_ker] at hk
  let := localModule_elementary_from_source hG T
    ⟨Chapter1.mem_H_of_isTwoLocal hN.1.1,hN.2⟩
  let U := V.subgroupOf N
  let : U.Normal := normal_subgroupOf_of_le_normalizer hn
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf (localModule_le T hN.2)
  have hUT := (IsElementaryAbelian.isPGroup 2 U).le_sylow_of_normal (T.subtype hN.2)
  have hVN : V ≤ N := localModule_le T hN.2
  have hVT : V ≤ (T : Subgroup G) := by
    have hh := map_mono (f := N.subtype) hUT
    change (V.subgroupOf N).map N.subtype ≤ _ at hh
    simpa only [map_subgroupOf_eq_of_le hVN,Sylow.coe_subtype,
      map_subgroupOf_eq_of_le hN.2] using hh
  have hVZ : V ≤ centralInvolutions T := by
    intro v hv
    apply (mem_omegaOneCenterAmbient_iff _ _).mpr
    exact ⟨hVT hv,elemPow_eq_one_of_isElementaryAbelian v hv,
      fun t ht => (hTV ht v hv).symm⟩
  have he : V = centralInvolutions T := le_antisymm hVZ (le_conjugateSpanBy _ _)
  have hCN : centralizer (centralInvolutions T : Set G) ≤ N := by
    rw [←he,(maximal_local_normalizer_from_source hG T hN).2]
    exact Subgroup.centralizer_le_normalizer _
  exact hne (Set.mem_singleton_iff.mp (hu ▸
    (show N ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      ⟨hN.1,hCN⟩)))

private theorem full_intersection_action_symmetricThree_of_index
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} [IsElementaryAbelian 2 V] (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNMc : N ≠ Mc)
    (hindex : let f := (actionHom M V hV.normalized).rangeRestrict
      (((T : Subgroup G).subgroupOf M).map f).relIndex (((M ⊓ N).subgroupOf M).map f) = 3) :
    Nonempty (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N) ≃* Equiv.Perm (Fin 3)) ∧
      ¬ (((((T : Subgroup G).subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict).subgroupOf
        (((M ⊓ N).subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict)).Normal) := by
  let D := internalActionImage M V hV.normalized
  let f : M →* D := (actionHom M V hV.normalized).rangeRestrict
  let H := (M ⊓ N).subgroupOf M
  let A := H.map f
  let P := (T.subtype hM.1.2).mapSurjective
    (f := f) (actionHom M V hV.normalized).rangeRestrict_surjective
  have hPA : (P : Subgroup D) ≤ A := map_mono
    (subgroupOf_mono M (le_inf hM.1.2 hN.2))
  have hord := source_ordering_of_centralizing_orderingMaximal hG T hempty hM hJ N hN
  have hCN : M ⊓ centralizer (V : Set G) ≤
      N ⊓ centralizer (localModule T N : Set G) := by
    rw [hfull]
    exact (lemma_A_5_3 hord).2.2 (maximal_local_normalizer_from_source hG T hN)
  let Dn := internalActionImage N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)
  let g : N →* Dn :=
    (actionHom N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).rangeRestrict
  let i : H →* N := (M.subtype.comp H.subtype).codRestrict N (fun x => x.property.2)
  let j := f.subgroupMap H
  let k := g.comp i
  have hk : Function.Surjective k := by
    intro d
    obtain ⟨n,hn⟩ := (actionHom N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).rangeRestrict_surjective d
    change g n = d at hn
    obtain ⟨a,ha,b,hb,he⟩ := hord n n.property
    have haH : (⟨a,ha.2⟩ : M) ∈ H := ⟨ha.2,ha.1⟩
    have hbker : (⟨b,hb.1⟩ : N) ∈
        (actionHom N (localModule T N) (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).ker := by
      exact (actionHom_ker N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).symm ▸ hb.2
    have hgb : g ⟨b,hb.1⟩ = 1 := by
      apply Subtype.ext
      exact hbker
    refine ⟨⟨⟨a,ha.2⟩,haH⟩,?_⟩
    have hnprod : n = (⟨a,ha.1⟩ : N) * ⟨b,hb.1⟩ := Subtype.ext he.symm
    rw [hnprod,map_mul,hgb,mul_one] at hn
    exact hn
  have hker : j.ker ≤ k.ker := by
    intro x hx
    have hfx : f (x : M) = 1 := congrArg Subtype.val hx
    have hxker : (x : M) ∈ (actionHom M V hV.normalized).ker := congrArg Subtype.val hfx
    rw [actionHom_ker] at hxker
    have hxc := (hCN ⟨(x : M).property,hxker⟩).2
    have hxg : i x ∈ (actionHom N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).ker := by
      exact (actionHom_ker N (localModule T N)
        (le_normalizer_conjugateSpanBy (centralInvolutions T) N)).symm ▸ hxc
    apply Subtype.ext
    exact hxg
  let q : A →* Dn := j.liftOfSurjective (f.subgroupMap_surjective H) ⟨k,hker⟩
  have hq : Function.Surjective q := by
    intro d
    obtain ⟨x,rfl⟩ := hk d
    exact ⟨j x,by simp [q]⟩
  let S := P.subtype hPA
  let R := S.mapSurjective hq
  have hSi : (S : Subgroup A).index = 3 := hindex
  have hdiv : (R : Subgroup Dn).index ∣ 3 := by
    exact hSi ▸ (S : Subgroup A).index_map_dvd hq
  have hRi : (R : Subgroup Dn).index = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdiv with hi | hi
    · have he : (R : Subgroup Dn) = ⊤ := index_eq_one.mp hi
      have hp := R.isPGroup'
      rw [he] at hp
      exact (maximal_local_action_not_twoGroup hG T hN hu hNMc
        (hp.of_equiv topEquiv)).elim
    · exact hi
  have hcore := maximal_local_action_twoCore hG T hN
  have hlt : pCore 2 Dn < (R : Subgroup Dn) := by
    rw [hcore]
    exact bot_lt_iff_ne_bot.mpr (maximal_local_action_sylow_ne_bot hG T hN hu hNMc R)
  obtain ⟨e⟩ := sylow_index_three_core_quotient R hRi hlt
  refine ⟨⟨((QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot).symm.trans e⟩,?_⟩
  intro hnormal
  let : (S : Subgroup A).Normal := hnormal
  have hRn : (R : Subgroup Dn).Normal := Normal.map inferInstance q hq
  exact not_le_of_gt hlt (le_sSup ⟨hRn,R.isPGroup'⟩)

/-- A third maximal local in the original full extraspecial row has the
literal symmetric-three action on its own local module. -/
theorem PreparedChosenModule.extraspecial_third_action_symmetricThree
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := hV.elementary
      SourceCases.Extraspecial (imageRepresentation M V hV.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    Nonempty (internalActionImage N (localModule T N)
      (le_normalizer_conjugateSpanBy (centralInvolutions T) N) ≃* Equiv.Perm (Fin 3)) := by
  let := hV.elementary
  exact (full_intersection_action_symmetricThree_of_index hG T hempty hM hJ hu hV hfull hN hNMc
    (hV.extraspecial_third_action_relIndex hG T hempty hM hJ hu hex hN hNM hNMc)).1

/-- A third local forces the original Sylow action to move the central
cubic subgroup of the extraspecial residual. -/
theorem PreparedChosenModule.extraspecial_third_sylow_moves_center
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G) (T : Sylow 2 G)
    (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc V N : Subgroup G} (hM : IsOrderingMaximal T M)
    (hJ : elementaryAbelianMaxJ (T : Subgroup G) ≤ centralizer (localModule T M : Set G))
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hV : PreparedChosenModule T M V) (hfull : V = localModule T M)
    (hex : letI := hV.elementary
      SourceCases.Extraspecial (imageRepresentation M V hV.normalized)
        (((T : Subgroup G).subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict))
    (hN : N ∈ maximalTwoLocalOvergroups (T : Subgroup G)) (hNM : N ≠ M) (hNMc : N ≠ Mc) :
    let D := internalActionImage M V hV.normalized
    ¬ (((T : Subgroup G).subgroupOf M).map (actionHom M V hV.normalized).rangeRestrict) ≤
      centralizer ((center (pResidual 2 D)).map (pResidual 2 D).subtype : Set D) := by
  let := hV.elementary
  let D := internalActionImage M V hV.normalized
  let f : M →* D := (actionHom M V hV.normalized).rangeRestrict
  let A := ((M ⊓ N).subgroupOf M).map f
  let P := (T.subtype hM.1.2).mapSurjective
    (f := f) (actionHom M V hV.normalized).rangeRestrict_surjective
  have hPA : (P : Subgroup D) ≤ A := map_mono
    (subgroupOf_mono M (le_inf hM.1.2 hN.2))
  obtain ⟨_,hn,hne⟩ := hV.third_maximal_action_constraints hG T hempty hM hJ hu hN hNM hNMc
  have hnP := (full_intersection_action_symmetricThree_of_index hG T hempty hM hJ hu hV hfull
    hN hNMc (hV.extraspecial_third_action_relIndex hG T hempty hM hJ hu hex hN hNM hNMc)).2
  obtain ⟨_,_,_,hP,_,_,_,hI⟩ := hex
  let : IsExtraspecial 3 (pResidual 2 D) := hP
  have heA := SourceExtraspecialModel.proper_non_two_overgroup_eq P hI A hPA hne hn
  change ¬ (P : Subgroup D) ≤ centralizer
    ((center (pResidual 2 D)).map (pResidual 2 D).subtype : Set D)
  intro hc
  apply hnP
  apply normal_subgroupOf_of_le_normalizer
  change A ≤ normalizer (P : Set D)
  rw [heA]
  exact sup_le ((le_centralizer_iff.mp hc).trans (Subgroup.centralizer_le_normalizer _))
    (P : Subgroup D).le_normalizer

end CFSG.Quasithin.Chapter15.Section01
