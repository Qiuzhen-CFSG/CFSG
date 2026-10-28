module
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ModuleGeometry.ExchangedInner
public import Theory.SpecificGroups.PSL2.SixteenWreathPairIndex
public import Theory.GroupTheory.CenterlessPairInnerActions

/-!
# Excluding the exchanged PSL₂(16) branch of original 14.6.15

The literal full automorphism wreath model puts the actual component
product at index 32 modulo O₂(Mc). The quintic Borel detector makes every
element of O₂(H) inner on both component quotients. Their commuting,
centerless images have trivial joint centralizer in Mc/O₂(Mc), so these
inner actions place O₂(H) in K_z O₂(Mc).

The original Sylow two-subgroup lies in H. It surjects onto the quotient
of Mc by K_z O₂(Mc), hence that quotient of order 32 is also a quotient
of H/O₂(H). The earlier exchanged-factor setup gives the latter order
200, a contradiction. The residual branch has already been excluded by
the actual second-normalizer and component comparisons imported here.
This proves quintic exclusion without an additional geometry premise.

The original 14.6.12 factor-join index is used in the order 200; it remains
an explicit earlier-source input owned by qt-e-14612-singleton. This is
not a proof of that index. Final suitable-choice assembly retains the
discharge of the earlier 14.6.12--14 premises.
Source: Aschbacher--Smith 14.6.14(4)--15, printed pp.1033--1035.
-/

public section
open Subgroup Theory.GroupTheory Representation.BinaryOffender
open scoped IsMulCommutative
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open ComponentExclusion
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)

include s in
/-- The actual component closure has index 32 in Mc/O₂(Mc). -/
theorem source_exchanged_quotient_closure_index :
    (((residualClosure H Mc).subgroupOf Mc).map (QuotientGroup.mk' (pCore 2 Mc))).index = 32 := by
  obtain ⟨b⟩ := source_exchanged_factor_data s
  obtain ⟨e⟩ := (source_exchanged_closure_model s).2
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let A := b.K1.subgroupOf Mc
  let B := b.K2.subgroupOf Mc
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  have hA := (b.first_component.map_quotient (pCore 2 Mc)).map_equiv e
  have hB := (b.second_component.map_quotient (pCore 2 Mc)).map_equiv e
  have hn : (A.map q).map e.toMonoidHom ≠ (B.map q).map e.toMonoidHom := by
    intro he
    have hab := b.first_component.eq_of_map_quotient_eq b.second_component (pCore 2 Mc)
      (map_injective e.injective he)
    have hk : b.K1 = b.K2 := by
      have hh := congrArg (map Mc.subtype) hab
      simpa only [map_subgroupOf_eq_of_le b.first_le,map_subgroupOf_eq_of_le b.second_le] using hh
    obtain ⟨t,_,hnt,ht⟩ := b.exchanged
    apply hnt
    apply inv_mem_iff.mp
    apply mem_normalizer_iff_map_conj_eq.mpr
    exact ht.trans hk.symm
  have hi := Theory.PSL2.SixteenWreathComponents.component_pair_index hA hB hn
  rw [←Subgroup.map_sup,index_map_of_bijective e.bijective,←Subgroup.map_sup] at hi
  have hj : A ⊔ B = (residualClosure H Mc).subgroupOf Mc := by
    rw [←subgroupOf_sup b.first_le b.second_le,b.join_eq]
  rwa [hj] at hi

include s in
/-- Pull the component index back through the literal two-core quotient. -/
theorem source_exchanged_core_supplement_index :
    (residualClosure H Mc ⊔ Mc.pCoreIn 2).relIndex Mc = 32 := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  have hi := source_exchanged_quotient_closure_index s
  have hh := index_comap_of_surjective (f := q)
    (((residualClosure H Mc).subgroupOf Mc).map q) (QuotientGroup.mk'_surjective (pCore 2 Mc))
  rw [comap_map_eq,QuotientGroup.ker_mk'] at hh
  have hK : residualClosure H Mc ≤ Mc := by
    obtain ⟨b⟩ := source_exchanged_factor_data s
    rw [←b.join_eq]
    exact sup_le b.first_le b.second_le
  have he : ((residualClosure H Mc ⊔ Mc.pCoreIn 2).subgroupOf Mc) =
      (residualClosure H Mc).subgroupOf Mc ⊔ pCore 2 Mc := by
    rw [subgroupOf_sup hK (pCoreIn_le 2 Mc)]
    congr 1
    ext x
    exact mem_map_iff_mem Mc.subtype_injective
  change ((residualClosure H Mc ⊔ Mc.pCoreIn 2).subgroupOf Mc).index = 32
  rw [he,hh]
  exact hi
private theorem quotient_inner_action {K : Subgroup G}
    (hKM : K ≤ Mc) (hK : (K.subgroupOf Mc).IsCComponent)
    (x : Mc) (hx : (x : G) ∈ normalizer (K : Set G))
    (hi : normalizerPCoreQuotientAction K ⟨x,hx⟩ ∈
      MulAut.innerSubgroup (K ⧸ pCore 2 K)) :
    let q := QuotientGroup.mk' (pCore 2 Mc)
    ∃ k ∈ (K.subgroupOf Mc).map q,
      ∀ y ∈ (K.subgroupOf Mc).map q, q x*y*(q x)⁻¹ = k*y*k⁻¹ := by
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let f := q.comp (inclusion hKM)
  have hc : K.pCoreIn 2 ≤ Mc.pCoreIn 2 := by
    have hh := map_mono (f := Mc.subtype) (pCoreIn_le_of_subnormal 2 hK.subnormal)
    rw [map_pCoreIn_of_injective 2 _ _ Mc.subtype_injective,
      map_subgroupOf_eq_of_le hKM] at hh
    exact hh
  have hk : pCore 2 K ≤ f.ker := by
    intro k hk
    apply (QuotientGroup.eq_one_iff _).mpr
    exact (mem_map_iff_mem Mc.subtype_injective).mp
      (hc (mem_map_of_mem K.subtype hk))
  let fbar := QuotientGroup.lift (pCore 2 K) f hk
  obtain ⟨k,hki⟩ := hi
  obtain ⟨k,rfl⟩ := QuotientGroup.mk'_surjective (pCore 2 K) k
  refine ⟨f k,mem_map_of_mem q k.property,?_⟩
  rintro _ ⟨y,hy,rfl⟩
  let z : K := ⟨y,hy⟩
  have hh := MulEquiv.congr_fun hki (QuotientGroup.mk' (pCore 2 K) z)
  rw [MulAut.conj_apply,←map_mul,←map_inv,←map_mul] at hh
  change QuotientGroup.mk' (pCore 2 K) (k*z*k⁻¹) =
    quotientAut (pCore 2 K) (K.normalizerMonoidHom ⟨x,hx⟩)
      (QuotientGroup.mk' (pCore 2 K) z) at hh
  rw [quotientAut_apply_mk] at hh
  have hf := congrArg fbar hh
  change q (inclusion hKM k * y * (inclusion hKM k)⁻¹) = q (x*y*x⁻¹) at hf
  change q x * q y * (q x)⁻¹ = q (inclusion hKM k) * q y * (q (inclusion hKM k))⁻¹
  simpa only [map_mul,map_inv] using hf.symm

include s in
/-- Both literal inner actions place O₂(H) in the component product modulo O₂(Mc). -/
theorem source_exchanged_core_le_closure_supplement :
    H.pCoreIn 2 ≤ residualClosure H Mc ⊔ Mc.pCoreIn 2 := by
  obtain ⟨b⟩ := source_exchanged_factor_data s
  let q := QuotientGroup.mk' (pCore 2 Mc)
  let A := (b.K1.subgroupOf Mc).map q
  let B := (b.K2.subgroupOf Mc).map q
  let : Group.IsNilpotent (pCore 2 Mc) := pCore_isPGroup.isNilpotent
  have hA : A.IsCComponent := b.first_component.map_quotient (pCore 2 Mc)
  have hB : B.IsCComponent := b.second_component.map_quotient (pCore 2 Mc)
  let e1 := subgroupOfEquivOfLe b.first_le
  let e2 := subgroupOfEquivOfLe b.second_le
  let a1 := (cComponentTwoCoreQuotientEquiv b.first_component).symm.trans
    ((QuotientGroup.congr _ _ e1 (pCore_map_iso 2 e1)).trans b.first_model.some)
  let a2 := (cComponentTwoCoreQuotientEquiv b.second_component).symm.trans
    ((QuotientGroup.congr _ _ e2 (pCore_map_iso 2 e2)).trans b.second_model.some)
  let := Theory.PSL2.SixteenWreathComponents.simple
  let : IsSimpleGroup A := a1.isSimpleGroup
  let : IsSimpleGroup B := a2.isSimpleGroup
  let := hA.perfect
  let := hB.perfect
  have hzA : center A = ⊥ :=
    (inferInstance : (center A).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative A (center_eq_top_iff.mp he))
  have hzB : center B = ⊥ :=
    (inferInstance : (center B).Normal).eq_bot_or_eq_top.resolve_right
      (fun he => Group.IsPerfect.not_isMulCommutative B (center_eq_top_iff.mp he))
  have hn : A ≠ B := by
    intro he
    have hab := b.first_component.eq_of_map_quotient_eq b.second_component (pCore 2 Mc) he
    have hk : b.K1 = b.K2 := by
      have hh := congrArg (map Mc.subtype) hab
      simpa only [map_subgroupOf_eq_of_le b.first_le,map_subgroupOf_eq_of_le b.second_le] using hh
    obtain ⟨t,_,hnt,ht⟩ := b.exchanged
    exact hnt (inv_mem_iff.mp (mem_normalizer_iff_map_conj_eq.mpr (ht.trans hk.symm)))
  have hc : A ≤ centralizer (B : Set (Mc ⧸ pCore 2 Mc)) :=
    commutator_eq_bot_iff_le_centralizer.mp
      (simple_subnormal_commute_of_ne A B hA.subnormal hB.subnormal hn)
  have hd : Disjoint A B := by
    apply disjoint_def.mpr
    intro x hx hy
    have hh : (⟨x,hx⟩ : A) ∈ center A := mem_center_iff.mpr fun y =>
      Subtype.ext ((hc y.property x hy).symm)
    exact congrArg Subtype.val (show (⟨x,hx⟩ : A) = 1 from mem_bot.mp (hzA ▸ hh))
  have hj : A ⊔ B = ((residualClosure H Mc).subgroupOf Mc).map q := by
    rw [←Subgroup.map_sup,←subgroupOf_sup b.first_le b.second_le,b.join_eq]
  let : ((residualClosure H Mc).subgroupOf Mc).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  have hAB : (A ⊔ B).Normal := by
    rw [hj]
    exact Normal.map inferInstance q (QuotientGroup.mk'_surjective _)
  let := hAB
  have hquot : IsPGroup 2 ((Mc ⧸ pCore 2 Mc) ⧸ (A ⊔ B)) := by
    apply IsPGroup.of_card (n := 5)
    rw [←index_eq_card,hj,source_exchanged_quotient_closure_index s]
    rfl
  have hH : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 s.ambient T s.empty s.maximal s.unique
      s.many s.module_card s.action H s.outside.1 s.outside.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hnorm := source_exchanged_core_normalizes_factors s b
  intro x hx
  let xm : Mc := ⟨x,hH (pCoreIn_le 2 H hx)⟩
  have hfirst := source_exchanged_core_action_inner s b b.first_le b.first_component b.first_model
    ((le_sup_left : b.K1 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq) ⟨x,hnorm.1 hx⟩ hx
  have hsecond := source_exchanged_core_action_inner s b b.second_le b.second_component b.second_model
    ((le_sup_right : b.K2 ≤ b.K1 ⊔ b.K2).trans_eq b.join_eq) ⟨x,hnorm.2 hx⟩ hx
  have hmem := mem_product_of_paired_inner_actions A B hd hc hzA hzB hquot
    (pCore_quotient_pCore_eq_bot 2) (q xm)
    (quotient_inner_action b.first_le b.first_component xm (hnorm.1 hx) hfirst)
    (quotient_inner_action b.second_le b.second_component xm (hnorm.2 hx) hsecond)
  rw [hj] at hmem
  have hx' : xm ∈ (((residualClosure H Mc).subgroupOf Mc).map q).comap q := hmem
  rw [comap_map_eq,QuotientGroup.ker_mk'] at hx'
  have hm := mem_map_of_mem Mc.subtype hx'
  rw [Subgroup.map_sup,map_subgroupOf_eq_of_le (show residualClosure H Mc ≤ Mc from
    b.join_eq ▸ sup_le b.first_le b.second_le)] at hm
  exact hm

include s in
/-- The exchanged closure forces a quotient of order 32 of the actual actor
of order 200. The original Sylow subgroup makes the map surjective. -/
theorem source_quintic_exclusion : False := by
  obtain ⟨b⟩ := source_exchanged_factor_data s
  have hK : residualClosure H Mc ≤ Mc := b.join_eq ▸ sup_le b.first_le b.second_le
  have hH : H ≤ Mc := by
    have he := (Section02.source_lemma_14_2_3 s.ambient T s.empty s.maximal s.unique
      s.many s.module_card s.action H s.outside.1 s.outside.2).1
    exact (show Mc ∈ maximalTwoLocalOvergroups H from he ▸ Set.mem_singleton Mc).2
  have hTM : (T : Subgroup G) ≤ Mc := s.outside.1.2.trans hH
  let N := (residualClosure H Mc ⊔ Mc.pCoreIn 2).subgroupOf Mc
  have he : N = (residualClosure H Mc).subgroupOf Mc ⊔ pCore 2 Mc := by
    dsimp only [N]
    rw [subgroupOf_sup hK (pCoreIn_le 2 Mc)]
    congr 1
    ext x
    exact mem_map_iff_mem Mc.subtype_injective
  let : ((residualClosure H Mc).subgroupOf Mc).Normal :=
    normal_subgroupOf_of_le_normalizer (le_normalizer_conjugateSpanBy _ _)
  have hN : N.Normal := by rw [he]; infer_instance
  let := hN
  have hi : Nat.card (Mc ⧸ N) = 32 := by
    rw [←index_eq_card]
    exact source_exchanged_core_supplement_index s
  have hq : IsPGroup 2 (Mc ⧸ N) := IsPGroup.of_card (n := 5) hi
  let q := QuotientGroup.mk' N
  let P := (T.subtype hTM).mapSurjective (f := q) (QuotientGroup.mk'_surjective N)
  have hP : (P : Subgroup (Mc ⧸ N)) = ⊤ :=
    (P.is_maximal' (hq.of_injective (⊤ : Subgroup (Mc ⧸ N)).subtype Subtype.val_injective) le_top).symm
  let f := q.comp (inclusion hH)
  have hf : Function.Surjective f := by
    intro y
    have hy : y ∈ (P : Subgroup (Mc ⧸ N)) := hP ▸ mem_top y
    obtain ⟨x,hx,hxy⟩ := hy
    exact ⟨⟨x,s.outside.1.2 hx⟩,hxy⟩
  have hk : pCore 2 H ≤ f.ker := by
    intro x hx
    apply (QuotientGroup.eq_one_iff _).mpr
    exact source_exchanged_core_le_closure_supplement s (mem_map_of_mem H.subtype hx)
  let fbar := QuotientGroup.lift (pCore 2 H) f hk
  have hbar : Function.Surjective fbar := by
    intro y
    obtain ⟨x,rfl⟩ := hf y
    exact ⟨QuotientGroup.mk' (pCore 2 H) x,rfl⟩
  have hd := card_dvd_of_surjective fbar hbar
  rw [hi,OddCriticalPair.exchanged_actor_card a (T : Subgroup G) 5 H0 H1 H2 s.factors] at hd
  norm_num at hd

end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ModuleGeometry
