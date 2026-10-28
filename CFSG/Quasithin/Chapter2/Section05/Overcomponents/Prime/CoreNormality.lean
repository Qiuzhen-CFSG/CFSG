module
public import CFSG.Quasithin.Chapter2.Section05.Overcomponents.Prime.CoreFour
public import CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource.Maximality
public import Theory.GroupAction.InvolutionSylow
public import Theory.GroupTheory.GeneralizedFitting.SylowNormalizedComponent
public import CFSG.Quasithin.Chapter2.Section05.ComponentSelection.TwoComponentCenterSource
public import Theory.GroupTheory.SylowIndexTwoExtension


/-! The four-centralizer alternative forces original component normality,
as in source 2.5.19, printed p.561. -/
public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource

variable {G : Type*} [Group G] [Finite G]

/-- A normalized subgroup with order-two center, together with a disjoint
central involution, forces the involution centralizer to exceed four. -/
theorem four_lt_centralizer_card_of_center_two
    (W P : Subgroup G) (hPW : P ≤ W) (hPcard : 4 < Nat.card P)
    (hZ : Nat.card (center P) = 2)
    (t i : G) (ht : orderOf t = 2) (htW : t ∈ W)
    (htC : t ∈ centralizer (P : Set G)) (htP : t ∉ P)
    (hiW : i ∈ W) (hiP : i ∈ normalizer (P : Set G))
    (hti : Commute t i) :
    4 < Nat.card (W ⊓ centralizer ({i} : Set G) : Subgroup G) := by
  obtain ⟨z,hz⟩ := exists_prime_orderOf_dvd_card' (G := center P) 2 (hZ ▸ dvd_rfl)
  let a : G := ((z : P) : G)
  have ha : orderOf a = 2 := by simpa only [a,orderOf_coe] using hz
  let Z := (center P).map P.subtype
  have haZ : a ∈ Z := mem_map_of_mem P.subtype z.property
  have hZZ : Z = zpowers a := by
    apply (eq_of_le_of_card_ge (zpowers_le.mpr haZ) ?_).symm
    rw [Nat.card_zpowers,ha,card_map_of_injective P.subtype_injective,hZ]
  have hiZ : i ∈ normalizer (Z : Set G) :=
    normalizer_le_normalizer_characteristic_image P (center P) hiP
  rw [hZZ,normalizer_zpowers_eq_centralizer_of_order_two a ha] at hiZ
  have hia : Commute a i := (mem_centralizer_singleton_iff.mp hiZ).symm
  have haP : a ∈ P := (z : P).property
  have haC : a ∈ centralizer (P : Set G) := by
    intro x hx
    exact congrArg Subtype.val (mem_center_iff.mp z.property (⟨x,hx⟩ : P))
  have hta : Commute t a := (htC a haP).symm
  have hne : t ≠ a := fun he => htP (he.symm ▸ haP)
  let R := W ⊓ centralizer ({i} : Set G)
  let V := closure ({t,a} : Set G)
  have hV : IsKleinFour V := isKleinFour_closure_pair_of_orderOf t a ht ha hne hta
  have hVR : V ≤ R := (closure_le _).mpr (by
    rintro x (rfl | rfl)
    · exact ⟨htW,mem_centralizer_singleton_iff.mpr hti.eq⟩
    · exact ⟨hPW haP,mem_centralizer_singleton_iff.mpr hia.eq⟩)
  have hVC : V ≤ centralizer (P : Set G) := (closure_le _).mpr (by
    rintro x (rfl | rfl) <;> assumption)
  by_contra hn
  have hcard : Nat.card R ≤ 4 := by
    change ¬ 4 < Nat.card R at hn
    omega
  have he : V = R := eq_of_le_of_card_ge hVR (by rw [hV.card_four]; exact hcard)
  have hiR : i ∈ R := ⟨hiW,mem_centralizer_singleton_iff.mpr rfl⟩
  have hiC : i ∈ centralizer (P : Set G) := hVC (he.symm ▸ hiR)
  have hPR : P ≤ R := le_inf hPW
    (fun p hp => mem_centralizer_singleton_iff.mpr (hiC p hp))
  have hp := (card_le_of_le hPR).trans hcard
  omega

/-- A component with source Sylow shape is normal when a central Sylow
involution and its centralizing actor have only a four-group centralizer
inside C_S(K). This is the implication (2) ⇒ (1) on printed p.561. -/
theorem component_normal_of_four_sylow_centralizer
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    (K : Subgroup G) (hK : IsComponent G K) (hZ : center K = ⊥)
    (hshape : ∀ P : Sylow 2 K, Nat.card (center P) = 2 ∧ 4 < Nat.card P)
    (S : Sylow 2 G) (t i : G) (ht : orderOf t = 2)
    (htS : t ∈ (S : Subgroup G)) (htZ : t ∈ center G)
    (hiS : i ∈ (S : Subgroup G)) (hiK : i ∈ centralizer (K : Set G))
    (hfour : Nat.card (((S : Subgroup G) ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G) : Subgroup G) ≤ 4) : K.Normal := by
  by_contra hn
  have hiN := (hK.normal_or_index_two_of_odd_rank_le_two hrank).resolve_left hn
  let N := normalizer (K : Set G)
  let : N.Normal := normal_of_index_eq_two hiN
  obtain ⟨g,hg⟩ : ∃ g : G, K.map (MulAut.conj g).toMonoidHom ≠ K := by
    by_contra! h
    exact hn (normal_iff_map_conj_eq.mpr h)
  let L := K.map (MulAut.conj g).toMonoidHom
  let e : K ≃* L := (MulAut.conj g).subgroupMap K
  have hL : IsComponent G L := hK.map_conj g
  have hLC : L ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp (hL.commutator_eq_bot_of_ne hK hg)
  have hNL : normalizer (L : Set G) = N := by
    change normalizer (K.map (MulAut.conj g).toMonoidHom : Set G) = N
    rw [← map_equiv_normalizer_eq]
    exact normal_iff_map_conj_eq.mp (inferInstance : N.Normal) g
  have hiL : i ∈ normalizer (L : Set G) := by
    rw [hNL]
    exact Subgroup.centralizer_le_normalizer _ hiK
  obtain ⟨P,hP⟩ := S.exists_subgroupOf_eq_of_subnormal L hL.1
  let P₀ := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let eP : P ≃* P₀ := (P : Subgroup L).equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  let U := (S : Subgroup G) ⊓ L
  have hUeq : (P : Subgroup L).map L.subtype = U := by
    rw [hP,subgroupOf_map_subtype]
  let eU : P ≃* U := ((P : Subgroup L).equivMapOfInjective L.subtype
    L.subtype_injective).trans (MulEquiv.subgroupCongr hUeq)
  have hUZ : Nat.card (center U) = 2 :=
    (Nat.card_congr (centerCongr eU).toEquiv).symm.trans
      ((Nat.card_congr (centerCongr eP).toEquiv).trans (hshape P₀).1)
  have hUcard : 4 < Nat.card U := (hshape P₀).2.trans_eq
    ((Nat.card_congr eP.toEquiv).symm.trans (Nat.card_congr eU.toEquiv))
  have hiU : i ∈ normalizer (U : Set G) :=
    inf_normalizer_le_normalizer_inf ⟨(S : Subgroup G).le_normalizer hiS,hiL⟩
  have htU : t ∉ U := by
    intro him
    have htLK : e.symm (⟨t,him.2⟩ : L) ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      apply e.injective
      simp only [map_mul,e.apply_symm_apply]
      exact Subtype.ext (mem_center_iff.mp htZ (e k))
    rw [hZ,mem_bot] at htLK
    have htLone : (⟨t,him.2⟩ : L) = 1 := e.symm.map_eq_one_iff.mp htLK
    have htt : t = 1 := congrArg (fun x : L => (x : G)) htLone
    rw [htt,orderOf_one] at ht
    omega
  let W := (S : Subgroup G) ⊓ centralizer (K : Set G)
  change Nat.card (W ⊓ centralizer ({i} : Set G) : Subgroup G) ≤ 4 at hfour
  have hlarge := four_lt_centralizer_card_of_center_two W U
    (le_inf inf_le_left (inf_le_right.trans hLC)) hUcard hUZ t i ht
    ⟨htS,fun k _ => mem_center_iff.mp htZ k⟩
    (fun u _ => mem_center_iff.mp htZ u) htU ⟨hiS,hiK⟩ hiU
    (mem_center_iff.mp htZ i).symm
  omega

/-- In the original four-Sylow configuration, a component with the source
Sylow shape is normal. A second conjugate component would supply a
normalized Sylow with center two and force a larger simultaneous centralizer. -/
theorem component_normal_of_four_simultaneous_centralizer
    (hrank : ∀ p : ℕ, p.Prime → Odd p → primeRank p G ≤ 2)
    (K : Subgroup G) (hK : IsComponent G K) (hZ : center K = ⊥)
    (hshape : ∀ P : Sylow 2 K, Nat.card (center P) = 2 ∧ 4 < Nat.card P)
    (i t : G) (hi : orderOf i = 2) (hiZ : i ∈ center G)
    (ht : orderOf t = 2) (htK : t ∈ centralizer (K : Set G))
    (hfour : ∀ Q : Subgroup G, IsPGroup 2 Q →
      Q ≤ centralizer ({t} : Set G) ⊓ centralizer (K : Set G) → Nat.card Q ≤ 4) :
    K.Normal := by
  by_contra hn
  have hiN := (hK.normal_or_index_two_of_odd_rank_le_two hrank).resolve_left hn
  let N := normalizer (K : Set G)
  let : N.Normal := normal_of_index_eq_two hiN
  obtain ⟨g,hg⟩ : ∃ g : G, K.map (MulAut.conj g).toMonoidHom ≠ K := by
    by_contra! h
    exact hn (normal_iff_map_conj_eq.mpr h)
  let L := K.map (MulAut.conj g).toMonoidHom
  let e : K ≃* L := (MulAut.conj g).subgroupMap K
  have hLC : L ≤ centralizer (K : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp ((hK.map_conj g).commutator_eq_bot_of_ne hK hg)
  have hNL : normalizer (L : Set G) = N := by
    change normalizer (K.map (MulAut.conj g).toMonoidHom : Set G) = N
    rw [← map_equiv_normalizer_eq]
    exact normal_iff_map_conj_eq.mp (inferInstance : N.Normal) g
  have htL : t ∈ normalizer (L : Set G) := by
    rw [hNL]
    exact Subgroup.centralizer_le_normalizer _ htK
  let a : MulAut L := L.normalizerMonoidHom ⟨t,htL⟩
  have ha : a ^ 2 = 1 := by
    change (L.normalizerMonoidHom ⟨t,htL⟩)^2 = 1
    rw [← map_pow,show (⟨t,htL⟩ : normalizer (L : Set G))^2 = 1 from
      Subtype.ext (ht ▸ pow_orderOf_eq_one t),map_one]
  obtain ⟨P,hP⟩ := MulAut.exists_fixed_sylow_two a ha
  let P₀ := P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let eP : P ≃* P₀ := (P : Subgroup L).equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  have hPZ : Nat.card (center P) = 2 :=
    (Nat.card_congr (centerCongr eP).toEquiv).trans (hshape P₀).1
  have hPcard : 4 < Nat.card P := (hshape P₀).2.trans_eq (Nat.card_congr eP.toEquiv).symm
  let U := (P : Subgroup L).map L.subtype
  let eU : P ≃* U := (P : Subgroup L).equivMapOfInjective L.subtype L.subtype_injective
  have hUZ : Nat.card (center U) = 2 :=
    (Nat.card_congr (centerCongr eU).toEquiv).symm.trans hPZ
  have hUcard : 4 < Nat.card U := hPcard.trans_eq (Nat.card_congr eU.toEquiv)
  have htU : t ∈ normalizer (U : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    have hp : (P : Subgroup L).map a.toMonoidHom = P := congrArg Sylow.toSubgroup hP
    have hm := congrArg (Subgroup.map L.subtype) hp
    rw [map_map] at hm ⊢
    exact hm
  have hiU : i ∉ U := by
    intro him
    have hiL : i ∈ L := map_subtype_le _ him
    have hiLK : e.symm (⟨i,hiL⟩ : L) ∈ center K := by
      apply mem_center_iff.mpr
      intro k
      apply e.injective
      simp only [map_mul,e.apply_symm_apply]
      apply Subtype.ext
      exact mem_center_iff.mp hiZ (e k)
    rw [hZ,mem_bot] at hiLK
    have hiLone : (⟨i,hiL⟩ : L) = 1 := e.symm.map_eq_one_iff.mp hiLK
    have hii : i = 1 := congrArg (fun x : L => (x : G)) hiLone
    rw [hii,orderOf_one] at hi
    omega
  have hiUC : i ∈ centralizer (U : Set G) := fun u _ => mem_center_iff.mp hiZ u
  let W := (U ⊔ zpowers i) ⊔ zpowers t
  have hiN_U : zpowers i ≤ normalizer (U : Set G) :=
    zpowers_le.mpr (Subgroup.centralizer_le_normalizer _ hiUC)
  have htN_Ui : zpowers t ≤ normalizer ((U ⊔ zpowers i : Subgroup G) : Set G) := by
    apply zpowers_le.mpr
    apply normalizer_inf_normalizer_le_normalizer_sup U (zpowers i)
    refine ⟨htU,?_⟩
    rw [normalizer_zpowers_eq_centralizer_of_order_two i hi]
    exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hiZ t)
  have hWp : IsPGroup 2 W := ((P.isPGroup'.map L.subtype).to_sup_of_normal_left'
    (IsPGroup.of_card (p := 2) (n := 1) (by simpa [Nat.card_zpowers] using hi)) hiN_U).to_sup_of_normal_left'
    (IsPGroup.of_card (p := 2) (n := 1) (by simpa [Nat.card_zpowers] using ht)) htN_Ui
  have hWC : W ≤ centralizer (K : Set G) := sup_le
    (sup_le ((map_subtype_le _).trans hLC)
      (zpowers_le.mpr (fun k _ => mem_center_iff.mp hiZ k))) (zpowers_le.mpr htK)
  have hlarge := four_lt_centralizer_card_of_center_two W U
    (le_sup_left.trans le_sup_left) hUcard hUZ i t hi
    (mem_sup_left (mem_sup_right (mem_zpowers i))) hiUC hiU
    (mem_sup_right (mem_zpowers t)) htU (mem_center_iff.mp hiZ t).symm
  have hsmall := hfour (W ⊓ centralizer ({t} : Set G)) (hWp.to_le inf_le_left)
    (le_inf inf_le_right (inf_le_left.trans hWC))
  omega

end CFSG.Quasithin.Chapter2.Section05.OvercomponentsSource
namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection OvercomponentsSource
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

private theorem shape_card_gt_four {P : Type*} [Group P]
    (h : SourceSylowTwoShape P) : 4 < Nat.card P := by
  unfold SourceSylowTwoShape at h
  rcases h with ⟨m,hm,⟨e⟩⟩ | ⟨e⟩
  · rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have hh := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hm
    norm_num at hh
    omega
  · obtain ⟨e⟩ := e
    rw [Nat.card_congr e.toEquiv, Semidihedral.standardModel_card]
    norm_num

/-- Once source 2.5.19(4) gives component persistence, the actual
four-group Sylow centralizer makes the component normal in C_G(i).
This is the normalization step of source 2.5.21 on printed p.566. -/
theorem source_prime_core_normalization_of_component
    (c : MathieuSourceSetup H K M S z) [(K.subgroupOf H).Normal]
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (hstar : H ∈ gammaStar (Chapter1.He G) M)
    (hmodel : ∃ k : ℕ, 2 ≤ k ∧ Nonempty (twoCore H ≃* DihedralGroup (2 ^ k)))
    (t i : G) (ht : orderOf t = 2) (hi : orderOf i = 2)
    (htC : t ∈ twoCore H) (hiC : i ∈ twoCore H)
    (htZ : t ∈ centerIn ((S : Subgroup H).map H.subtype))
    (hcomp : IsComponentIn K (centralizer ({i} : Set G))) :
    centralizer ({i} : Set G) ≤ normalizer (K : Set G) := by
  by_cases hti : t = i
  · subst i
    exact source_component_normal_in_centralizer_t c hG hempty hgen hb hstar t ht htC htZ
  let J := centralizer ({i} : Set G)
  let D := K.subgroupOf J
  let eD : D ≃* K := subgroupOfEquivOfLe hcomp.1
  have hcore : twoCore H ≤ centralizer (K : Set G) := by
    rw [MathieuSourceSetup.core_eq_sylow_centralizer c hgen]
    exact inf_le_right
  have htJ : t ∈ J := mem_centralizer_singleton_iff.mpr
    (htZ.2 i (pCoreIn_le_sylow H S hiC)).symm
  let ti : J := ⟨t,htJ⟩
  let ii : J := ⟨i,mem_centralizer_singleton_iff.mpr rfl⟩
  have hti' : orderOf ti = 2 := (orderOf_coe ti).symm.trans ht
  have hii : orderOf ii = 2 := (orderOf_coe ii).symm.trans hi
  have hiiZ : ii ∈ center J := mem_center_iff.mpr (fun x =>
    Subtype.ext (mem_centralizer_singleton_iff.mp x.property))
  have htiD : ti ∈ centralizer (D : Set J) := by
    intro k hk
    exact Subtype.ext (hcore htC k hk)
  have hZD : center D = ⊥ := by
    apply eq_bot_iff.mpr
    intro d hd
    have hm : eD d ∈ center K := (centerCongr eD ⟨d,hd⟩).property
    rw [MathieuSourceSetup.component_center_eq_bot c hG hempty hgen,mem_bot] at hm
    exact eD.map_eq_one_iff.mp hm
  have hshape (P : Sylow 2 D) : Nat.card (center P) = 2 ∧ 4 < Nat.card P := by
    let Q := P.mapSurjective (f := eD.toMonoidHom) eD.surjective
    let eP : P ≃* Q := (P : Subgroup D).equivMapOfInjective eD.toMonoidHom eD.injective
    have hs := (MathieuSourceSetup.small_remaining_component c hG hempty hgen hb).sylowTwoShape Q
    refine ⟨(Nat.card_congr (centerCongr eP).toEquiv).trans hs.center_card,?_⟩
    exact (shape_card_gt_four hs).trans_eq (Nat.card_congr eP.toEquiv).symm
  obtain ⟨_,hfour,_⟩ := source_prime_core_four c hG hempty hgen hb hstar hmodel
    t i ht hi hti htC hiC htZ
  have hSyl := source_prime_core_four_sylow c hG hempty hgen hb hstar hmodel
    t i ht hi hti htC hiC htZ
  let C := centralizer ({t} : Set G) ⊓ centralizer (K : Set G) ⊓ J
  obtain ⟨P,hP⟩ := hSyl
  have hbound (Q : Subgroup J) (hQ : IsPGroup 2 Q)
      (hQC : Q ≤ centralizer ({ti} : Set J) ⊓ centralizer (D : Set J)) : Nat.card Q ≤ 4 := by
    let U := Q.map J.subtype
    have hUC : U ≤ C := by
      rintro x ⟨q,hq,rfl⟩
      refine ⟨⟨?_,?_⟩,q.property⟩
      · exact mem_centralizer_singleton_iff.mpr
          (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hQC hq).1))
      · intro k hk
        exact congrArg Subtype.val ((hQC hq).2 ⟨k,hcomp.1 hk⟩ hk)
    have hbnd := Subgroup.card_le_sylow_two ((hQ.map J.subtype).comap_subtype :
      IsPGroup 2 (U.subgroupOf C)) P
    change Nat.card (U.subgroupOf C) ≤ Nat.card P at hbnd
    rw [Nat.card_congr (subgroupOfEquivOfLe hUC).toEquiv] at hbnd
    change Nat.card (Q.map J.subtype) ≤ Nat.card P at hbnd
    rw [card_map_of_injective J.subtype_injective] at hbnd
    have hPc : Nat.card P = 4 := by
      rw [←card_map_of_injective C.subtype_injective,hP]
      exact hfour.card_four
    exact hbnd.trans_eq hPc
  have hDn : D.Normal := component_normal_of_four_simultaneous_centralizer
    (hG.involution_centralizer_sqtk hi).stronglyQuasithin D hcomp.2 hZD hshape
    ii ti hii hiiZ hti' htiD hbound
  exact (normal_subgroupOf_iff_le_normalizer hcomp.1).mp hDn

end CFSG.Quasithin.Chapter2.Section05.Overcomponents

namespace CFSG.Quasithin.Chapter2.Section05.Overcomponents
open ComponentRefinement ComponentSelection OvercomponentsSource
variable {G : Type*} [Group G] [Finite G]
  {H K M : Subgroup G} {S : Sylow 2 H} {z : G}

/-- The small-centralizer conclusion of source 2.5.19 forces normality
of the original component, without an independent companion assumption. -/
theorem source_component_normal_of_four_core_centralizer
    (c : MathieuSourceSetup H K M S z)
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (hempty : gammaEvenZero (Chapter1.He G) M = ∅)
    (hgen : H = K ⊔ (S : Subgroup H).map H.subtype)
    (hb : ¬ ClassificationModels.IsBenderModel K)
    (i : G) (hiS : i ∈ (S : Subgroup H).map H.subtype)
    (hiK : i ∈ centralizer (K : Set G))
    (hfour : Nat.card ((((S : Subgroup H).map H.subtype) ⊓ centralizer (K : Set G)) ⊓
      centralizer ({i} : Set G) : Subgroup G) ≤ 4) : (K.subgroupOf H).Normal := by
  let D := K.subgroupOf H
  let eD : D ≃* K := subgroupOfEquivOfLe c.component_le
  obtain ⟨t,ht,htC,htZ⟩ := MathieuSourceSetup.exists_central_core_involution c
  have htY := pCoreIn_le_sylow H S htC
  let ti : H := ⟨t,map_subtype_le _ htY⟩
  let ii : H := ⟨i,map_subtype_le _ hiS⟩
  have htS : ti ∈ (S : Subgroup H) := by
    obtain ⟨y,hy,he⟩ := htY
    exact (Subtype.ext he : y = ti) ▸ hy
  have hiS' : ii ∈ (S : Subgroup H) := by
    obtain ⟨y,hy,he⟩ := hiS
    exact (Subtype.ext he : y = ii) ▸ hy
  have hti : orderOf ti = 2 := (orderOf_coe ti).symm.trans ht
  have hHJ := (MathieuSourceSetup.central_core_involution_centralizer c hgen t ht htC htZ).1
  have htiZ : ti ∈ center H := mem_center_iff.mpr (fun y =>
    Subtype.ext (mem_centralizer_singleton_iff.mp (hHJ y.property)))
  have hiiD : ii ∈ centralizer (D : Set H) := by
    intro k hk
    exact Subtype.ext (hiK k hk)
  have hZD : center D = ⊥ := by
    apply eq_bot_iff.mpr
    intro d hd
    have hm : eD d ∈ center K := (centerCongr eD ⟨d,hd⟩).property
    rw [MathieuSourceSetup.component_center_eq_bot c hG hempty hgen,mem_bot] at hm
    exact eD.map_eq_one_iff.mp hm
  have hshape (P : Sylow 2 D) : Nat.card (center P) = 2 ∧ 4 < Nat.card P := by
    let Q := P.mapSurjective (f := eD.toMonoidHom) eD.surjective
    let eP : P ≃* Q := (P : Subgroup D).equivMapOfInjective eD.toMonoidHom eD.injective
    have hs := (MathieuSourceSetup.small_remaining_component c hG hempty hgen hb).sylowTwoShape Q
    refine ⟨(Nat.card_congr (centerCongr eP).toEquiv).trans hs.center_card,?_⟩
    exact (shape_card_gt_four hs).trans_eq (Nat.card_congr eP.toEquiv).symm
  have hQ : pCore 2 H ≠ ⊥ := by
    intro he
    have hn := (c.gamma.elim (fun h => h.1.1) (fun h => h.1)).1
    exact hn (by simp only [twoCore,he,Subgroup.map_bot])
  have hrank := Theory.Quasithin.primeRank_subgroup_le_two_of_normal_two_subgroup
    hG.quasithin H (pCore 2 H) hQ pCore_isPGroup
  apply component_normal_of_four_sylow_centralizer hrank D c.component hZD hshape
    S ti ii hti htS htiZ hiS' hiiD
  let W := ((S : Subgroup H) ⊓ centralizer (D : Set H)) ⊓ centralizer ({ii} : Set H)
  have hmap : W.map H.subtype ≤ (((S : Subgroup H).map H.subtype) ⊓
      centralizer (K : Set G)) ⊓ centralizer ({i} : Set G) := by
    rintro x ⟨w,hw,rfl⟩
    refine ⟨⟨mem_map_of_mem H.subtype hw.1.1,?_⟩,?_⟩
    · intro k hk
      exact congrArg Subtype.val (hw.1.2 ⟨k,c.component_le hk⟩ hk)
    · exact mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hw.2))
  have hc := (card_le_of_le hmap).trans hfour
  rwa [card_map_of_injective H.subtype_injective] at hc

end CFSG.Quasithin.Chapter2.Section05.Overcomponents