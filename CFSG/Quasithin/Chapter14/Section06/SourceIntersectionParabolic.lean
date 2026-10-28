module
public import CFSG.Quasithin.Chapter14.Section06.SourceIntersectionFactorization
public import Theory.GroupTheory.PCoreFrattiniTransport

/-!
# The first intersection parabolic

Put L_I = O²(L ∩ I) and I₁ = L_I (T ∩ I). From the factorization
L = L_I O₂(L), the action of L_I on the original four-element module
has image C₃. The suitable involution supplies a nontrivial two-element
image of T ∩ I. Hence I₁ has image S₃. The literal action kernel is
O₂(LT), and Sylow maximality identifies O₂(I₁) with
(T ∩ I) ∩ O₂(LT). This also gives L_I/O₂(L_I) ≃ C₃.

The factorization and O₂(L) ≤ C_G(V) ≤ M_c show that L_I ≤ M_c would
force LT ≤ M_c, contrary to the unique maximal two-local overgroup M
of LT. Thus L_I escapes M_c.

The explicit Sylow premise is supplied by
`suitable_involution_intersection_sylow`; the factorization premise is
supplied by original 14.6.6(3–5). All module actions and quotient maps
come from the original rank-two source hypotheses.
Source: Aschbacher–Smith, refs/quasithin.pdf, the first-parabolic step
of 14.6.6(6), printed pp.1023–1024, and the opening of 14.6.10, p.1028.
-/

public section
open Subgroup Theory.GroupTheory
open scoped Pointwise
namespace CFSG.Quasithin.Chapter14.Section06
variable {G : Type*} [Group G] [Finite G]

private theorem cubic_image_core_quotient
    (f : G →* Equiv.Perm (Fin 3)) (R : Subgroup G)
    (hk : IsPGroup 2 f.ker) (hc : Nat.card (R.map f) = 3) :
    Nonempty ((R ⧸ pCore 2 R) ≃* Multiplicative (ZMod 3)) := by
  let r := f.subgroupMap R
  have hkr : IsPGroup 2 r.ker := by
    rw [show r = f.subgroupMap R from rfl, ker_subgroupMap]
    exact hk.comap_subtype
  have h3 : IsPGroup 3 (R.map f) := IsPGroup.of_card (n := 1) (by simpa using hc)
  have hz : pCore 2 (R.map f) = ⊥ := by
    have hh := IsPGroup.disjoint_of_ne 2 3 (by decide) (pCore 2 (R.map f)) ⊤
      pCore_isPGroup (h3.to_subgroup ⊤)
    simpa using hh.eq_bot
  let e := r.pCoreQuotientEquiv (f.subgroupMap_surjective R) hkr
  have hcard : Nat.card (R ⧸ pCore 2 R) = 3 := by
    rw [Nat.card_congr e.toEquiv,hz,Nat.card_congr QuotientGroup.quotientBot.toEquiv,hc]
  exact ⟨mulEquivOfPrimeCardEq hcard (by simp)⟩

open Chapter12.Section08
private theorem rankTwo_intersection_parabolic
    {K : GroupClass} {T : Sylow 2 G} {L M : Subgroup G}
    (h : RankTwoHypothesis K T L M) (I : Subgroup G)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ I) I)
    (hmove : ¬ (T : Subgroup G) ⊓ I ≤ centralizer (rankTwoSeed T M : Set G))
    (hcover : (L : Set G) =
      ((pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype : Set G) *
        (L.pCoreIn 2 : Set G)) :
    let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
    let P := R ⊔ ((T : Subgroup G) ⊓ I)
    Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Multiplicative (ZMod 3)) ∧
      P.pCoreIn 2 = ((T : Subgroup G) ⊓ I) ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 := by
  let J := L ⊔ (T : Subgroup G)
  let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
  let S := (T : Subgroup G) ⊓ I
  let P := R ⊔ S
  have hRL : R ≤ L := (map_subtype_le _).trans inf_le_left
  have hRI : R ≤ I := (map_subtype_le _).trans inf_le_right
  have hLJ : L ≤ J := le_sup_left
  have hRJ : R ≤ J := hRL.trans hLJ
  have hSJ : S ≤ J := inf_le_left.trans le_sup_right
  have hPJ : P ≤ J := sup_le hRJ hSJ
  let a := setupSeedAction J (rankTwoSeed T M)
    ((sup_le h.L_le h.sylow_le).trans RankTwoHypothesis.M_normalizes_seed)
  obtain ⟨e⟩ := h.seedAut_model
  let f := e.toMonoidHom.comp a
  have hker : f.ker = pCore 2 J := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective]
    exact h.literal_action_kernel
  have hLimage : (L.subgroupOf J).map f = pResidual 2 (Equiv.Perm (Fin 3)) := by
    have hmap : (L.subgroupOf J).map a =
        (setupSeedAction L (rankTwoSeed T M) h.L_normalizes_seed).range := by
      ext b
      constructor
      · rintro ⟨l,hl,rfl⟩
        exact ⟨⟨l,hl⟩,rfl⟩
      · rintro ⟨l,rfl⟩
        exact ⟨⟨l,hLJ l.property⟩,l.property,rfl⟩
    change (L.subgroupOf J).map (e.toMonoidHom.comp a) = _
    rw [←map_map,hmap,h.L_action_range,map_pResidual]
  have hRimage : (R.subgroupOf J).map f = (L.subgroupOf J).map f := by
    apply le_antisymm (map_mono (comap_mono hRL))
    rintro x ⟨l,hl,rfl⟩
    have hl' : (l : G) ∈ (L : Set G) := hl
    rw [hcover] at hl'
    obtain ⟨r,hr,q,hq,he⟩ := Set.mem_mul.mp hl'
    have hqJ : q ∈ J := hLJ (pCoreIn_le 2 L hq)
    have hqker : (⟨q,hqJ⟩ : J) ∈ f.ker := by
      rw [hker]
      have hh : q ∈ J.pCoreIn 2 := by
        rw [←h.centralizer]
        exact ⟨hqJ,(h.centralizer_L.ge hq).2⟩
      obtain ⟨v,hv,he⟩ := hh
      exact (Subtype.ext he : v = ⟨q,hqJ⟩) ▸ hv
    refine ⟨⟨r,hRJ hr⟩,hr,?_⟩
    have hmul : (⟨r,hRJ hr⟩ : J) * ⟨q,hqJ⟩ = l := Subtype.ext he
    have hm := congrArg f hmul
    have hqone : f ⟨q,hqJ⟩ = 1 := hqker
    simpa only [map_mul,hqone,mul_one] using hm
  have hRc : Nat.card ((R.subgroupOf J).map f) = 3 := by
    rw [hRimage,hLimage,Equiv.Perm.twoResidual_eq_alternating,nat_card_alternatingGroup]
    norm_num [Nat.factorial]
  have hSne : (S.subgroupOf J).map f ≠ ⊥ := by
    intro hb
    apply hmove
    intro s hs
    have hz := (Subgroup.map_eq_bot_iff _).mp hb (show (⟨s,hSJ hs⟩ : J) ∈ S.subgroupOf J from hs)
    have ha : a ⟨s,hSJ hs⟩ = 1 := by
      apply e.injective
      change e (a ⟨s,hSJ hs⟩) = 1 at hz
      simpa only [map_one] using hz
    exact (setupSeedAction_ker J (rankTwoSeed T M) _).le ha
  have hSc : Nat.card ((S.subgroupOf J).map f) = 2 := by
    have hp : IsPGroup 2 ((S.subgroupOf J).map f) :=
      (T.isPGroup'.to_le (show S ≤ (T : Subgroup G) from inf_le_left)).comap_subtype.map f
    have hd : Nat.card ((S.subgroupOf J).map f) ∣ 2 * 3 := by
      simpa [Nat.card_eq_fintype_card,Fintype.card_perm,Nat.factorial] using
        ((S.subgroupOf J).map f).card_subgroup_dvd_card
    have hc : Nat.Coprime (Nat.card ((S.subgroupOf J).map f)) 3 := by
      obtain ⟨n,hn⟩ := hp.exists_card_eq
      rw [hn]
      exact (by decide : Nat.Coprime 2 3).pow_left n
    rcases (Nat.dvd_prime Nat.prime_two).mp (hc.dvd_mul_right.mp hd) with hc | hc
    · exact (hSne (card_eq_one.mp hc)).elim
    · exact hc
  have hPk : IsPGroup 2 (P.subgroupOf J ⊓ f.ker : Subgroup J) := by
    rw [hker]
    exact pCore_isPGroup.to_le inf_le_right
  have hPimage : (P.subgroupOf J).map f = ⊤ := by
    change ((R ⊔ S).subgroupOf J).map f = ⊤
    rw [subgroupOf_sup hRJ hSJ]
    exact permThree_join_image_eq_top f _ _ hRc hSc
  obtain ⟨hQ,⟨eP⟩⟩ := product_twoCore_of_permThree f (P.subgroupOf J) hPimage hPk
  have hQambient : P.pCoreIn 2 = P ⊓ J.pCoreIn 2 := by
    have hm := congrArg (Subgroup.map J.subtype) hQ
    rw [map_pCoreIn_of_injective 2 _ J.subtype J.subtype_injective,
      map_subgroupOf_eq_of_le hPJ,Subgroup.map_inf _ _ _ J.subtype_injective,
      map_subgroupOf_eq_of_le hPJ,hker] at hm
    exact hm
  have hSP : Chapter1.IsSylowIn 2 S P := hSyl.restrict le_sup_right (sup_le hRI inf_le_right)
  have hQS : P.pCoreIn 2 ≤ S := by
    obtain ⟨SP,hSP⟩ := hSP
    exact hSP ▸ pCoreIn_le_sylow P SP
  have hQSJ : P.pCoreIn 2 = S ⊓ J.pCoreIn 2 := by
    apply le_antisymm (le_inf hQS (hQambient.le.trans inf_le_right))
    rw [hQambient]
    exact inf_le_inf_right _ le_sup_right
  let ep := (subgroupOfEquivOfLe hPJ).symm
  let epq := ep.toMonoidHom.pCoreQuotientEquiv (p := 2) ep.surjective
    (IsPGroup.ker_isPGroup_of_injective ep.injective)
  obtain ⟨eR⟩ := cubic_image_core_quotient f (R.subgroupOf J) (by rw [hker]; exact pCore_isPGroup) hRc
  let er := (subgroupOfEquivOfLe hRJ).symm
  let erq := er.toMonoidHom.pCoreQuotientEquiv (p := 2) er.surjective
    (IsPGroup.ker_isPGroup_of_injective er.injective)
  exact ⟨⟨epq.trans eP⟩,⟨erq.trans eR⟩,hQSJ⟩

open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06

/-- The first parabolic in original 14.6.6(6): its two-core and both quotient
models, together with the residual escaping the partner. These are also the
opening data of original 14.6.10. -/
theorem source_intersection_parabolic_data
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hunique : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (hab : IsMulCommutative (conjugateSpanBy (localModule T M) Mc))
    (H : Subgroup G) (hH : H ∈ Chapter1.HOutside G (T : Set G) (M : Set G))
    (u : G) (hu : u ∈ conjugateSpanBy (localModule T M) H)
    (hindex : (suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u).relIndex
        (T : Subgroup G) = 2)
    (hmove : ¬ Mc.pCoreIn 2 ≤ centralizer ({u} : Set G))
    (hproduct : ∀ t ∈ (T : Subgroup G), t ∉ suitableQuotientCentralizer
      (source_rankTwo_f9_hypothesis hG T hempty hM hunique hmany hcard e hab H hH) u →
        ¬ Mc.pCoreIn 2 ≤ centralizer ({u * (MulAut.conj t⁻¹) u} : Set G))
    (I : Subgroup G)
    (hTuI : (T : Subgroup G) ⊓ centralizer ({u} : Set G) ≤ I)
    (hSyl : Chapter1.IsSylowIn 2 ((T : Subgroup G) ⊓ I) I)
    (hcover : (sourceResidual M Mc : Set G) =
      ((pResidual 2 (sourceResidual M Mc ⊓ I : Subgroup G)).map
        (sourceResidual M Mc ⊓ I).subtype : Set G) *
          ((sourceResidual M Mc).pCoreIn 2 : Set G)) :
    let L := sourceResidual M Mc
    let R := (pResidual 2 (L ⊓ I : Subgroup G)).map (L ⊓ I).subtype
    let P := R ⊔ ((T : Subgroup G) ⊓ I)
    Nonempty ((P ⧸ pCore 2 P) ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty ((R ⧸ pCore 2 R) ≃* Multiplicative (ZMod 3)) ∧
      P.pCoreIn 2 = ((T : Subgroup G) ⊓ I) ⊓ (L ⊔ (T : Subgroup G)).pCoreIn 2 ∧
      ¬ R ≤ Mc := by
  have hTMc : (T : Subgroup G) ≤ Mc := by
    intro t ht
    apply (show Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) from
      hunique ▸ Set.mem_singleton Mc).2
    intro z hz
    exact (centralInvolutions_le_centralizer_sylow T hz t ht).symm
  have hQT : Mc.pCoreIn 2 ≤ (T : Subgroup G) := by
    simpa only [Sylow.coe_subtype,map_subgroupOf_eq_of_le hTMc] using
      pCoreIn_le_sylow Mc (T.subtype hTMc)
  have hc := (source_suitable_core_and_residual hG T hempty hM hunique hmany hcard e hab H hH u hu
    hindex hmove hproduct).2.1
  have hmoveI : ¬ (T : Subgroup G) ⊓ I ≤ centralizer (rankTwoSeed T M : Set G) := by
    rw [Section02.rankTwoSeed_eq_localModule]
    intro hh
    apply hc
    intro q hq
    exact ⟨hq.1,hh ⟨hQT hq.1,hTuI ⟨hQT hq.1,hq.2⟩⟩⟩
  have hd := rankTwo_intersection_parabolic
    (Section02.source_lemma_14_2_4 hG T hempty hM hunique hmany hcard e) I hSyl hmoveI hcover
  refine ⟨hd.1,hd.2.1,hd.2.2,?_⟩
  obtain ⟨_,_,_,_,_,hcore,huniqLT,_,_,_,_,_,_,_,hfam⟩ :=
    source_lemma_14_1_18 hG T hempty hM hunique hmany hcard e
  have hCMc := InitialSource.localModule_centralizer_le_partner T M hunique
  have hMcmax : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hunique ▸ Set.mem_singleton Mc
  intro hR
  have hLMc : sourceResidual M Mc ≤ Mc := by
    intro x hx
    have hx' : x ∈ (sourceResidual M Mc : Set G) := hx
    rw [hcover] at hx'
    obtain ⟨r,hr,q,hq,rfl⟩ := Set.mem_mul.mp hx'
    exact Mc.mul_mem (hR hr) (hCMc ((hcore.le hq).2))
  have hmem : Mc ∈ maximalTwoLocalOvergroups (sourceResidual M Mc ⊔ (T : Subgroup G)) :=
    ⟨hMcmax.1,sup_le hLMc hTMc⟩
  have he : Mc = M := Set.mem_singleton_iff.mp (huniqLT ▸ hmem)
  have honly : maximalTwoLocalOvergroups (T : Subgroup G) = {M} := by
    simpa [he] using hfam
  rw [honly,Set.ncard_singleton] at hmany
  omega

end CFSG.Quasithin.Chapter14.Section06
