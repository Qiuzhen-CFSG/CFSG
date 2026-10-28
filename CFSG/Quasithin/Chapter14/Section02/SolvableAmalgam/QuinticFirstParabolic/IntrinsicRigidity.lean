module
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic.IntrinsicCentralizer
public import CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.ReeLocal.ResidualRigidity.LinearResidual
public import Theory.GroupTheory.FiveFrattiniCoreOvergroup
public import Theory.Frattini.OmegaProducts

/-!
# Intrinsic rigidity of the original order-512 quintic core

An upper bound on O₂(H) gives its derived, Frattini and second-central
layers from `IntrinsicCore`. The faithful five-action on its Frattini
quotient, together with the central quotient chain, proves that the
actual ambient core O₂(Mc) is O₂(H).

Conjugation on the common core's Frattini quotient then embeds Mc/O₂(Mc)
in GL₄(2). Its Sylow two-subgroup is cyclic of order four, inherited from
the known Sz(2) quotient of H. A larger odd residual would be cyclic of
order fifteen. The original core's invariant third commutator excludes
that automorphism, so |Mc/O₂(Mc)|≤20 and H=Mc.

The consumer constructs the full involution centralizer's intrinsic
Parrott hypotheses with no assumed H=Mc or first-parabolic equivalence.
Only |O₂(H)|≤512 remains an additional source premise; its unconditional
proof and final assembly stay with qt-e-quintic-first-parabolic.

Source: Aschbacher--Smith 14.2.21, printed pp.988--989, and Parrott (1972),
Lemma 1, printed p.672. The quotient actions use the literal core maps.
-/

public section
open Subgroup Stellmacher Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
private theorem frattini_no_fifteen_of_equiv
    {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hno : ∀ a : MulAut A, orderOf (quotientAut (frattini A) a) ≠ 15)
    (b : MulAut B) : orderOf (quotientAut (frattini B) b) ≠ 15 := by
  let eV := QuotientGroup.congr (frattini A) (frattini B) e (frattini_map_equiv e)
  have he : MulAut.congr eV (quotientAut (frattini A) (MulAut.congr e.symm b)) =
      quotientAut (frattini B) b := by
    ext v
    obtain ⟨x,rfl⟩ := QuotientGroup.mk'_surjective (frattini B) v
    obtain ⟨x,rfl⟩ := e.surjective x
    have hmk : QuotientGroup.mk' (frattini B) (e x) =
        eV (QuotientGroup.mk' (frattini A) x) := rfl
    rw [hmk, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, eV.symm_apply_apply, quotientAut_apply_mk]
    change QuotientGroup.mk' (frattini B) (e (e.symm (b (e x)))) =
      quotientAut (frattini B) b (QuotientGroup.mk' (frattini B) (e x))
    rw [e.apply_symm_apply, quotientAut_apply_mk]
  have ho := (MulAut.congr eV).orderOf_eq
    (quotientAut (frattini A) (MulAut.congr e.symm b))
  rw [he] at ho
  exact ho ▸ hno (MulAut.congr e.symm b)
private theorem sylow_bound {A B : Type*} [Group A] [Finite A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (S : Sylow 2 B) (hS : (S : Subgroup B) ≤ f.range)
    (hA : Nat.card A = 20) (hcyc : ∀ T : Sylow 2 A, IsCyclic T) :
    IsCyclic S ∧ Nat.card S ≤ 4 := by
  let T := S.comapOfInjective f hf hS
  let φ : T →* S := (f.comp T.toSubgroup.subtype).codRestrict S (fun x => x.property)
  have hφ : Function.Bijective φ := by
    constructor
    · intro x y h
      exact Subtype.ext (hf (congrArg Subtype.val h))
    · intro s
      obtain ⟨a, ha⟩ := hS s.property
      refine ⟨⟨a, ?_⟩, Subtype.ext ha⟩
      change f a ∈ S
      rw [ha]
      exact s.property
  let e := MulEquiv.ofBijective φ hφ
  have hcard : Nat.card S = Nat.card T := (Nat.card_congr e.toEquiv).symm
  let := hcyc T
  refine ⟨isCyclic_of_surjective φ hφ.2, ?_⟩
  rw [hcard]
  obtain ⟨n, hn⟩ := T.isPGroup'.exists_card_eq
  have hnle : n ≤ 2 := by
    by_contra h
    have hd : 8 ∣ 20 := by
      rw [← hA]
      exact (hn ▸ Nat.pow_dvd_pow 2 (show 3 ≤ n by omega)).trans T.toSubgroup.card_subgroup_dvd_card
    norm_num at hd
  rw [hn]
  exact Nat.pow_le_pow_right (by decide) hnle


private theorem card_le_twenty_of_no_fifteen
    {A V : Type*} [Group A] [Finite A] [Group V] [Finite V] [IsElementaryAbelian 2 V]
    (T : Sylow 2 A) (hT : IsCyclic T) (hTc : Nat.card T ≤ 4)
    (ρ : A →* MulAut V) (hρ : Function.Injective ρ) (hV : Nat.card V = 16)
    (hfive : 5 ∣ Nat.card A) (hno : ∀ a : A, orderOf a ≠ 15) : Nat.card A ≤ 20 := by
  let R := pResidual 2 A
  have hp : IsPGroup 2 (A ⧸ R) := isPGroup_quotient_pResidual 2
  have hc : Nat.card R * Nat.card (A ⧸ R) = Nat.card A := R.card_mul_index
  have h5 : 5 ∣ Nat.card R := by
    rw [← hc] at hfive
    rcases (by decide : Nat.Prime 5).dvd_mul.mp hfive with h | h
    · exact h
    · obtain ⟨n, hn⟩ := hp.exists_card_eq
      rw [hn] at h
      have := (by decide : Nat.Prime 5).dvd_of_dvd_pow h
      norm_num at this
  have hRc : Nat.card R ≤ 5 := by
    let : Fact (Nat.Prime 5) := ⟨by decide⟩
    obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := R) 5 h5
    let K := zpowers a
    have hK : Nat.card K = 5 := (Nat.card_zpowers a).trans ha
    by_cases htop : K = ⊤
    · simpa only [htop, card_top] using hK.le
    · obtain ⟨hR,hcyc,_⟩ := ReeLocal.ResidualRigidity.cyclic_fifteen_regular
        T hT ρ hρ hV K hK (lt_top_iff_ne_top.mpr htop)
      let := hcyc
      obtain ⟨r,hr⟩ := isCyclic_iff_exists_zpowers_eq_top.mp hcyc
      have ho : orderOf (r : A) = 15 := by
        rw [orderOf_coe, orderOf_eq_card_of_zpowers_eq_top hr, hR]
      exact (hno r ho).elim
  have hindex : Nat.card (A ⧸ R) ≤ Nat.card T := by
    let U := T.mapSurjective (QuotientGroup.mk'_surjective R)
    have hU : (U : Subgroup (A ⧸ R)) = ⊤ :=
      (U.is_maximal' (hp.to_subgroup ⊤) le_top).symm
    let f := (QuotientGroup.mk' R).comp T.toSubgroup.subtype
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨x, hx, he⟩ := hU.ge (mem_top y)
      exact ⟨⟨x, hx⟩, he⟩
    exact Nat.card_le_card_of_surjective f hf
  nlinarith
variable {G : Type*} [Group G] [Finite G]

/-- The actual cores of H and its full involution centralizer agree under
only the original core bound. The argument uses the original five-action,
the intrinsic Frattini layer and the central quotient chain. -/
theorem source_core512_ambient_core
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    Mc.pCoreIn 2 = H.pCoreIn 2 := by
  let P := pCore 2 H
  let Q := H.pCoreIn 2
  let q : P ≃* Q := equivMapOfInjective P H.subtype H.subtype_injective
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,_,hMc,_⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  have hHMc : H ≤ Mc := hMc ▸
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hTMc := hH.1.1.2.trans hHMc
  have hMcMem : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hcMc : centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T)
      ⟨Chapter1.mem_H_of_isTwoLocal hMcMem.1.1,hTMc⟩)
  have hcH : centralizer (P : Set H) ≤ P :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T) hH.1.1)
  let i : H →* Mc := inclusion hHMc
  have hzcenter : (center P).map (i.comp P.subtype) ≤ center Mc := by
    rintro _ ⟨z,hz,rfl⟩
    have hzq : q z ∈ center Q := by
      rw [mem_center_iff]
      intro y
      obtain ⟨x,rfl⟩ := q.surjective y
      simpa only [map_mul] using congrArg q (mem_center_iff.mp hz x)
    have hzZ : (z : H).val ∈ centralInvolutions T := by
      rw [← source_core512_core_center hG T hempty hM hu hmany hcard e H hH hi hQupper]
      exact mem_map_of_mem Q.subtype hzq
    rw [mem_center_iff]
    intro y
    apply Subtype.ext
    exact (mem_centralizer_iff.mp (hMc.le y.property) _ hzZ).symm
  obtain ⟨_,hPhi,hUpper,hV⟩ := source_core512_characteristic_layers
    hG T hempty hM hu hmany hcard e H hH hi hQupper
  have hPhiQ : frattini Q = Subgroup.upperCentralSeries Q 2 := by
    apply map_injective Q.subtype_injective
    exact hPhi.trans hUpper.symm
  have hPhiP : frattini P ≤ Subgroup.upperCentralSeries P 2 := by
    rw [← Subgroup.comap_upperCentralSeries q 2, ← hPhiQ]
    exact frattini_le_comap_frattini_of_surjective q.surjective
  have hVP : Nat.card (P ⧸ frattini P) = 16 :=
    (Nat.card_congr (QuotientGroup.congr _ _ q (frattini_map_equiv q)).toEquiv).trans hV
  obtain ⟨hmodel,_,_,_⟩ := source_core512_orders hG T hempty hM hu hmany hcard e H hH hi hQupper
  have hfive : 5 ∣ Nat.card (H ⧸ P) := by
    rw [(Nat.card_congr hmodel.some.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card]
    decide
  have hh := core_eq_of_five_frattini_second_center i (inclusion_injective hHMc)
    (T.subtype hTMc) (by
      intro t ht
      exact ⟨⟨t,hH.1.1.2 ht⟩,rfl⟩) hcH hcMc hzcenter hPhiP hVP hfive
  change (pCore 2 Mc).map Mc.subtype = P.map H.subtype
  rw [hh,map_map]
  rfl

/-- The core bound forces H to fill the full centralizer. A larger quotient
would have an odd residual of order fifteen, forbidden by the original
core's nonzero third commutator. No endpoint equivalence is used. -/
theorem source_core512_eq_mc
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) : H = Mc := by
  have hZ := plane_centralInvolutions_card T M hM.1.2 hcard e
  obtain ⟨_,_,hMc,_⟩ := plane_ordering_and_overgroups hG T hempty hM hu hmany hcard hZ
  have hHMc : H ≤ Mc := hMc ▸
    (source_lemma_14_2_3 hG T hempty hM hu hmany hcard e H hH.1.1 hH.1.2).2
  have hTMc := hH.1.1.2.trans hHMc
  have hMcMem : Mc ∈ maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) :=
    hu ▸ Set.mem_singleton Mc
  have hcMc : centralizer (pCore 2 Mc : Set Mc) ≤ pCore 2 Mc :=
    Chapter1.mem_He_iff.mp (Chapter1.lemma_1_1_4_6 T (hG.evenCharacteristic T)
      ⟨Chapter1.mem_H_of_isTwoLocal hMcMem.1.1,hTMc⟩)
  have hcore := source_core512_ambient_core hG T hempty hM hu hmany hcard e H hH hi hQupper
  let P := pCore 2 H
  let J := pCore 2 Mc
  let Q := H.pCoreIn 2
  let q : J ≃* Q := (equivMapOfInjective J Mc.subtype Mc.subtype_injective).trans
    (MulEquiv.subgroupCongr hcore)
  obtain ⟨hmodel,hTcard,hPcard,_⟩ := source_core512_orders
    hG T hempty hM hu hmany hcard e H hH hi hQupper
  have hJcard : Nat.card J = 512 := (Nat.card_congr q.toEquiv).trans
    ((card_map_of_injective H.subtype_injective).trans hPcard)
  obtain ⟨_,_,_,hVQ⟩ := source_core512_characteristic_layers
    hG T hempty hM hu hmany hcard e H hH hi hQupper
  let V := J ⧸ frattini J
  let : Fact (IsPGroup 2 J) := ⟨pCore_isPGroup⟩
  let : IsElementaryAbelian 2 V := isElementaryAbelian_quotient_frattini (p := 2)
  have hV : Nat.card V = 16 :=
    (Nat.card_congr (QuotientGroup.congr _ _ q (frattini_map_equiv q)).toEquiv).trans hVQ
  have hnoJ (a : MulAut J) : orderOf (quotientAut (frattini J) a) ≠ 15 :=
    frattini_no_fifteen_of_equiv q.symm
      (source_core512_no_fifteen hG T hempty hM hu hmany hcard e H hH hi hQupper) a
  let action : Mc →* MulAut V := (quotientAut (frattini J)).comp
    (MulAut.conjNormal : Mc →* MulAut J)
  have hker : action.ker = J := pCore_frattini_action_kernel 2 hcMc
  let eqv := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivRange action)
  let ρ : Mc ⧸ J →* MulAut V := action.range.subtype.comp eqv.toMonoidHom
  have hρ : Function.Injective ρ := action.range.subtype_injective.comp eqv.injective
  have hno (a : Mc ⧸ J) : orderOf a ≠ 15 := by
    obtain ⟨a,rfl⟩ := QuotientGroup.mk'_surjective J a
    have ho := orderOf_injective ρ hρ (QuotientGroup.mk' J a)
    exact ho ▸ hnoJ (MulAut.conjNormal a)
  let i : H →* Mc := inclusion hHMc
  have hPmap : P.map i = J := by
    apply map_injective Mc.subtype_injective
    rw [map_map]
    change H.pCoreIn 2 = Mc.pCoreIn 2
    exact hcore.symm
  have hpre : J.comap i = P := by rw [←hPmap,comap_map_eq_self_of_injective (inclusion_injective hHMc)]
  let f := QuotientGroup.map P J i hpre.ge
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    rw [QuotientGroup.ker_map,hpre,QuotientGroup.map_mk'_self]
  have hHq : Nat.card (H ⧸ P) = 20 :=
    (Nat.card_congr hmodel.some.toEquiv).trans BenderSuzuki.MatrixGroups.suzukiZero_card
  have hHcyc (S : Sylow 2 (H ⧸ P)) : IsCyclic S := by
    let e20 := hmodel.some.trans
      Tits.ExceptionalParabolics.FirstQuotient.coreQuotientEquiv.symm
    let R := S.mapSurjective (f := e20.toMonoidHom) e20.surjective
    let := ReeTwo.ParabolicConcrete.tits_quotient_sylow_cyclic R
    let eS : S ≃* R := S.toSubgroup.equivMapOfInjective e20.toMonoidHom e20.injective
    exact isCyclic_of_injective eS.toMonoidHom eS.injective
  let S := (T.subtype hTMc).mapSurjective (QuotientGroup.mk'_surjective J)
  have hS : (S : Subgroup (Mc ⧸ J)) ≤ f.range := by
    rintro _ ⟨s,hs,rfl⟩
    exact ⟨QuotientGroup.mk' P ⟨s,hH.1.1.2 hs⟩,rfl⟩
  obtain ⟨hSc,hScard⟩ := sylow_bound f hf S hS hHq hHcyc
  have hfive : 5 ∣ Nat.card (Mc ⧸ J) := by
    have hd := card_dvd_of_injective f hf
    rw [hHq] at hd
    exact (by decide : 5 ∣ 20).trans hd
  have hbound := card_le_twenty_of_no_fifteen S hSc hScard ρ hρ hV hfive hno
  apply eq_of_le_of_card_ge hHMc
  have hMcCard := J.index_mul_card
  change Nat.card (Mc ⧸ J) * Nat.card J = Nat.card Mc at hMcCard
  rw [hJcard] at hMcCard
  have hHcard := P.index_mul_card
  change Nat.card (H ⧸ P) * Nat.card P = Nat.card H at hHcard
  rw [hHq,hPcard] at hHcard
  omega

/-- The full original centralizer satisfies Parrott's intrinsic hypotheses
under just the two-core upper bound; its equality with H is now proved. -/
theorem source_intrinsic_of_core_upper_bound
    (hG : IsSimpleQTKE KnownSimple.IsKnownSimple G)
    (T : Sylow 2 G) (hempty : MainForward.faithfulLocalComponents T = ∅)
    {M Mc : Subgroup G} (hM : IsOrderingMaximal T M)
    (hu : maximalTwoLocalOvergroups (centralizer (centralInvolutions T : Set G)) = {Mc})
    (hmany : 1 < (maximalTwoLocalOvergroups (T : Subgroup G)).ncard)
    (hcard : Nat.card (localModule T M) = 4)
    (e : (M ⧸ (centralizer (localModule T M : Set G)).subgroupOf M) ≃* Equiv.Perm (Fin 3))
    (H : Subgroup G) (hH : H ∈ Chapter3.HStar (T : Subgroup G) M)
    (hi : (T : Subgroup G).relIndex H = 5)
    (hQupper : Nat.card (pCore 2 H) ≤ 512) :
    ∃ z : G, zpowers z = centralInvolutions T ∧
      Recognition.ParrottCentralizerHypotheses z :=
  source_intrinsic_of_core_bound hG T hempty hM hu hmany hcard e H hH hi
    (source_core512_eq_mc hG T hempty hM hu hmany hcard e H hH hi hQupper) hQupper

end CFSG.Quasithin.Chapter14.Section02.SolvableAmalgam.QuinticFirstParabolic
