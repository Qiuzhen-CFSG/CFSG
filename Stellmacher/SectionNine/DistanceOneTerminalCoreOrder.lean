module

public import Stellmacher.SectionNine.DistanceOneReduction
public import Stellmacher.SectionNine.DistanceOneVstarContainments
public import Stellmacher.SectionThree.PrimitiveKleinSylowExclusion
public import Theory.GroupTheory.QuaternionFixedEight
public import Theory.GroupTheory.QuaternionCentralProductFactors
public import Theory.GroupTheory.InnerRestrictionsCommutingSup
public import Theory.GroupTheory.SubgroupConjugation
public import Theory.GroupTheory.PGroup.CyclicInvolution
public import Mathlib.Tactic.IntervalCases


/-!
# The terminal core has order64

In the actual distance-one local context, assume the distinguished Sylow has
order128 and contains a quaternion central product V inside the terminal
core. The actual seed Z_a intersect Q_d is an elementary eight contained in V.
Then Q_d has order64. No local conclusion, terminal quotient model, or global
normality of the extracted V is assumed.

The core is a proper subgroup of the Sylow and contains V of order32, so its
order is32 or64. In the first case it equals V, hence is normal in the terminal
stabilizer and self-centralizing there by characteristic two. An element of
Z_a outside the core fixes the elementary seed pointwise. Such an actor cannot
be a square modulo V: squares preserve both intrinsic quaternion factors,
while preserving both factors and fixing the seed would make its restrictions
inner. Combining the inner actors would put it inside V, a contradiction.

The actual terminal Sylow quotient has order4 in this case. The outside
involution which is not a square makes it elementary abelian. Solvability,
trivial two-core, and the exact unique-maximal-over-Sylow property pass to the
actual core quotient. The primitive Klein-four exclusion rules out this case.

Source: the local calculation after Stellmacher(9.1), relation(11), Journal
of Algebra190 (1997), p.48. This theorem supplies a missing order calculation
before identifying the terminal quotient and the exact conjugate closure.
-/

namespace Stellmacher.SectionNine
open Stellmacher.Later Stellmacher.SectionsFiveToSeven Subgroup

private theorem actor_not_square_mod_quaternion_product
    {G : Type*} [Group G] [Finite G]
    (B C U : Subgroup G)
    (hB : Nonempty (B ≃* QuaternionGroup 2))
    (hC : Nonempty (C ≃* QuaternionGroup 2))
    (hinter : Nat.card (B ⊓ C : Subgroup G) = 2)
    (hcomm : ∀ b ∈ B, ∀ c ∈ C, b*c=c*b)
    (hVcard : Nat.card (B ⊔ C : Subgroup G) = 32)
    (N : Subgroup G) (hVN : B ⊔ C ≤ N)
    (hVnormal : N ≤ normalizer ((B ⊔ C : Subgroup G) : Set G))
    (hself : N ⊓ centralizer ((B ⊔ C : Subgroup G) : Set G) ≤ B ⊔ C)
    (hU : U ≤ B ⊔ C) (hUcard : Nat.card U=8)
    (hUexp : ∀u∈U,u^2=1)
    (a : G) (haN : a ∈ N) (ha : a ∉ B ⊔ C) (hfix : ∀u∈U,Commute a u) :
    ∀ t ∈ N, a⁻¹*t^2 ∉ B ⊔ C := by
  have hnormB : B ⊔ C ≤ normalizer (B : Set G) := by
    apply sup_le B.le_normalizer
    exact (show C ≤ centralizer (B : Set G) from fun c hc b hb => hcomm b hb c hc).trans
      (Subgroup.centralizer_le_normalizer _)
  have hnormC : B ⊔ C ≤ normalizer (C : Set G) := by
    apply sup_le ?_ C.le_normalizer
    exact (show B ≤ centralizer (C : Set G) from fun b hb c hc => (hcomm b hb c hc).symm).trans
      (Subgroup.centralizer_le_normalizer _)
  have hnot : ¬ (a∈normalizer (B : Set G) ∧ a∈normalizer (C : Set G)) := by
    rintro ⟨haB,haC⟩
    have hb := Subgroup.factor_inner_of_fixed_eight B C U hB hC hcomm hVcard hU hUcard hUexp a haB haC hfix
    have hc := Subgroup.factor_inner_of_fixed_eight C B U hC hB
      (fun c hc b hb => (hcomm b hb c hc).symm) (by simpa [sup_comm] using hVcard)
      (by simpa [sup_comm] using hU) hUcard hUexp a haC haB hfix
    obtain ⟨v,hv,hva⟩ := Subgroup.exists_mul_inv_mem_centralizer_of_inner_restrictions B C hcomm a hb hc
    have hkN : v⁻¹*a ∈ N := N.mul_mem (N.inv_mem (hVN hv)) haN
    exact ha (by simpa using (B ⊔ C).mul_mem hv (hself ⟨hkN,hva⟩))
  intro t htN ht
  have hjoin : (B ⊔ C).map (MulAut.conj t).toMonoidHom = B ⊔ C :=
    mem_normalizer_iff_map_conj_eq.mp (hVnormal htN)
  have hsquares := quaternion_factors_invariant_of_square B C hB hC hinter hcomm
    (MulAut.conj t) hjoin
  have htB : t^2 ∈ normalizer (B : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change B.conjBy (t^2) = B
    rw [pow_two,conjBy_mul]
    exact hsquares.1
  have htC : t^2 ∈ normalizer (C : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change C.conjBy (t^2) = C
    rw [pow_two,conjBy_mul]
    exact hsquares.2
  apply hnot
  constructor
  · have hh := (normalizer (B : Set G)).mul_mem htB
      ((normalizer (B : Set G)).inv_mem (hnormB ht))
    simpa using hh
  · have hh := (normalizer (C : Set G)).mul_mem htC
      ((normalizer (C : Set G)).inv_mem (hnormC ht))
    simpa using hh

private theorem elementary_four_of_involution_not_square
    {G : Type*} [Group G] [Finite G] (hcard : Nat.card G=4)
    (a:G) (ha : a≠1) (ha2:a^2=1) (hnot:∀t:G,t^2≠a) : IsElementaryAbelian 2 G := by
  have hpow (t:G) : t^2=1 := by
    have hd : orderOf t ∣ 4 := hcard ▸ orderOf_dvd_natCard t
    have hpos : 0 < orderOf t := orderOf_pos t
    have hle : orderOf t ≤ 4 := Nat.le_of_dvd (by decide) hd
    interval_cases h : orderOf t
    · exact (orderOf_dvd_iff_pow_eq_one).mp (by rw [h]; decide)
    · exact (orderOf_dvd_iff_pow_eq_one).mp (by rw [h])
    · norm_num at hd
    · have hgen : Subgroup.zpowers t = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [Nat.card_zpowers,h,hcard]
      let _ : IsCyclic G := isCyclic_of_surjective
        (Subgroup.zpowers t).subtype (by
          intro x
          exact ⟨⟨x,by rw [hgen]; trivial⟩,rfl⟩)
      have ht2 : orderOf (t^2)=2 := by rw [orderOf_pow, h]; decide
      exact (hnot t (IsCyclic.eq_of_orderOf_eq_two ht2 (orderOf_eq_prime ha2 ha))).elim
  exact { toIsMulCommutative := ⟨⟨by
              intro x y
              have hx := hpow x
              have hy := hpow y
              have hxy := hpow (x*y)
              have hxi : x⁻¹=x := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hx)
              have hyi : y⁻¹=y := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hy)
              have hi : (x*y)⁻¹=x*y := inv_eq_of_mul_eq_one_left (by simpa [pow_two] using hxy)
              simpa [mul_inv_rev,hxi,hyi] using hi.symm⟩⟩
          exponent_dvd_p := Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpow }


public theorem distance_one_terminal_core_card_of_quaternion_product
    {G : Type*} [Group G] [Finite G] {T A B : Subgroup G}
    (ctx : SectionNineLocalContext G T A B) (hb : ctx.criticalPath.length=1)
    (hTcard : Nat.card T=128) (V : Subgroup G) (hVmodel : IsCentralProductQ8Q8 V)
    (hVQ : V ≤ QAt ctx.Γ ctx.criticalPath.a')
    (hseedV : ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a' ≤ V)
    (hseedcard : Nat.card (ZAt ctx.Γ ctx.criticalPath.a ⊓ QAt ctx.Γ ctx.criticalPath.a' : Subgroup G)=8) :
    Nat.card (QAt ctx.Γ ctx.criticalPath.a')=64 := by
  classical
  let Q := QAt ctx.Γ ctx.criticalPath.a'
  let terminal := GAt ctx.Γ ctx.criticalPath.a'
  let Za := ZAt ctx.Γ ctx.criticalPath.a
  let seed := Za ⊓ Q
  change V ≤ Q at hVQ
  change seed ≤ V at hseedV
  change Nat.card seed=8 at hseedcard
  have hend : ctx.criticalPath.a' = ctx.criticalPath.firstStep := by
    rw [← ctx.criticalPath.path_end, ← ctx.criticalPath.path_first]
    congr 1
    exact Fin.ext hb
  have hQT : Q ≤ T := by
    change QAt ctx.Γ ctx.criticalPath.a' ≤ T
    rw [hend]
    exact (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).2
  obtain ⟨hTB,P,hP⟩ := by
    have h := (SevenSix.edge_sylow_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
    rw [← hend] at h
    exact h
  change T ≤ terminal at hTB
  have hQterm : Q ≤ terminal := hQT.trans hTB
  have hVterm : V ≤ terminal := hVQ.trans hQterm
  obtain ⟨L,R,hL,hR,hjoin,hI,hcomm,_⟩ := hVmodel
  have hLcard : Nat.card L=8 := by
    rw [Nat.card_congr hL.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hRcard : Nat.card R=8 := by
    rw [Nat.card_congr hR.some.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hRnL : R ≤ normalizer (L : Set G) :=
    (show R ≤ centralizer (L : Set G) from fun r hr l hl => hcomm l hl r hr).trans
      (Subgroup.centralizer_le_normalizer _)
  have hVcard : Nat.card V=32 := by
    have h := card_mul_eq_card_inf_mul_card_sup_of_normalizes L R hRnL
    rw [hLcard,hRcard,hI,← hjoin] at h
    omega
  have hQneT : Q ≠ T := by
    have h := (SevenSix.edge_local_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2.1.1.2.2.2
    rw [← hend] at h
    change T ≠ twoCoreIn terminal at h
    have heq : Q=twoCoreIn terminal := by
      change ctx.Γ.twoCoreAt ctx.criticalPath.a'=twoCoreIn terminal
      rw [ctx.Γ.twoCoreAt_def]
      rfl
    exact fun hQT => h (hQT.symm.trans heq)
  have hidxpos : 0 < V.relIndex Q := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H:=V.subgroupOf Q))
  have hQidx : 2 ≤ Q.relIndex T := by
    have hp : 0 < Q.relIndex T := Nat.pos_of_ne_zero (index_ne_zero_of_finite (H:=Q.subgroupOf T))
    have hn : Q.relIndex T≠1 := fun hh => hQneT (le_antisymm hQT (relIndex_eq_one.mp hh))
    omega
  have hVTidx : V.relIndex T=4 := by
    have h := relIndex_mul_relIndex (⊥ : Subgroup G) V T bot_le (hVQ.trans hQT)
    simp only [relIndex_bot_left] at h
    rw [hVcard,hTcard] at h
    omega
  have hprod := relIndex_mul_relIndex V Q T hVQ hQT
  rw [hVTidx] at hprod
  have hVidx : V.relIndex Q=1 ∨ V.relIndex Q=2 := by
    have hh : V.relIndex Q≤2 := by nlinarith
    omega
  rcases hVidx with hVidx | hVidx
  swap
  · have h := relIndex_mul_relIndex (⊥ : Subgroup G) V Q bot_le hVQ
    simp only [relIndex_bot_left] at h
    rw [hVcard,hVidx] at h
    exact h.symm
  have hQV : Q=V := le_antisymm (relIndex_eq_one.mp hVidx) hVQ
  have hQcard : Nat.card Q=32 := hQV ▸ hVcard
  have hchar : IsCharacteristicTwoType terminal := by
    have h := (SevenSix.edge_characteristic_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2
    rw [← hend] at h
    exact h
  have hQnative : (pCore 2 terminal).map terminal.subtype=Q := by
    change (pCore 2 terminal).map terminal.subtype=ctx.Γ.twoCoreAt ctx.criticalPath.a'
    rw [ctx.Γ.twoCoreAt_def]
    rfl
  have hself : terminal ⊓ centralizer (V : Set G) ≤ V := by
    intro c hc
    have hc' : (⟨c,hc.1⟩ : terminal) ∈ centralizer (pCore 2 terminal : Set terminal) := by
      intro x hx
      apply Subtype.ext
      exact hc.2 x (hQV ▸ (hQnative ▸ mem_map_of_mem terminal.subtype hx))
    exact hQV ▸ (hQnative ▸ mem_map_of_mem terminal.subtype (hchar hc'))
  have hVnorm : terminal ≤ normalizer (V : Set G) := by
    rw [← hQV]
    exact SevenSix.stabilizer_le_normalizer_q ctx.Γ ctx.criticalPath.a'
  have hn : ctx.criticalPath.a' ∈ CosetGraphContext.neighborhood ctx.Γ ctx.criticalPath.a := by
    rw [CosetGraphContext.neighborhood,ctx.Γ.neighbors_def]
    exact (ctx.Γ.distance_symm _ _).trans (ctx.criticalPath.endpoint_distance.trans hb)
  let _ : IsElementaryAbelian 2 (ZAt ctx.Γ ctx.criticalPath.a) := SevenSix.z_isElementaryAbelian_of_neighbor ctx.sectionSeven ctx.Γ hn
  have hZaT : Za ≤ T := by
    have hZaQ := ((lemma_seven_three ctx.sectionSeven ctx.Γ).center_core _ _ hn).trans
      ((SevenSix.omegaOneCenter_le_centerAmbient _).trans (map_subtype_le _))
    exact hZaQ.trans (SevenSix.local_cores_le_edge_sylow ctx.sectionSeven ctx.Γ ctx.criticalPath).1
  obtain ⟨a,haZa,haQ⟩ := SetLike.not_le_iff_exists.mp ctx.criticalPath.critical.2
  have haT : a∈T := hZaT haZa
  have ha2 : a^2=1 := elemPow_eq_one_of_isElementaryAbelian a
    (show a∈ZAt ctx.Γ ctx.criticalPath.a from haZa)
  have hnonsquare := actor_not_square_mod_quaternion_product L R seed hL hR hI hcomm
    (hjoin ▸ hVcard) terminal (hjoin ▸ hVterm) (hjoin ▸ hVnorm) (hjoin ▸ hself)
    (hjoin ▸ hseedV) hseedcard (fun u hu => elemPow_eq_one_of_isElementaryAbelian u hu.1)
    a (hTB haT) (hjoin ▸ hQV ▸ haQ)
    (fun u hu => setLike_mul_comm (s:=Za) haZa hu.1)
  let q : terminal →* terminal ⧸ pCore 2 terminal := QuotientGroup.mk' (pCore 2 terminal)
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hqker : q.ker=Q.subgroupOf terminal := by
    rw [QuotientGroup.ker_mk']
    apply map_injective terminal.subtype_injective
    rw [hQnative,map_subgroupOf_eq_of_le hQterm]
  have hPnative : (P : Subgroup terminal)=T.subgroupOf terminal := by
    apply map_injective terminal.subtype_injective
    rw [map_subgroupOf_eq_of_le hTB]
    exact hP
  let Pbar := P.mapSurjective hq
  have hPcard : Nat.card P=128 := by
    exact (card_map_of_injective (K:=(P:Subgroup terminal)) terminal.subtype_injective).symm.trans
      ((congrArg (fun K : Subgroup G => Nat.card K) hP).trans hTcard)
  have hkP : q.ker ≤ (P : Subgroup terminal) := by
    rw [hqker,hPnative]
    exact subgroupOf_mono terminal hQT
  have hkcard : Nat.card q.ker=32 := by
    rw [hqker, Nat.card_congr (subgroupOfEquivOfLe hQterm).toEquiv]
    exact hQcard
  have hPbarcard : Nat.card Pbar=4 := by
    have h := relIndex_mul_relIndex (⊥ : Subgroup terminal) q.ker (P : Subgroup terminal) bot_le hkP
    simp only [relIndex_bot_left,relIndex_ker] at h
    rw [hkcard,hPcard] at h
    change 32 * Nat.card Pbar=128 at h
    omega
  let an : terminal := ⟨a,hTB haT⟩
  have haP : an∈(P:Subgroup terminal) := by rw [hPnative]; exact haT
  let abar : Pbar := ⟨q an,mem_map_of_mem q haP⟩
  have habarne : abar≠1 := by
    intro hh
    have hk : an∈q.ker := congrArg Subtype.val hh
    rw [hqker] at hk
    exact haQ hk
  have habar2 : abar^2=1 := by
    apply Subtype.ext
    change q an ^2=1
    rw [← map_pow,show an^2=1 from Subtype.ext ha2,map_one]
  have habarsquare : ∀t:Pbar,t^2≠abar := by
    intro t ht
    obtain ⟨t0,ht0,heq⟩ := t.property
    have hker : an⁻¹*t0^2∈q.ker := by
      change q (an⁻¹*t0^2)=1
      simp only [map_mul,map_inv,map_pow]
      have hh : (q t0)^2=q an := by
        have hh := congrArg Subtype.val ht
        change (t.val)^2=q an at hh
        rwa [← heq] at hh
      rw [hh,inv_mul_cancel]
    rw [hqker] at hker
    exact hnonsquare t0 t0.property (hjoin ▸ hQV ▸ hker)
  let _ : IsElementaryAbelian 2 Pbar := elementary_four_of_involution_not_square hPbarcard abar habarne habar2 habarsquare
  obtain ⟨M,hM,hTM,huniq⟩ := by
    have h := (SevenSix.edge_local_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2.1.2.2
    rw [← hend] at h
    exact h
  have hPM : (P : Subgroup terminal) ≤ M := by rwa [hPnative]
  have hkM : q.ker ≤ M := hkP.trans hPM
  have hMproper : M.map q≠⊤ := by
    intro heq
    have hh := comap_map_eq q M
    rw [heq,comap_top,sup_eq_left.mpr hkM] at hh
    exact hM.ne_top hh.symm
  obtain ⟨Mbar,hMbar,hMMbar⟩ := (eq_top_or_exists_le_coatom (M.map q)).resolve_left hMproper
  have hPbarM : (Pbar : Subgroup _) ≤ Mbar := (map_mono hPM).trans hMMbar
  have huniqbar : ∀N:Subgroup (terminal ⧸ pCore 2 terminal),IsCoatom N→
      (Pbar:Subgroup _)≤N→N=Mbar := by
    intro N hN hPN
    apply comap_injective hq
    have hm (K : Subgroup (terminal ⧸ pCore 2 terminal)) (hK:IsCoatom K)
        (hPK:(Pbar:Subgroup _)≤K) : K.comap q=M := by
      apply huniq _ (isCoatom_comap_of_surjective hq hK)
      intro t ht
      have htP : t∈(P:Subgroup terminal) := hPnative.symm ▸ ht
      exact hPK (mem_map_of_mem q htP)
    exact (hm N hN hPN).trans (hm Mbar hMbar hPbarM).symm
  have hcorebar : pCore 2 (terminal ⧸ pCore 2 terminal)=⊥ := by
    have h := pCore_map_mk'_eq_of_normal_isPGroup (G:=terminal) (p:=2)
      (pCore 2 terminal) (pCore_isPGroup (G:=terminal) (p:=2))
    have hh : (pCore 2 terminal).map q=⊥ := by
      apply (Subgroup.map_eq_bot_iff (f:=q) (H:=pCore 2 terminal)).mpr
      rw [QuotientGroup.ker_mk']
    exact h.symm.trans hh
  have hsolv : Group.IsSolvable terminal := by
    have h := (SevenSix.edge_local_data ctx.sectionSeven ctx.Γ ctx.criticalPath).2.2
    rw [← hend] at h
    exact h
  let _ := hsolv
  exact (SectionThree.not_elementary_four_sylow_of_unique_maximal inferInstance hcorebar
    Pbar inferInstance hPbarcard Mbar hMbar hPbarM huniqbar).elim
end Stellmacher.SectionNine
