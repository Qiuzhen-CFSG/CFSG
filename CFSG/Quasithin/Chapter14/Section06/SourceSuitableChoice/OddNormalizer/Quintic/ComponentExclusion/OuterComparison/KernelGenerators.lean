module
public import Theory.GroupTheory.PrimeRankOneNormal
public import CFSG.Quasithin.Chapter14.Section06.SourceSuitableChoice.OddNormalizer.Quintic.ComponentExclusion.OuterComparison.Kernel

/-!
# Five-elements in the literal quotient-action kernel

At five-rank one, every five-element of the action kernel lies in K₂;
conversely the given five-generators of K₂ lie in that kernel. A kernel
five-element cannot lie in J because it would survive in the prime-to-five
center of J/O₂(J). Passing to N_G(K₂)/J now proves that every inner
five-actor lies in J K₂. Thus either K₁ is contained in J K₂ or an actual
first-factor generator acts outerly with order five.

This is a proved alternative, not an inference from K₁ not contained in J.
The final owner qt-e-14615-quintic-exclusion retains the remaining model
comparison and the construction of NormalizerGeometry. SourceComponent's
StarComparison applies these results to the extracted component and its
literal C.2.7 action.

Source: Aschbacher--Smith 14.6.15, printed p.1035; the ordinary-centralizer
convention issue recorded in docs/quasithin-proof-basis.md is not used.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
open SourcePreliminaries Chapter15.Section03 ChapterA.Section05To06
open Chapter15.Section03.AbelianAmalgam Chapter15.Section03.AbelianAmalgam.GenerationOne
open ComponentExclusion Chapter1.RadicalExclusions
open ModelReduction FullSieve FullSieve.SourceInterface
variable {G : Type*} [Group G] [Finite G]
variable {T : Sylow 2 G} {M Mc H H0 H1 H2 : Subgroup G}
    [IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H)]
    {a : LocalQuotientAction H (conjugateSpanBy (localModule T M) H) (centralInvolutions T)}
    (s : Context T M Mc H H0 H1 H2 a)
local instance : IsElementaryAbelian 2
    (ChapterF.Section09.Setup.UH
      ⟨T,sourceResidual M Mc,localModule T M,localModule T M,centralInvolutions T,H⟩) :=
  inferInstanceAs (IsElementaryAbelian 2 (conjugateSpanBy (localModule T M) H))
variable (d : NormalizerGeometry (T : Subgroup G) Mc H H1 H2
      (conjugateSpanBy (localModule T M) Mc) (centralInvolutions T)
      (firstSupport a H1) (firstSupport a H2) s.critical.endpoint.representative)
    (J : Subgroup G) (hJN : J ≤ normalizer (d.K2 : Set G))
    (hJ : (J.subgroupOf (normalizer (d.K2 : Set G))).IsCComponent)
    (hq : IsQuasisimple (J ⧸ pCore 2 J))
    (hout : ¬J ≤ Mc ⊓ normalizer (d.K2 : Set G))
    (hf : generalizedFitting J = pCore 2 J)

include hJN hJ hq hout hf in
/-- Every actual order-five element of the quotient-action kernel lies in K₂. -/
theorem component_quotient_kernel_prime_generator_mem_second (hr : primeRank 5 J = 1)
    {x : G} (hx : x ∈ pCoreActionKernelIn 2 J (normalizer (d.K2 : Set G)))
    (ho : orderOf x = 5) : x ∈ d.K2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let D := pCoreActionKernelIn 2 J (normalizer (d.K2 : Set G))
  let B := d.K2.subgroupOf D
  have hKD : d.K2 ≤ D := second_factor_le_component_quotient_kernel s d J hJN hJ hq hout
  have hB : 5 ∣ Nat.card B := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hKD).toEquiv]
    by_contra hn
    have hz := PrimeRank.eq_zero_iff_not_dvd_card.mpr hn
    have hp := second_quintic_rank_pos s d
    omega
  have hD : primeRank 5 D ≤ 1 :=
    (component_quotient_kernel_five_rank s d J hJN hJ hq hout hf hr).le
  let y : D := ⟨x,hx⟩
  have hy : orderOf y = 5 := (Subgroup.orderOf_coe y).symm.trans ho
  have hn : y ∈ normalizer (B : Set D) :=
    le_normalizer_comap D.subtype (show y ∈ (normalizer (d.K2 : Set G)).comap D.subtype
      from hx.1)
  exact mem_of_prime_order_normalizes_of_rank_one B hB hD y hy hn

include hJN hJ hq hout hf in
/-- The five-element closure of the literal quotient-action kernel is K₂. -/
theorem component_quotient_kernel_five_closure (hr : primeRank 5 J = 1) :
    closure {x : G | x ∈ pCoreActionKernelIn 2 J (normalizer (d.K2 : Set G)) ∧
      orderOf x = 5} = d.K2 := by
  apply le_antisymm
  · apply (closure_le _).mpr
    rintro x ⟨hx,ho⟩
    exact component_quotient_kernel_prime_generator_mem_second s d J hJN hJ hq hout hf hr hx ho
  · calc
      d.K2 = closure {x : G | x ∈ d.K2 ∧ orderOf x = 5} := d.second_generated.symm
      _ ≤ _ := Subgroup.closure_mono (by
        rintro x ⟨hx,ho⟩
        exact ⟨second_factor_le_component_quotient_kernel s d J hJN hJ hq hout hx,ho⟩)

include hJN hJ hq hout hf in
/-- The equality uses the actual N_G(K₂) action and its embedded kernel. -/
theorem component_rank_one_literal_kernel_five_closure (hr : primeRank 5 J = 1) :
    ∃ hn : normalizer (d.K2 : Set G) ≤ normalizer (J : Set G),
      closure {x : G | x ∈
        (((pCoreNormalizerAction 2 J).comp (inclusion hn)).ker).map
          (normalizer (d.K2 : Set G)).subtype ∧ orderOf x = 5} = d.K2 := by
  obtain ⟨hn,_,_⟩ := component_rank_one_normalizer_action_kernel s d J hJN hJ hq hout hf hr
  refine ⟨hn,?_⟩
  rw [←pCoreActionKernelIn_eq_map_ker 2 J _ hn]
  exact component_quotient_kernel_five_closure s d J hJN hJ hq hout hf hr

include hJN hJ hq hout hf in
/-- A kernel five-element cannot lie in J: it would survive in the
prime-to-five center of the core quotient. -/
theorem component_kernel_quintic_not_mem (hr : primeRank 5 J = 1)
    {x : G} (hx : x ∈ pCoreActionKernelIn 2 J (normalizer (d.K2 : Set G)))
    (ho : orderOf x = 5) : x ∉ J := by
  intro hxJ
  have hs := (source_secondNormalizer_setup s.ambient T s.empty s.maximal s.unique
    s.many s.module_card s.action s.abelian H s.outside a H1 H2 s.critical d).2.2
  let := component_normal_of_quintic_rank_one s d J hJN hJ hq hout hr
  have hi : Input KnownSimple.IsKnownSimple (normalizer (d.K2 : Set G)) (Mc.pCoreIn 2)
      (Mc ⊓ normalizer (d.K2 : Set G)) J :=
    ⟨hs,⟨hJN,hJ⟩,hq,hf,hout,
      hs.radical_le.trans (le_normalizer_of_normal_subgroupOf hJN)⟩
  let y : J := ⟨x,hxJ⟩
  let q := QuotientGroup.mk' (pCore 2 J)
  obtain ⟨k,hk,he⟩ := hx.2
  have hek : k = (⟨x,J.le_normalizer hxJ⟩ : normalizer (J : Set G)) := Subtype.ext he
  have ha : MulAut.conj (q y) = 1 := by
    rw [←pCoreNormalizerAction_on_component 2 J y]
    exact hek ▸ hk
  have hz : q y ∈ center (J ⧸ pCore 2 J) := by
    apply mem_center_iff.mpr
    intro z
    exact (mul_inv_eq_iff_eq_mul.mp (DFunLike.congr_fun ha z)).symm
  have hqker : IsPGroup 2 q.ker := by rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hoy : orderOf y = 5 := (Subgroup.orderOf_coe y).symm.trans ho
  have hoq : orderOf (q y) = 5 := by
    rw [q.orderOf_map_eq_of_coprime_of_isPGroup_ker hqker _ (by rw [hoy]; decide),hoy]
  have hd : 5 ∣ Nat.card (center (J ⧸ pCore 2 J)) := by
    have heo : orderOf (⟨q y,hz⟩ : center (J ⧸ pCore 2 J)) = 5 :=
      (Subgroup.orderOf_coe _).symm.trans hoq
    exact heo ▸ orderOf_dvd_natCard (⟨q y,hz⟩ : center (J ⧸ pCore 2 J))
  rcases ChapterC.C27Source.coreQuotient_center_card_from_source hi with hc | hc <;>
    rw [hc] at hd <;> norm_num at hd

include hJN hJ hq hout hf in
/-- An inner order-five quotient actor lies in J K₂, using the original
outer-action kernel and the rank-one image of its action kernel modulo J. -/
theorem component_inner_quintic_mem_join_second (hr : primeRank 5 J = 1)
    (x : normalizer (d.K2 : Set G)) (ho : orderOf x = 5)
    (hi : ∀ hn : normalizer (d.K2 : Set G) ≤ normalizer (J : Set G),
      pCoreNormalizerAction 2 J (inclusion hn x) ∈ MulAut.innerSubgroup (J ⧸ pCore 2 J)) :
    (x : G) ∈ J ⊔ d.K2 := by
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := normalizer (d.K2 : Set G)
  let L := J.subgroupOf N
  let B := d.K2.subgroupOf N
  let := component_normal_of_quintic_rank_one s d J hJN hJ hq hout hr
  obtain ⟨hn,he,hrD,hBD⟩ := component_rank_one_outer_action_kernel s d J hJN hJ hq hout hf hr
  let D := ((pCoreNormalizerAction 2 J).comp (inclusion hn)).ker
  have hBD' : B ≤ D := by
    intro b hb
    obtain ⟨y,hy,hey⟩ := hBD hb
    have hey' : y = b := Subtype.ext hey
    exact hey' ▸ hy
  have hB5 : 5 ∣ Nat.card B := by
    rw [Nat.card_congr (subgroupOfEquivOfLe d.K2.le_normalizer).toEquiv]
    by_contra hh
    have hh' := PrimeRank.eq_zero_iff_not_dvd_card.mpr hh
    have hp := second_quintic_rank_pos s d
    omega
  let q := QuotientGroup.mk' L
  have hBimage : 5 ∣ Nat.card (B.map q) := by
    obtain ⟨b,hob⟩ := exists_prime_orderOf_dvd_card' (G := B) 5 hB5
    have hbD : (b : G) ∈ pCoreActionKernelIn 2 J N := by
      rw [pCoreActionKernelIn_eq_map_ker 2 J N hn]
      exact mem_map_of_mem N.subtype (hBD' b.property)
    have hobG : orderOf (b : G) = 5 :=
      (Subgroup.orderOf_coe (b : N)).trans ((Subgroup.orderOf_coe b).trans hob)
    have hbJ := component_kernel_quintic_not_mem s d J hJN hJ hq hout hf hr hbD hobG
    have hqne : q (b : N) ≠ 1 := fun hh => hbJ ((QuotientGroup.eq_one_iff (N := L) (b : N)).mp hh)
    have hqo : orderOf (q (b : N)) = 5 := orderOf_eq_prime (by
      rw [←map_pow]
      have hpow : (b : N)^5 = 1 := by
        rw [←(Subgroup.orderOf_coe b).trans hob,pow_orderOf_eq_one]
      rw [hpow,map_one]) hqne
    have him : q (b : N) ∈ B.map q := mem_map_of_mem q b.property
    have horder : orderOf (⟨q (b : N),him⟩ : B.map q) = 5 :=
      (Subgroup.orderOf_coe _).symm.trans hqo
    exact horder ▸ orderOf_dvd_natCard (⟨q (b : N),him⟩ : B.map q)
  have hx : x ∈ L ⊔ D := by
    rw [←he]
    change QuotientGroup.mk' (MulAut.innerSubgroup (J ⧸ pCore 2 J))
      (pCoreNormalizerAction 2 J (inclusion hn x)) = 1
    exact (QuotientGroup.eq_one_iff _).mpr (hi hn)
  have hxLB := prime_order_mem_sup_of_rank_one_quotient L D B hBD'
    (by decide : Odd 5) hrD.le hBimage x ho hx
  have hxmap := mem_map_of_mem N.subtype hxLB
  rwa [Subgroup.map_sup,map_subgroupOf_eq_of_le hJN,
    map_subgroupOf_eq_of_le d.K2.le_normalizer] at hxmap
include hJN hJ hq hout hf in
/-- The literal rank-one action gives either placement in J K₂ or an
actual outer order-five generator. The first alternative is not K₁ ≤ J. -/
theorem component_rank_one_first_join_or_outer (hr : primeRank 5 J = 1) :
    d.K1 ≤ J ⊔ d.K2 ∨
    ∃ k : normalizer (J : Set G), (k : G) ∈ d.K1 ∧ (k : G) ∉ J ⊔ d.K2 ∧
      orderOf k = 5 ∧ orderOf (pCoreNormalizerAction 2 J k) = 5 ∧
      pCoreNormalizerAction 2 J k ∉ MulAut.innerSubgroup (J ⧸ pCore 2 J) ∧
      orderOf (pCoreNormalizerOuterAction 2 J k) = 5 := by
  classical
  by_cases hle : d.K1 ≤ J ⊔ d.K2
  · exact Or.inl hle
  right
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  have hex : ∃ k ∈ d.K1, orderOf k = 5 ∧ k ∉ J ⊔ d.K2 := by
    by_contra! hh
    exact hle (d.first_generated.ge.trans ((closure_le _).mpr (fun k hk => hh k hk.1 hk.2)))
  obtain ⟨x,hx,ho,houtx⟩ := hex
  have hxN : x ∈ normalizer (d.K2 : Set G) :=
    closure_le_secondNormalizer s d ((show d.K1 ≤ residualClosure H Mc from d.join_eq ▸ le_sup_left) hx)
  let := component_normal_of_quintic_rank_one s d J hJN hJ hq hout hr
  have hn : normalizer (d.K2 : Set G) ≤ normalizer (J : Set G) :=
    le_normalizer_of_normal_subgroupOf hJN
  let k : normalizer (J : Set G) := ⟨x,hn hxN⟩
  have hk : orderOf k = 5 := (Subgroup.orderOf_coe k).symm.trans ho
  have hinner : pCoreNormalizerAction 2 J k ∉ MulAut.innerSubgroup (J ⧸ pCore 2 J) := by
    intro hi
    apply houtx
    apply component_inner_quintic_mem_join_second s d J hJN hJ hq hout hf hr ⟨x,hxN⟩
      ((Subgroup.orderOf_coe _).symm.trans ho)
    intro hn'
    exact hi
  have horder : orderOf (pCoreNormalizerAction 2 J k) = 5 := orderOf_eq_prime (by
    rw [←map_pow,←hk,pow_orderOf_eq_one,map_one]) (fun he => hinner (he ▸ one_mem _))
  exact ⟨k,hx,houtx,hk,horder,hinner,
    MulAut.outer_order_eq_prime_of_prime_order_not_inner _ horder hinner⟩
end CFSG.Quasithin.Chapter14.Section06.OddNormalizer.Quintic.ComponentExtraction
