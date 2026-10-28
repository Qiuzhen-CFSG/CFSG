module
public import Theory.GroupTheory.PResidual.CentralSylowFrattini
public import Theory.GroupTheory.PResidual.PrimeSection
public import Theory.GroupTheory.PResidual.Quotient
public import Theory.GroupTheory.PResidual.PerfectCover
public import Theory.GroupTheory.CentralizerModulo
public import Theory.GroupTheory.Commutator.NormalClosure

/-! A two-perfect group has no central Sylow two-subgroup. Consequently the
two-core intersection of a residual vanishes modulo a supplied normal
two-subgroup when that intersection is central modulo it and the residual
image has odd order. This is the source-neutral core step in 14.3.18(5).
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G D : Type*} [Group G] [Finite G] [Group D]

theorem ker_eq_bot_of_isPPerfect_of_central_of_odd_range
    (hG : IsPPerfect 2 G) (f : G →* D) (hp : IsPGroup 2 f.ker)
    (hc : f.ker ≤ center G) (ho : Odd (Nat.card f.range)) : f.ker=⊥ := by
  have hi : ¬2∣f.ker.index := by rw [index_ker]; exact ho.not_two_dvd_nat
  let S : Sylow 2 G := hp.toSylow hi
  have hS : (S:Subgroup G)=f.ker := IsPGroup.toSylow_coe hp hi
  have hfr : (⊤:Subgroup S)≤frattini S :=
    central_subgroup_le_frattini_sylow_of_isPPerfect hG S ⊤ (by
      rw [←MonoidHom.range_eq_map,(S:Subgroup G).range_subtype,hS]
      exact hc)
  have ht : (⊥:Subgroup S)=⊤ := frattini_nongenerating (by
    rw [bot_sup_eq]
    exact top_unique hfr)
  apply le_bot_iff.mp
  intro x hx
  have hsx : x∈(S:Subgroup G) := by rwa [hS]
  have hs : (⟨x,hsx⟩:S)∈(⊥:Subgroup S) := ht.symm ▸ mem_top _
  exact congrArg Subtype.val (mem_bot.mp hs)

theorem pResidual_inf_pCore_le_of_central_mod
    (U : Subgroup G) [U.Normal] (hU : U≤pCore 2 G)
    (hc : ⁅pResidual 2 G,pCore 2 G⁆≤U)
    (ho : Odd (Nat.card ((pResidual 2 G).map (QuotientGroup.mk' (pCore 2 G))))) :
    pResidual 2 G⊓pCore 2 G≤U := by
  let K := pResidual 2 G
  let UK := U.subgroupOf K
  let q := QuotientGroup.mk' (pCore 2 G)
  let f : K →* G⧸pCore 2 G := q.comp K.subtype
  have hUK : UK≤f.ker := by
    intro x hx
    exact (QuotientGroup.eq_one_iff (x:G)).mpr (hU hx)
  let π := QuotientGroup.mk' UK
  let fbar := QuotientGroup.lift UK f hUK
  have he : fbar.comp π=f := rfl
  have hker : fbar.ker=f.ker.map π := QuotientGroup.ker_lift UK f hUK
  have hp : IsPGroup 2 f.ker := by
    have hh : f.ker=(pCore 2 G).subgroupOf K := by
      ext x
      exact QuotientGroup.eq_one_iff (x:G)
    rw [hh]
    exact pCore_isPGroup.comap_subtype
  have hcentral : fbar.ker≤center (K⧸UK) := by
    rw [hker]
    rintro x ⟨a,ha,rfl⟩
    apply mem_center_iff.mpr
    intro y
    obtain ⟨b,rfl⟩ := QuotientGroup.mk'_surjective UK y
    have haq : (a:G)∈pCore 2 G := (QuotientGroup.eq_one_iff _).mp ha
    have hab : ⁅b,a⁆∈UK := hc (commutator_mem_commutator b.property haq)
    have hz : ⁅π b,π a⁆=1 := by
      rw [←map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).mpr hab
    exact commutatorElement_eq_one_iff_mul_comm.mp hz
  have hrange : fbar.range=f.range := by
    rw [←he,MonoidHom.range_comp,MonoidHom.range_eq_top.mpr
      (QuotientGroup.mk'_surjective UK),←MonoidHom.range_eq_map]
  have hodd : Odd (Nat.card fbar.range) := by
    rw [hrange]
    change Odd (Nat.card (q.comp K.subtype).range)
    rw [MonoidHom.range_comp,K.range_subtype]
    exact ho
  have hb : fbar.ker=⊥ := ker_eq_bot_of_isPPerfect_of_central_of_odd_range
    ((isPPerfect_pResidual (G:=G) 2).of_surjective π (QuotientGroup.mk'_surjective UK))
    fbar (hker ▸ hp.map π) hcentral hodd
  intro x hx
  let a : K := ⟨x,hx.1⟩
  have ha : π a∈fbar.ker := by
    change fbar (π a)=1
    change q x=1
    exact (QuotientGroup.eq_one_iff x).mpr hx.2
  have hz : π a=1 := mem_bot.mp (hb ▸ ha)
  exact (QuotientGroup.eq_one_iff a).mp hz

theorem commutator_pResidual_core_le_of_normalClosure_cover
    (U R : Subgroup G) [U.Normal]
    (hR : ⁅pCore 2 G,R⁆≤U)
    (hcover : (pResidual 2 G).map (QuotientGroup.mk' (pCore 2 G)) ≤
      (normalClosure (R:Set G)).map (QuotientGroup.mk' (pCore 2 G))) :
    ⁅pResidual 2 G,pCore 2 G⁆≤U := by
  let C := centralizerModulo ⊤ (pCore 2 G) U
  let q := QuotientGroup.mk' U
  have hC : C=(centralizer ((pCore 2 G).map q:Set (G⧸U))).comap q := by
    simp only [C,q,centralizerModulo,top_inf_eq]
  let : C.Normal := by
    rw [hC]
    infer_instance
  have hRC : R≤C := by
    intro r hr
    exact mem_centralizerModulo_iff.mpr ⟨mem_top _,fun a ha=>
      hR (commutator_mem_commutator ha hr)⟩
  have hn : normalClosure (R:Set G)≤C := normalClosure_le_normal hRC
  have hsup : pResidual 2 G≤C⊔pCore 2 G := by
    have hh := (le_comap_map (QuotientGroup.mk' (pCore 2 G)) (pResidual 2 G)).trans
      (comap_mono (hcover.trans (map_mono hn)))
    simpa only [comap_map_eq,QuotientGroup.ker_mk'] using hh
  have hKC := le_normal_of_isPPerfect_of_le_sup_pGroup (pResidual 2 G) C (pCore 2 G)
    (isPPerfect_pResidual 2) pCore_isPGroup hsup
  rw [commutator_comm,commutator_le]
  intro a ha k hk
  exact (mem_centralizerModulo_iff.mp (hKC hk)).2 a ha

/-- The same central-kernel bound through an arbitrary map with the literal
prime core as kernel. This avoids replacing a consumer's quotient. -/
theorem pResidual_inf_pCore_le_of_central_mod_map
    (U:Subgroup G) [U.Normal] (hU:U≤pCore 2 G)
    (hc:⁅pResidual 2 G,pCore 2 G⁆≤U)
    (f:G→*D) (hk:f.ker=pCore 2 G)
    (ho:Odd (Nat.card ((pResidual 2 G).map f))) :
    pResidual 2 G⊓pCore 2 G≤U := by
  apply pResidual_inf_pCore_le_of_central_mod U hU hc
  have he : Nat.card ((pResidual 2 G).map (QuotientGroup.mk' (pCore 2 G)))=
      Nat.card ((pResidual 2 G).map f) := by
    rw [←relIndex_ker,←relIndex_ker,QuotientGroup.ker_mk',hk]
  exact he.symm ▸ ho

theorem commutator_pResidual_core_le_of_normalClosure_cover_map
    (U R : Subgroup G) [U.Normal]
    (hR : ⁅pCore 2 G,R⁆≤U)
    (f:G→*D) (hk:f.ker=pCore 2 G)
    (hcover : (pResidual 2 G).map f ≤ (normalClosure (R:Set G)).map f) :
    ⁅pResidual 2 G,pCore 2 G⁆≤U := by
  let C := centralizerModulo ⊤ (pCore 2 G) U
  let q := QuotientGroup.mk' U
  have hC : C=(centralizer ((pCore 2 G).map q:Set (G⧸U))).comap q := by
    simp only [C,q,centralizerModulo,top_inf_eq]
  let : C.Normal := by
    rw [hC]
    infer_instance
  have hRC : R≤C := by
    intro r hr
    exact mem_centralizerModulo_iff.mpr ⟨mem_top _,fun a ha=>
      hR (commutator_mem_commutator ha hr)⟩
  have hn : normalClosure (R:Set G)≤C := normalClosure_le_normal hRC
  have hsup : pResidual 2 G≤C⊔pCore 2 G := by
    have hh := (le_comap_map f (pResidual 2 G)).trans
      (comap_mono (hcover.trans (map_mono hn)))
    simpa only [comap_map_eq,hk] using hh
  have hKC := le_normal_of_isPPerfect_of_le_sup_pGroup (pResidual 2 G) C (pCore 2 G)
    (isPPerfect_pResidual 2) pCore_isPGroup hsup
  rw [commutator_comm,commutator_le]
  intro a ha k hk
  exact (mem_centralizerModulo_iff.mp (hKC hk)).2 a ha

end Subgroup
