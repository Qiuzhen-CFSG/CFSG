module
public import Theory.GroupTheory.DisjointConjugateCenter
public import Mathlib.GroupTheory.SpecificGroups.KleinFour
public import Theory.GroupTheory.CharacteristicCentralizerFusion
/-! # Central factors with disjoint conjugates
An index-two central factor with a disjoint conjugate has order two, and
its two conjugates fill a center of order four. The actual involutions
and ambient center line are then recovered. A normalized subgroup whose
center has order two contributes that whole central line to the actor group.
Source: Aschbacher--Smith 2.5.8(4) and 2.5.11, printed pp.557--558.
-/
public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem center_pair_of_disjoint_factor
    (S K C:Subgroup G) (hsplit:centerIn S=K⊔C)
    (hKC:Disjoint K C) (hK:Nat.card K=2) (hC:C≠⊥)
    (x:G) (hx:x∈normalizer (S:Set G)) (hd:Disjoint C (C.conjBy x)) :
    Nat.card C=2 ∧ Nat.card (centerIn S)=4 ∧ centerIn S=C⊔C.conjBy x := by
  have hKZ:K≤centerIn S:=hsplit ▸ le_sup_left
  have hCZ:C≤centerIn S:=hsplit ▸ le_sup_right
  have hCK:C≤centralizer (K:Set G):=fun c hc k hk=>(hCZ hc).2 k (hKZ hk).1
  have hsize:Nat.card (centerIn S)=2*Nat.card C:=by
    rw [hsplit,card_sup_eq_mul_of_normalizes_of_disjoint K C
      (hCK.trans (Subgroup.centralizer_le_normalizer _)) hKC,hK]
  have hxZ:x∈normalizer (centerIn S:Set G):=
    normalizes_centerIn (S:=S) (A:=normalizer (S:Set G)) le_rfl hx
  have hc2:=card_le_two_of_disjoint_conjugate hCZ hxZ hd hsize
  have hcpos:0<Nat.card C:=Nat.card_pos
  have hcne:Nat.card C≠1:=fun hh=>hC (C.eq_bot_iff_card.mpr hh)
  have hc:Nat.card C=2:=by omega
  have hz:Nat.card (centerIn S)=4:=by rw [hsize,hc]
  have hCx:C.conjBy x≤centerIn S:=by
    have hm:=map_mono (f:=(MulAut.conj x).toMonoidHom) hCZ
    have he:(centerIn S).map (MulAut.conj x).toMonoidHom=centerIn S:=mem_normalizer_iff_map_conj_eq.mp hxZ
    rwa [he] at hm
  have hcc:C.conjBy x≤centralizer (C:Set G):=fun c hcx a ha=>(hCx hcx).2 a (hCZ ha).1
  refine ⟨hc,hz,?_⟩
  apply (eq_of_le_of_card_ge (sup_le hCZ hCx) ?_).symm
  rw [card_sup_eq_mul_of_normalizes_of_disjoint C (C.conjBy x)
    (hcc.trans (Subgroup.centralizer_le_normalizer _)) hd,
    show Nat.card (C.conjBy x)=Nat.card C from card_map_of_injective (MulAut.conj x).injective,hc,hz]

theorem exists_involution_generator_of_card_two (C:Subgroup G) (hc:Nat.card C=2) :
    ∃t:G,orderOf t=2 ∧ zpowers t=C := by
  obtain ⟨t,ht⟩:=exists_prime_orderOf_dvd_card' (G:=C) 2 (by rw [hc])
  have htG:orderOf (t:G)=2:=(Subgroup.orderOf_coe t).trans ht
  refine ⟨t,htG,eq_of_le_of_card_ge (zpowers_le.mpr t.property) ?_⟩
  rw [Nat.card_zpowers,htG,hc]
theorem center_eq_marked_line_of_four
    (S T:Subgroup G) (hST:S≤T) (hZT:centerIn T≤S)
    (hfour:Nat.card (centerIn S)=4)
    (z:G) (hz:orderOf z=2) (hzT:z∈centerIn T)
    (t:G) (htS:t∈centerIn S) (htT:t∉centerIn T) :
    centerIn T=zpowers z := by
  have hle:centerIn T≤centerIn S:=le_inf hZT (inf_le_right.trans (centralizer_le hST))
  have hcard:Nat.card (centerIn T)≤4:=hfour ▸ card_le_of_le hle
  have hne:Nat.card (centerIn T)≠4:=by
    intro hc
    have he:=eq_of_le_of_card_ge hle (by omega)
    exact htT (he.symm ▸ htS)
  have hd:Nat.card (centerIn T)∣4:=by
    rw [←hfour]
    exact card_dvd_of_le hle
  have ht:Nat.card (centerIn T)≤2:=by
    by_contra hh
    have he:Nat.card (centerIn T)=3:=by omega
    rw [he] at hd
    norm_num at hd
  have hzp:zpowers z≤centerIn T:=zpowers_le.mpr hzT
  exact (eq_of_le_of_card_ge hzp (by rwa [Nat.card_zpowers,hz])).symm
theorem center_factor_card_two_of_sylow_center
    (S K:Subgroup G) (hSK:S≤normalizer (K:Set G))
    (hc:Nat.card (centerIn (S⊓K))=2) :
    Nat.card (centerIn S⊓K:Subgroup G)=2 ∧ centerIn S⊓K=centerIn (S⊓K) := by
  have hn:S≤normalizer (S⊓K:Set G):=by
    intro s hs
    exact fun a=>and_congr (S.le_normalizer hs a) (hSK hs a)
  have hZn:S≤normalizer (centerIn (S⊓K):Set G):=normalizes_centerIn hn
  have hzcent:centerIn (S⊓K)≤centralizer (S:Set G):=by
    obtain ⟨z,hz,hgen⟩:=exists_involution_generator_of_card_two (centerIn (S⊓K)) hc
    have hh:S≤normalizer (zpowers z:Set G):=hgen.symm ▸ hZn
    rw [normalizer_zpowers_eq_centralizer_of_order_two z hz] at hh
    apply le_centralizer_iff.mp
    rw [←hgen]
    intro s hs
    apply mem_centralizer_iff.mpr
    intro a ha
    have hza:z∈centralizer ({s}:Set G):=mem_centralizer_singleton_iff.mpr
      (mem_centralizer_singleton_iff.mp (hh hs)).symm
    exact mem_centralizer_singleton_iff.mp ((zpowers_le.mpr hza) ha)
  have he:centerIn S⊓K=centerIn (S⊓K):=by
    apply le_antisymm
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
        (inf_le_left.trans (inf_le_right.trans (centralizer_le inf_le_left)))
    · exact le_inf (le_inf (inf_le_left.trans inf_le_left) hzcent) (inf_le_left.trans inf_le_right)
  exact ⟨he.symm ▸ hc,he⟩
end Subgroup
