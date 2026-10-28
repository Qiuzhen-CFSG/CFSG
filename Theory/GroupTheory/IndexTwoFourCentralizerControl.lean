module

public import Theory.GroupTheory.StrongEmbedding
public import Theory.GroupTheory.Involution.Dihedral
public import Theory.GroupTheory.InvolutionCentralizerControl
public import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
# Normalizer control across an index-two centralizer

Let C be normal of index two and T a Sylow two-subgroup with |T∩C|=4.
A subgroup containing T, the normalizer of T∩C, and the centralizers of
all involutions in T is the whole group, provided T contains involutions
both inside and outside C.  Strong embedding would force those involutions
into the same C-coset: a product of involutions across a strongly embedded
subgroup has odd order.  The strong-embedding criterion then reduces the
remaining normalizers to intersections with C of order one, two, or four.

The cubic-line application derives the index-two condition from the actual
normalizer action on a subgroup of order three.

Source: Aschbacher, *Sporadic Groups* (1994), Lemma 45.7(3), printed p.245.
-/

public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem strong_centralizer (M : Subgroup G) (hM : IsStronglyEmbedded M)
    {a:G} (haM:a∈M) (ha:IsInvolution a) : centralizer ({a}:Set G)≤M := by
  intro g hg
  by_contra hn
  apply hM.2.2 g hn a ⟨haM,?_⟩ ha
  refine ⟨a,haM,?_⟩
  change g*a*g⁻¹=a
  exact mul_inv_eq_iff_eq_mul.mpr (mem_centralizer_singleton_iff.mp hg)

private theorem strong_odd_product (M : Subgroup G) (hM : IsStronglyEmbedded M)
    {a b:G} (haM:a∈M) (ha:IsInvolution a) (hbM:b∉M) (hb:IsInvolution b) :
    Odd (orderOf (a*b)) := by
  apply Nat.not_even_iff_odd.mp
  rintro ⟨n,hn⟩
  have hab:a≠b := fun he=>hbM (he ▸ haM)
  have he:orderOf (a*b)=2*n := by omega
  obtain ⟨hw,hwa,hwb⟩ := BenderSuzuki.External.Suzuki.V.suzuki_ch5_proposition_1_2_iii ha hb hab he
  have hwM : (a*b)^n∈M := strong_centralizer M hM haM ha
    (mem_centralizer_singleton_iff.mpr hwa.eq)
  exact hbM (strong_centralizer M hM hwM hw (mem_centralizer_singleton_iff.mpr hwb.symm.eq))

omit [Finite G] in
private theorem odd_element_mem_index_two (C : Subgroup G) [C.Normal] (hC:C.index=2)
    (a:G) (ha:Odd (orderOf a)) : a∈C := by
  let q := QuotientGroup.mk' C
  have hd:orderOf (q a)∣2 := by rw [←hC]; exact _root_.orderOf_dvd_natCard (q a)
  have ho:Odd (orderOf (q a)) := Odd.of_dvd_nat ha (orderOf_map_dvd q a)
  have h1:orderOf (q a)=1 := ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_right (by intro he;rw[he] at ho;exact (by decide : ¬Odd 2) ho)
  exact (QuotientGroup.eq_one_iff a).mp (orderOf_eq_one_iff.mp h1)

theorem not_stronglyEmbedded_of_index_two_involutions (C M : Subgroup G) [C.Normal]
    (hC:C.index=2) (a b:G) (ha:a∈M) (hb:b∈M)
    (hao:IsInvolution a) (hbo:IsInvolution b) (haC:a∈C) (hbC:b∉C) :
    ¬IsStronglyEmbedded M := by
  intro hM
  obtain ⟨g,hg⟩ := SetLike.exists_of_lt (lt_top_iff_ne_top.mpr hM.1)
  have hgM:g∉M := hg.2
  let t:=g*a*g⁻¹
  have ht:IsInvolution t := by
    constructor
    · intro ht
      apply hao.1
      exact (MulAut.conj g).injective (ht.trans (map_one (MulAut.conj g)).symm)
    · change (MulAut.conj g a)^2=1
      rw[←map_pow,hao.2,map_one]
  have htM:t∉M := by
    intro hh
    exact hM.2.2 g hgM t ⟨hh,⟨a,ha,rfl⟩⟩ ht
  have hat:a*t∈C := odd_element_mem_index_two C hC _ (strong_odd_product M hM ha hao htM ht)
  have hbt:b*t∈C := odd_element_mem_index_two C hC _ (strong_odd_product M hM hb hbo htM ht)
  have htC:t∈C := (C.mul_mem_cancel_left haC).mp hat
  exact hbC ((C.mul_mem_cancel_right htC).mp hbt)

private theorem normalizer_card_two_le (M T Q : Subgroup G)
    (hQT:Q≤T) (hQ:Nat.card Q=2)
    (hc:∀x∈T,orderOf x=2→centralizer ({x}:Set G)≤M) : normalizer (Q:Set G)≤M := by
  obtain ⟨x,hx⟩ := exists_prime_orderOf_dvd_card' (G:=Q) 2 (by rw[hQ])
  have hxG:orderOf (x:G)=2 := (orderOf_injective Q.subtype Q.subtype_injective x).trans hx
  exact (normalizer_le_centralizer_of_card_two Q hQ).trans
    ((centralizer_le (show ({(x:G)}:Set G)⊆Q from Set.singleton_subset_iff.mpr x.property)).trans
      (hc x (hQT x.property) hxG))

theorem eq_top_of_index_two_four_centralizers
    (C M : Subgroup G) [C.Normal] (hC:C.index=2) (T:Sylow 2 G)
    (hTM:(T:Subgroup G)≤M) (hA:Nat.card ((T:Subgroup G)⊓C:Subgroup G)=4)
    (hn:normalizer (((T:Subgroup G)⊓C:Subgroup G):Set G)≤M)
    (hc:∀x∈(T:Subgroup G),orderOf x=2→centralizer ({x}:Set G)≤M)
    (a b:G) (ha:a∈T) (hb:b∈T) (hao:orderOf a=2) (hbo:orderOf b=2)
    (haC:a∈C) (hbC:b∉C) : M=⊤ := by
  by_contra hM
  have hai:IsInvolution a := ⟨by intro he;rw[he,orderOf_one] at hao;omega,by rw[←hao];exact pow_orderOf_eq_one a⟩
  have hbi:IsInvolution b := ⟨by intro he;rw[he,orderOf_one] at hbo;omega,by rw[←hbo];exact pow_orderOf_eq_one b⟩
  have hnot := not_stronglyEmbedded_of_index_two_involutions C M hC a b (hTM ha) (hTM hb) hai hbi haC hbC
  have hTne:(T:Subgroup G)≠⊥ := by intro he;exact hai.1 (mem_bot.mp (he ▸ ha))
  obtain ⟨Q,hQne,_,hQT,hN⟩ := exists_twoSubgroup_le_sylow_normalizer_not_le_of_not_stronglyEmbedded T hTne M hM hTM hnot
  apply hN
  let A:=Q⊓C
  have hAle:A≤(T:Subgroup G)⊓C := inf_le_inf_right _ hQT
  have hd:Nat.card A∣4 := hA ▸ card_dvd_of_le hAle
  have hcases:Nat.card A=1∨Nat.card A=2∨Nat.card A=4 := by
    have hh:=Nat.mem_divisors.mpr ⟨hd,(by decide:4≠0)⟩
    have he:Nat.divisors 4={1,2,4} := by decide
    simpa only [he,Finset.mem_insert,Finset.mem_singleton] using hh
  have hNA:normalizer (Q:Set G)≤normalizer (A:Set G) :=
    (le_inf le_rfl le_normalizer_of_normal).trans inf_normalizer_le_normalizer_inf
  rcases hcases with h1|h2|h4
  · have hAb:A=⊥ := (eq_bot_iff_card A).mpr h1
    have hqc:Nat.card Q∣2 := by
      have hh:C.relIndex Q∣2 := hC ▸ relIndex_dvd_index_of_normal C Q
      rw[←inf_relIndex_right,inf_comm] at hh
      change A.relIndex Q∣2 at hh
      rwa[hAb,relIndex_bot_left] at hh
    have hq2:Nat.card Q=2 := ((Nat.dvd_prime Nat.prime_two).mp hqc).resolve_left (by intro he;exact hQne ((eq_bot_iff_card Q).mpr he))
    exact normalizer_card_two_le M T Q hQT hq2 hc
  · exact hNA.trans (normalizer_card_two_le M T A (inf_le_left.trans hQT) h2 hc)
  · have he:A=(T:Subgroup G)⊓C := eq_of_le_of_card_ge hAle (by rw[hA,h4])
    exact hNA.trans (he ▸ hn)
/-- A nontrivial action on a subgroup of order three has the full automizer. -/
theorem centralizer_relIndex_normalizer_eq_two_of_card_three
    (U : Subgroup G) (hU : Nat.card U = 3) (t : G)
    (ht : t ∈ normalizer (U : Set G)) (htC : t ∉ centralizer (U : Set G)) :
    (centralizer (U : Set G)).relIndex (normalizer (U : Set G)) = 2 := by
  let : IsCyclic U := isCyclic_of_prime_card hU
  have ha : Nat.card (MulAut U) = 2 := by
    rw [IsCyclic.card_mulAut, hU]
    decide
  have hd : (centralizer (U : Set G)).relIndex (normalizer (U : Set G)) ∣ 2 := by
    have hh := U.normalizerMonoidHom.range.card_subgroup_dvd_card
    rw [← index_ker, U.normalizerMonoidHom_ker, ha] at hh
    exact hh
  exact ((Nat.dvd_prime Nat.prime_two).mp hd).resolve_left (fun h1 =>
    htC (relIndex_eq_one.mp h1 ht))

/-- Source normalizer closure for a cubic line.  The hypotheses are the
local involution-centralizer and four-group normalizer bounds. -/
theorem normalizer_le_of_card_three_four_centralizers
    (U I : Subgroup G) (hU : Nat.card U = 3)
    (T : Sylow 2 (normalizer (U : Set G)))
    (hTI : (T : Subgroup (normalizer (U : Set G))) ≤ I.subgroupOf (normalizer (U : Set G)))
    (hA : Nat.card ((T : Subgroup (normalizer (U : Set G))) ⊓
      (centralizer (U : Set G)).subgroupOf (normalizer (U : Set G)) : Subgroup (normalizer (U : Set G))) = 4)
    (hn : normalizer (((T : Subgroup (normalizer (U : Set G))) ⊓
      (centralizer (U : Set G)).subgroupOf (normalizer (U : Set G))) :
      Set (normalizer (U : Set G))) ≤ I.subgroupOf (normalizer (U : Set G)))
    (hc : ∀ x ∈ (T : Subgroup (normalizer (U : Set G))), orderOf x = 2 →
      centralizer ({x} : Set (normalizer (U : Set G))) ≤ I.subgroupOf (normalizer (U : Set G)))
    (a b : normalizer (U : Set G)) (ha : a ∈ T) (hb : b ∈ T)
    (hao : orderOf a = 2) (hbo : orderOf b = 2)
    (haC : (a : G) ∈ centralizer (U : Set G))
    (hbC : (b : G) ∉ centralizer (U : Set G)) : normalizer (U : Set G) ≤ I := by
  let C := (centralizer (U : Set G)).subgroupOf (normalizer (U : Set G))
  have hker : C = U.normalizerMonoidHom.ker := U.normalizerMonoidHom_ker.symm
  let : C.Normal := hker ▸ U.normalizerMonoidHom.normal_ker
  have hC : C.index = 2 := centralizer_relIndex_normalizer_eq_two_of_card_three U hU b b.property hbC
  have he := eq_top_of_index_two_four_centralizers C (I.subgroupOf (normalizer (U : Set G)))
    hC T hTI hA hn hc a b ha hb hao hbo haC hbC
  intro x hx
  exact (show (⟨x,hx⟩ : normalizer (U : Set G)) ∈ I.subgroupOf (normalizer (U : Set G)) from
    he ▸ mem_top _)

end Subgroup
