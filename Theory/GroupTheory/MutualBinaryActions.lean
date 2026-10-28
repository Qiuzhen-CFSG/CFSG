module

public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.Tactic.ByContra

/-!
# Mutual actions of order at most two

Let A and B normalize one another, with A abelian. If each conjugation
image on the other subgroup has order at most two, then [A,B] has order
at most two. Choose the unique possible nontrivial B-action on A. Its
displacement is a homomorphism on A and generates the full commutator.
The reverse action bounds its range by two. No classification or ambient
normality is used; the relative-centralizer formulation retains the
literal ambient subgroups.

Source: the symmetric rank-one step in Aschbacher--Smith 13.5.7,
printed pp.917--918.
-/

@[expose] public section
open Subgroup
open scoped IsMulCommutative commutatorElement
namespace Subgroup

private theorem small_eq_one_or_eq {H:Type*} [Group H] [Finite H]
    (hc:Nat.card H≤2) {t:H} (ht:t≠1) (x:H) : x=1 ∨ x=t := by
  classical
  let f:Bool→H:=fun b=>cond b t 1
  have hf:Function.Injective f := by
    intro a b hab
    cases a <;> cases b <;> simp_all [f]
  have hs:Function.Surjective f := (hf.bijective_of_nat_card_le (by simpa using hc)).2
  obtain ⟨b,rfl⟩:=hs x
  cases b <;> simp [f]

variable {G:Type*} [Group G] [Finite G]

theorem commutator_card_le_two_of_small_mutual_actions
    (A B:Subgroup G) [IsMulCommutative A]
    (hBA:B≤normalizer (A:Set G)) (hAB:A≤normalizer (B:Set G))
    (hf:Nat.card (A.normalizerMonoidHom.comp (inclusion hBA)).range≤2)
    (hh:Nat.card (B.normalizerMonoidHom.comp (inclusion hAB)).range≤2) :
    Nat.card (⁅A,B⁆:Subgroup G)≤2 := by
  let f:=A.normalizerMonoidHom.comp (inclusion hBA)
  let h:=B.normalizerMonoidHom.comp (inclusion hAB)
  by_cases hz:f.range=⊥
  · have hc:⁅A,B⁆=⊥ := by
      rw [commutator_comm,commutator_eq_bot_iff_le_centralizer]
      intro b hb
      apply mem_centralizer_iff.mpr
      intro a ha
      have hb1:f ⟨b,hb⟩=1 := mem_bot.mp (hz ▸ (show f ⟨b,hb⟩∈f.range from ⟨⟨b,hb⟩,rfl⟩))
      have he:=congrArg (fun u:MulAut A=>(u ⟨a,ha⟩:G)) hb1
      change b*a*b⁻¹=a at he
      exact (mul_inv_eq_iff_eq_mul.mp he).symm
    rw [hc,card_bot]
    decide
  obtain ⟨k,hk,hkn⟩:∃k∈f.range,k≠1 := by
    by_contra! he
    exact hz (eq_bot_iff.mpr he)
  obtain ⟨b,rfl⟩:=hk
  have hcases (b':B):f b'=1 ∨ f b'=f b := by
    rcases small_eq_one_or_eq hf (t:=⟨f b,⟨b,rfl⟩⟩)
      (by intro he;exact hkn (congrArg Subtype.val he))
      ⟨f b',⟨b',rfl⟩⟩ with he|he
    · exact Or.inl (congrArg Subtype.val he)
    · exact Or.inr (congrArg Subtype.val he)
  let δ:A→*A := {
    toFun:=fun a=>f b a*a⁻¹
    map_one':=by simp
    map_mul':=by
      intro a a'
      change f b (a*a')*(a*a')⁻¹=(f b a*a⁻¹)*(f b a'*a'⁻¹)
      simp only [map_mul,mul_inv_rev]
      ac_rfl }
  have hker:h.ker≤δ.ker := by
    intro a ha
    have he:=congrArg (fun u:MulAut B=>(u b:G)) (show h a=1 from ha)
    change (a:G)*b*(a:G)⁻¹=b at he
    apply Subtype.ext
    change (b:G)*a*(b:G)⁻¹*(a:G)⁻¹=1
    apply commutatorElement_eq_one_iff_mul_comm.mpr
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  have hd:Nat.card δ.range≤2 := by
    have hv:=index_dvd_of_le hker
    rw [index_ker,index_ker] at hv
    exact (Nat.le_of_dvd Nat.card_pos hv).trans hh
  have hle:⁅A,B⁆≤δ.range.map A.subtype := by
    rw [commutator_comm]
    apply commutator_le.mpr
    intro b' hb' a ha
    rcases hcases ⟨b',hb'⟩ with he|he
    · have he':b'*a*b'⁻¹=a :=
        congrArg (fun u:MulAut A=>(u ⟨a,ha⟩:G)) he
      have hz':⁅b',a⁆=1 := by change b'*a*b'⁻¹*a⁻¹=1;rw [he',mul_inv_cancel]
      rw [hz'];exact (δ.range.map A.subtype).one_mem
    · refine ⟨δ ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,?_⟩
      change (f b ⟨a,ha⟩:G)*a⁻¹=b'*a*b'⁻¹*a⁻¹
      rw [←he]
      rfl
  have he:Nat.card (δ.range.map A.subtype)=Nat.card δ.range :=
    card_map_of_injective A.subtype_injective
  exact (Nat.card_le_card_of_injective (inclusion hle) (inclusion_injective hle)).trans
    (he.le.trans hd)

omit [Finite G] in
theorem normalizer_action_range_card (A B:Subgroup G)
    (hBA:B≤normalizer (A:Set G)) :
    Nat.card (A.normalizerMonoidHom.comp (inclusion hBA)).range=
      (centralizer (A:Set G)).relIndex B := by
  rw [←index_ker]
  change _=((centralizer (A:Set G)).subgroupOf B).index
  congr 1
  ext b
  change A.normalizerMonoidHom (inclusion hBA b)=1 ↔ b.val∈centralizer (A:Set G)
  constructor
  · intro h
    apply mem_centralizer_iff.mpr
    intro a ha
    have he:=congrArg (fun f:MulAut A=>(f ⟨a,ha⟩:G)) h
    change b.val*a*b.val⁻¹=a at he
    exact (mul_inv_eq_iff_eq_mul.mp he).symm
  · intro hb
    ext a
    change b.val*a.val*b.val⁻¹=a.val
    rw [←mem_centralizer_iff.mp hb a.val a.property,mul_inv_cancel_right]

theorem commutator_card_le_two_of_mutual_centralizer_indices
    (A B:Subgroup G) [IsMulCommutative A]
    (hBA:B≤normalizer (A:Set G)) (hAB:A≤normalizer (B:Set G))
    (hf:(centralizer (A:Set G)).relIndex B≤2)
    (hh:(centralizer (B:Set G)).relIndex A≤2) :
    Nat.card (⁅A,B⁆:Subgroup G)≤2 := by
  apply commutator_card_le_two_of_small_mutual_actions A B hBA hAB
  · rwa [normalizer_action_range_card]
  · rwa [normalizer_action_range_card]
end Subgroup
