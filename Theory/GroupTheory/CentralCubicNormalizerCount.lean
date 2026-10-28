module

public import Theory.GroupTheory.NormalizedSupCard
public import Mathlib.GroupTheory.Commutator.Basic
public import Mathlib.GroupTheory.Sylow

/-!
# A central cubic displacement and a normalizer count

In a class-two group whose commutators lie in a central cubic line, the
centralizer of any internal cubic line has index dividing three: its
commutator row is a homomorphism into that central line. If an abelian
ambient layer meets the odd group in order27 and has normalizer quotient
of order24, the odd part of the centralizer has order dividing81. The whole
odd group therefore has order dividing243.

This is the finite counting step in Aschbacher, Sporadic Groups (1994),45.8,
printed p246. No extraspecial or dimension conclusion is an input.
-/

public section
open Subgroup
open scoped commutatorElement
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem central_line_centralizer_relIndex_dvd (D W F:Subgroup G)
    (hW:Nat.card W=3) (hF:Nat.card F=3) (hFD:F≤D)
    (hcom:⁅D,D⁆≤W) (hcen:W≤centralizer (D:Set G)) :
    (centralizer (F:Set G)).relIndex D∣3 := by
  obtain ⟨t,ht⟩:=exists_prime_orderOf_dvd_card' (G:=F) 3 (hF ▸ dvd_rfl)
  have htG:orderOf (t:G)=3:=(orderOf_injective F.subtype F.subtype_injective t).trans ht
  have hFt:F=zpowers (t:G):=(eq_of_le_of_card_ge (zpowers_le.mpr t.property)
    (by rw [Nat.card_zpowers,htG,hF])).symm
  let f:D→*W:={
    toFun d:=⟨⁅(d:G),(t:G)⁆,hcom (commutator_mem_commutator d.property (hFD t.property))⟩
    map_one':=by apply Subtype.ext;simp
    map_mul' a b:=by
      apply Subtype.ext
      change ⁅(a:G)*(b:G),(t:G)⁆=⁅(a:G),(t:G)⁆*⁅(b:G),(t:G)⁆
      have hb:=hcom (commutator_mem_commutator b.property (hFD t.property))
      have hc:=mem_centralizer_iff.mp (hcen hb) a a.property
      rw [commutatorElement_mul_left_eq_conj_mul,hc]
      simp only [mul_inv_cancel_right]
      have hd:⁅(a:G),(t:G)⁆∈D:=le_normalizer_iff_commutator_le_left.mp D.le_normalizer
        (commutator_mem_commutator a.property (hFD t.property))
      exact (mem_centralizer_iff.mp (hcen hb) _ hd).symm }
  have hker:f.ker=(centralizer ({(t:G)}:Set G)).subgroupOf D:=by
    ext d
    change (⟨⁅(d:G),(t:G)⁆,_⟩:W)=1 ↔ _
    rw [Subtype.ext_iff]
    change ⁅(d:G),(t:G)⁆=1 ↔ (d:G)∈centralizer ({(t:G)}:Set G)
    rw [commutatorElement_eq_one_iff_mul_comm,mem_centralizer_singleton_iff]
  rw [hFt,zpowers_eq_closure,centralizer_closure]
  change ((centralizer ({(t:G)}:Set G)).subgroupOf D).index∣3
  rw [←hker,index_ker]
  exact hW ▸ f.range.card_subgroup_dvd_card
end Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
theorem odd_central_cubic_card_dvd_243 (D W V F:Subgroup G)
    (hodd:Odd (Nat.card D)) (hW:Nat.card W=3) (hF:Nat.card F=3) (hFD:F≤D)
    (hcom:⁅D,D⁆≤W) (hcen:W≤centralizer (D:Set G))
    (hVF:V≤centralizer (F:Set G)) (hVN:normalizer (F:Set G)≤normalizer (V:Set G))
    (hindex:V.relIndex (normalizer (F:Set G))=24)
    (hcap:Nat.card (D⊓V:Subgroup G)=27) : Nat.card D∣243 := by
  let N:=normalizer (F:Set G)
  let C:=D⊓centralizer (F:Set G)
  have hCN:C≤N:=inf_le_right.trans (centralizer_le_normalizer _)
  have hVle:V≤N:=hVF.trans (centralizer_le_normalizer _)
  let : (V.subgroupOf N).Normal:=(normal_subgroupOf_iff_le_normalizer hVle).mpr hVN
  have hd:V.relIndex C∣24:=by
    have hh:=relIndex_dvd_index_of_normal (V.subgroupOf N) (C.subgroupOf N)
    rw [relIndex_subgroupOf hCN] at hh
    change V.relIndex C∣V.relIndex N at hh
    rwa [hindex] at hh
  have ho:Odd (V.relIndex C):=(hodd.of_dvd_nat (card_dvd_of_le (inf_le_left:C≤D))).of_dvd_nat
    (relIndex_dvd_card V C)
  have h3:V.relIndex C∣3:=(ho.coprime_two_right.pow_right 3).dvd_mul_left.mp hd
  have hVC:V⊓C=D⊓V:=by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.2.1,hx.1⟩
    · intro x hx
      exact ⟨hx.2,hx.1,hVF hx.2⟩
  have hc:Nat.card C∣81:=by
    have hh:=relIndex_mul_relIndex (⊥:Subgroup G) (V⊓C) C bot_le inf_le_right
    rw [relIndex_bot_left,relIndex_bot_left,inf_relIndex_right,hVC,hcap] at hh
    rw [←hh]
    exact Nat.mul_dvd_mul_left 27 h3
  have hi:=central_line_centralizer_relIndex_dvd D W F hW hF hFD hcom hcen
  have hh:=relIndex_mul_relIndex (⊥:Subgroup G) C D bot_le inf_le_left
  rw [relIndex_bot_left,relIndex_bot_left] at hh
  have hiC:C.relIndex D∣3:=by simpa only [C,inf_relIndex_left] using hi
  rw [←hh]
  exact Nat.mul_dvd_mul hc hiC
end Subgroup
