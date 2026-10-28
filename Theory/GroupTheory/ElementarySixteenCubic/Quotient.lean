module
public import Theory.GroupTheory.SelfCentralizingFourSymmetricFour
public import Theory.GroupTheory.SymmetricThreeTwoCore
public import Theory.GroupTheory.CoprimeQuotientSubgroups
public import Theory.GroupTheory.NormalizedSupCard

/-!
# Local cubic Quotient

A normal fixed four and a normal cubic form the kernel of an S3 quotient. A bound of 24 on the fixed-four centralizer forces that centralizer to be the kernel. Quotienting by the cubic then gives S4 via the faithful normal four-group.
Source: Aschbacher (1994), 45.7(3).
-/

public section
open Subgroup
open scoped IsMulCommutative
namespace ElementarySixteenCubic
variable {N:Type*} [Group N] [Finite N]

theorem symmetric_four_quotient
    (S U:Subgroup N) [S.Normal] [U.Normal] [IsElementaryAbelian 2 S]
    (hS:Nat.card S=4) (hU:Nat.card U=3) (hN:Nat.card N=72)
    (f:N→*Equiv.Perm (Fin 3)) (hf:Function.Surjective f) (hk:f.ker=S⊔U)
    (hC:Nat.card (centralizer (S:Set N))∣24) :
    centralizer (S:Set N)=S⊔U ∧ Nonempty ((N⧸U)≃*Equiv.Perm (Fin 4)) := by
  let C:=centralizer (S:Set N)
  have hdis:Disjoint S U:=disjoint_of_coprime_natCard (by rw [hS,hU];decide)
  have hUC:U≤C:=commutator_eq_bot_iff_le_centralizer.mp
    (commutator_eq_bot_of_disjoint hdis.symm)
  have hSC:S≤C:=by
    intro s hs
    apply mem_centralizer_iff.mpr
    intro t ht
    exact congrArg Subtype.val (mul_comm (⟨t,ht⟩:S) ⟨s,hs⟩)
  have hkerC:f.ker≤C:=hk ▸ sup_le hSC hUC
  have hker:Nat.card f.ker=12:=by
    rw [hk,card_sup_eq_mul_of_normalizes_of_disjoint S U
      (by rw [normalizer_eq_top];exact le_top) hdis,hS,hU]
  let g:=f.comp C.subtype
  have hgker:g.ker=f.ker.subgroupOf C:=rfl
  have hgC:Nat.card g.ker=12:=by
    rw [hgker,Nat.card_congr (subgroupOfEquivOfLe hkerC).toEquiv,hker]
  have hg:=g.ker.card_mul_index
  rw [hgC,index_ker] at hg
  have hgr:g.range=C.map f:=by rw [MonoidHom.range_comp,range_subtype]
  have hd:Nat.card g.range∣2:=by
    have hh:=hC
    rw [← hg] at hh
    exact (Nat.mul_dvd_mul_iff_left (by decide:0<12)).mp hh
  have hp:IsPGroup 2 (C.map f):=by
    rw [←hgr]
    exact IsPGroup.of_card_dvd_pow (n:=1) hd
  let : (C.map f).Normal:=(inferInstance:C.Normal).map f hf
  have hpbot:pCore 2 (Equiv.Perm (Fin 3))=⊥:=by
    have hh:=ker_eq_twoCore_of_surjective_perm_three (MonoidHom.id (Equiv.Perm (Fin 3)))
      Function.surjective_id (by simp only [MonoidHom.ker_id];exact IsPGroup.of_subsingleton 2 _)
    simpa only [MonoidHom.ker_id] using hh.symm
  have hCb:C.map f=⊥:=by
    apply bot_unique
    rw [←hpbot]
    exact le_sSup ⟨inferInstance,hp⟩
  have hCe:C=S⊔U:=le_antisymm (hk ▸ (map_eq_bot_iff C).mp hCb) (sup_le hSC hUC)
  change centralizer (S:Set N)=S⊔U at hCe
  refine ⟨hCe,?_⟩
  let q:=QuotientGroup.mk' U
  let A:=S.map q
  let : A.Normal:=(inferInstance:S.Normal).map q (QuotientGroup.mk'_surjective U)
  let : IsElementaryAbelian 2 A:=IsElementaryAbelian.map q
  have hqcop:Nat.Coprime 2 (Nat.card q.ker):=by
    rw [QuotientGroup.ker_mk',hU];decide
  have hqi:=injective_comp_subtype_of_coprime_ker q hqcop S (IsElementaryAbelian.isPGroup 2 S)
  have hA:Nat.card A=4:=by
    rw [show A=(q.comp S.subtype).range by rw [MonoidHom.range_comp,range_subtype],
      ← Nat.card_congr (MonoidHom.ofInjective hqi).toEquiv,hS]
  have hcent:centralizer (A:Set (N⧸U))≤A:=by
    rw [← map_centralizer_eq_of_surjective_coprime q (QuotientGroup.mk'_surjective U)
      hqcop S (IsElementaryAbelian.isPGroup 2 S),hCe,Subgroup.map_sup,
      QuotientGroup.map_mk'_self,sup_bot_eq]
  have hcard:Nat.card (N⧸U)=24:=by
    have hh:=card_eq_card_quotient_mul_card_subgroup U
    rw [hN,hU] at hh
    omega
  exact mulEquiv_perm_four_of_selfCentralizing_four_card_twentyfour A hA hcent hcard
end ElementarySixteenCubic
