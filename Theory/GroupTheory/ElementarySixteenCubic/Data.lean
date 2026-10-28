module
public import Theory.GroupTheory.ElementarySixteenCubic.Structure
public import Theory.GroupTheory.ElementarySixteenCubic.Transitivity
public import Theory.GroupTheory.ElementarySixteenCubic.ThreeCore

/-!
# Marked local cubic normalizer data

The same A6 quotient and original cubic give the normalizer order, the exact
S4 quotient map, its three-core, and the actual conjugation orbit of every
Sylow three-subgroup on the fixed four. All subgroup maps are retained.
Source: Aschbacher (1994), 45.7(3).
-/

public section
open Subgroup
namespace ElementarySixteenCubic
variable {G:Type*} [Group G] [Finite G]

theorem normalizer_data
    (f:G→*alternatingGroup (Fin 6)) (hf:Function.Surjective f)
    [IsElementaryAbelian 2 f.ker] (hR:Nat.card f.ker=16)
    (hself:centralizer (f.ker:Set G)≤f.ker)
    (U:Subgroup G) (hU:Nat.card U=3)
    (hS:Nat.card (f.ker⊓centralizer (U:Set G):Subgroup G)=4) :
    let N:=normalizer (U:Set G)
    let S:=f.ker⊓centralizer (U:Set G)
    Nat.card N=72 ∧ pCore 3 N=U.subgroupOf N ∧
    (∃φ:N→*Equiv.Perm (Fin 4),Function.Surjective φ ∧ φ.ker=U.subgroupOf N) ∧
    ∀W:Sylow 3 N,∀x y:G,x∈S→y∈S→x≠1→y≠1→
      ∃w∈(W:Subgroup N).map N.subtype,w*x*w⁻¹=y := by
  let N:=normalizer (U:Set G)
  let S:=f.ker⊓centralizer (U:Set G)
  let Sn:=S.subgroupOf N
  let Un:=U.subgroupOf N
  have hSN:S≤N:=inf_le_right.trans (centralizer_le_normalizer _)
  have hRN:=kernel_inf_normalizer f hR U hU
  have hSn:Sn=f.ker.subgroupOf N:=by
    ext x
    exact ⟨fun hx=>hx.1,fun hx=>hRN.le ⟨hx,x.property⟩⟩
  let : Sn.Normal:=hSn ▸ (inferInstance:(f.ker.subgroupOf N).Normal)
  let : IsElementaryAbelian 2 S:=IsElementaryAbelian.of_injective
    (inclusion (show S≤f.ker from inf_le_left)) (inclusion_injective _)
  let : IsElementaryAbelian 2 Sn:=IsElementaryAbelian.subgroupOf hSN
  have hSnC:Nat.card Sn=4:=(Nat.card_congr (subgroupOfEquivOfLe hSN).toEquiv).trans hS
  have hUnC:Nat.card Un=3:=(Nat.card_congr (subgroupOfEquivOfLe U.le_normalizer).toEquiv).trans hU
  obtain ⟨hN,hcent,⟨e⟩⟩:=normalizer_structure f hf hR hself U hU hS
  have hthree:pCore 3 N=Un:=threeCore_eq_cubic Sn Un hSnC hUnC hcent
  let q:=QuotientGroup.mk' Un
  let φ:=e.toMonoidHom.comp q
  have hφ:Function.Surjective φ:=e.surjective.comp (QuotientGroup.mk'_surjective Un)
  have hφker:φ.ker=Un:=by
    ext x
    change e (q x)=1 ↔ x∈Un
    rw [e.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff x
  refine ⟨hN,hthree,⟨φ,hφ,hφker⟩,?_⟩
  intro W x y hx hy hx1 hy1
  have hC:Nat.card (centralizer (Sn:Set N))=12:=by
    rw [hcent,card_sup_eq_mul_of_normalizes_of_disjoint Sn Un
      (by rw [normalizer_eq_top];exact le_top)
      (disjoint_of_coprime_natCard (by rw [hSnC,hUnC];decide)),hSnC,hUnC]
  let xn:Sn:=⟨⟨x,hSN hx⟩,hx⟩
  let yn:Sn:=⟨⟨y,hSN hy⟩,hy⟩
  obtain ⟨w,hw⟩:=sylow_three_transitive_on_four Sn hSnC hN hC W xn yn
    (fun he=>hx1 (congrArg (fun v:Sn=>((v:N):G)) he))
    (fun he=>hy1 (congrArg (fun v:Sn=>((v:N):G)) he))
  exact ⟨((w:N):G),mem_map_of_mem N.subtype w.property,congrArg Subtype.val hw⟩
end ElementarySixteenCubic
