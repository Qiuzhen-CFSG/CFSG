module
public import Theory.GroupTheory.ElementarySixteenCubic.Data
public import Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair.A6Source

/-!
# The original plane cubic normalizer

The original plane-normalizer A6 quotient supplies the faithful elementary-sixteen input. The local quotient map and the conjugation orbit are transported with both actual subgroup inclusions, preserving the original cubic.
Source: Aschbacher, Sporadic Groups (1994), 45.7(3), printed p.245.
-/

public section
open Subgroup
namespace Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
variable {G:Type*} [Group G] [Finite G] {z:G}

/-- Literal local cubic data in the normalizer of an original source plane. -/
theorem plane_cubic_normalizer_data (P:RootPair z) (h:IsType z)
    (A:Subgroup G) (hA:A≤P.T ∧ IsElementaryAbelian 2 A ∧ Nat.card A=16)
    (U:Subgroup G) (hU:Nat.card U=3) (hUM:U≤normalizer (A:Set G))
    (hfixed:Nat.card (A⊓Subgroup.centralizer (U:Set G):Subgroup G)=4) :
    let M:=normalizer (A:Set G)
    let N:=normalizer (U.subgroupOf M:Set M)
    Nat.card N=72 ∧ pCore 3 N=(U.subgroupOf M).subgroupOf N ∧
    (∃φ:N→*Equiv.Perm (Fin 4),Function.Surjective φ ∧
      φ.ker=(U.subgroupOf M).subgroupOf N) ∧
    ∀W:Sylow 3 N,∀x y:G,x∈A⊓Subgroup.centralizer (U:Set G)→
      y∈A⊓Subgroup.centralizer (U:Set G)→x≠1→y≠1→
      ∃w∈((W:Subgroup N).map N.subtype).map M.subtype,w*x*w⁻¹=y := by
  let M:=normalizer (A:Set G)
  let R:=A.subgroupOf M
  let Um:=U.subgroupOf M
  let :=hA.2.1
  let : IsElementaryAbelian 2 R:=IsElementaryAbelian.subgroupOf A.le_normalizer
  obtain ⟨f,hf,hker⟩:=P.normalizer_A6_surjection h A hA
  let : IsElementaryAbelian 2 f.ker:=hker ▸ (inferInstance:IsElementaryAbelian 2 R)
  have hR:Nat.card f.ker=16:=by
    rw [hker,Nat.card_congr (subgroupOfEquivOfLe A.le_normalizer).toEquiv,hA.2.2]
  have hself:Subgroup.centralizer (f.ker:Set M)≤f.ker:=by
    rw [hker]
    intro x hx
    change (x:G)∈A
    rw [←P.plane_centralizer h A hA]
    intro a ha
    exact congrArg Subtype.val (hx (⟨a,A.le_normalizer ha⟩:M) ha)
  have hUm:Nat.card Um=3:=(Nat.card_congr (subgroupOfEquivOfLe hUM).toEquiv).trans hU
  have hSe:(f.ker⊓Subgroup.centralizer (Um:Set M):Subgroup M)=
      (A⊓Subgroup.centralizer (U:Set G)).subgroupOf M:=by
    rw [hker]
    ext x
    constructor
    · rintro ⟨hxA,hxC⟩
      refine ⟨hxA,?_⟩
      intro u hu
      exact congrArg Subtype.val (hxC (⟨u,hUM hu⟩:M) hu)
    · rintro ⟨hxA,hxC⟩
      exact ⟨hxA,fun u hu=>Subtype.ext (hxC u hu)⟩
  have hF:Nat.card (f.ker⊓Subgroup.centralizer (Um:Set M):Subgroup M)=4:=by
    rw [hSe,Nat.card_congr (subgroupOfEquivOfLe
      (show A⊓Subgroup.centralizer (U:Set G)≤M from inf_le_left.trans A.le_normalizer)).toEquiv]
    exact hfixed
  obtain ⟨hN,hthree,hφ,horb⟩:=ElementarySixteenCubic.normalizer_data f hf hR hself Um hUm hF
  refine ⟨hN,hthree,hφ,?_⟩
  intro W x y hx hy hx1 hy1
  let xm:M:=⟨x,A.le_normalizer hx.1⟩
  let ym:M:=⟨y,A.le_normalizer hy.1⟩
  have hxm:xm∈f.ker⊓Subgroup.centralizer (Um:Set M):=hSe ▸ hx
  have hym:ym∈f.ker⊓Subgroup.centralizer (Um:Set M):=hSe ▸ hy
  obtain ⟨w,hw,hxy⟩:=horb W xm ym hxm hym
    (fun he=>hx1 (congrArg Subtype.val he)) (fun he=>hy1 (congrArg Subtype.val he))
  exact ⟨w,mem_map_of_mem M.subtype hw,congrArg Subtype.val hxy⟩
end Theory.GroupTheory.Recognition.UnitaryFourThree.RootPair
