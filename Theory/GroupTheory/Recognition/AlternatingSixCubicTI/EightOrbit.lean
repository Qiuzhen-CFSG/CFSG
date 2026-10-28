module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.SymmetricAction
public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.MappedCubics
public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.InvolutionOrbit
public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.ThreePointOrbit
public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.AmbientCubics

/-!
# The eight-point suborbit in the original coset action

The cubic normalizer is transitive on three fixed cosets, with nonnormal
stabilizer of order six. Its stabilizer therefore interchanges the two
nonbase cosets. Two distinct cubics in S4 generate its four-core, whose
unique fixed coset is the base. Consequently the full symmetric stabilizer
of either chosen nonbase coset has order three, giving an orbit of size eight.
The final theorem derives every local input from the original TI Sylow data.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
open Theory.SpecificGroups.SymmetricSix.DuadCalculation
variable {G:Type*} [Group G] [Finite G]

theorem mapped_core_fixedPoints (f:Four→*G) (hf:Function.Injective f) (hi:f.range.index=15)
    (hc:∀x:G,orderOf x=3→Nat.card (centralizer ({x}:Set G))=9):
    MulAction.fixedPoints (core.map f) (G⧸f.range)={((1:G):G⧸f.range)} := by
  have hh:=symmetricCore_fixedPoints f.range (MonoidHom.ofInjective hf).symm hi hc
  have he:symmetricCore f.range=core.map f := symmetricCore_eq f.range (MonoidHom.ofInjective hf).symm
  rwa [he] at hh

theorem exists_eight_orbit (f:Four→*G) (hf:Function.Injective f) (hi:f.range.index=15)
    (hc:∀x:G,orderOf x=3→Nat.card (centralizer ({x}:Set G))=9)
    (hNU:Nat.card (normalizer (NativeFour.cubic.map f:Set G))=18):
    ∃q:G⧸f.range,q≠((1:G):G⧸f.range) ∧
      q∈MulAction.fixedPoints (NativeFour.cubic.map f) (G⧸f.range) ∧
      Nat.card (MulAction.orbit f.range q)=8 := by
  classical
  let H:=f.range
  let U:=NativeFour.cubic.map f
  let N:=normalizer (U:Set G)
  let o:G⧸H:=(1:G)
  let O:=MulAction.orbit N o
  let a:O:=⟨o,MulAction.mem_orbit_self o⟩
  have hH:Nat.card H=24 := by
    rw [←Nat.card_congr (MonoidHom.ofInjective hf).toEquiv]
    simp only [Nat.card_eq_fintype_card,Fintype.card_perm,Fintype.card_fin]
    decide
  have hU:Nat.card U=3 := by rw [card_map_of_injective hf,NativeFour.cubic_card]
  have hUH:U≤H:=map_le_range _ _
  have hNH:Nat.card (H⊓N:Subgroup G)=6:=mapped_cubic_normalizer_card f hf
  have hfixEq:MulAction.fixedPoints U (G⧸H)=MulAction.orbit N o :=
    cubic_fixedPoints_eq_normalizer_orbit H U hH hU hUH
  have hO:Nat.card O=3 := by
    change Nat.card (MulAction.orbit N o)=3
    rw [←hfixEq]
    exact cubic_fixedPoints_card H U hH hU hUH hNU hNH
  let : Nontrivial O:=Finite.one_lt_card_iff_nontrivial.mp (by rw [hO]; decide)
  obtain ⟨b,hb⟩:=exists_ne a
  have hbo:b.val≠o:=fun hh=>hb (Subtype.ext hh)
  have hbf:b.val∈MulAction.fixedPoints U (G⧸H):=hfixEq ▸ b.property
  have hs:MulAction.stabilizer N a=(H⊓N).subgroupOf N := by
    ext n
    change n • a=a ↔ n.val∈H ∧ n.val∈N
    rw [Subtype.ext_iff]
    change ((n.val*1:G):G⧸H)=((1:G):G⧸H) ↔ n.val∈H ∧ n.val∈N
    simp [QuotientGroup.eq,n.property]
  have hs6:Nat.card (MulAction.stabilizer N a)=6 := by
    rw [hs,Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv,hNH]
  have hsn:¬(MulAction.stabilizer N a).Normal := by
    intro hn
    have hn':((H⊓N).subgroupOf N).Normal:=hs ▸ hn
    exact eighteen_not_normalizes_six hc N (H⊓N) hNU hNH inf_le_right
      ((normal_subgroupOf_iff_le_normalizer inf_le_right).mp hn')
  have h3:=three_point_stabilizer_intersection_card hO a hsn hs6 b hb
  have hHQ:(H⊓MulAction.stabilizer G b.val:Subgroup G)≤N := by
    intro g hg
    have hgq:g • b.val=b.val:=hg.2
    let L:=U.map (MulAut.conj g).toMonoidHom
    have hL:Nat.card L=3 := by rw [card_map_of_injective (MulAut.conj g).injective,hU]
    have hLH:L≤H := (map_mono hUH).trans_eq
      (mem_normalizer_iff_map_conj_eq.mp (H.le_normalizer hg.1))
    have hUS:U≤MulAction.stabilizer G b.val := fun u hu=>hbf ⟨u,hu⟩
    have hLS:L≤MulAction.stabilizer G b.val := by
      have hh:=map_mono (f:=(MulAut.conj g).toMonoidHom) hUS
      rw [←MulAction.stabilizer_smul_eq_stabilizer_map_conj g b.val,hgq] at hh
      exact hh
    have he:L=U := by
      by_contra hne
      have hE:core.map f≤MulAction.stabilizer G b.val :=
        (mapped_core_le_sup_cubics f hf U L hU hL hUH hLH (Ne.symm hne)).trans (sup_le hUS hLS)
      have hh:b.val∈MulAction.fixedPoints (core.map f) (G⧸H):=fun x=>hE x.property
      rw [mapped_core_fixedPoints f hf hi hc,Set.mem_singleton_iff] at hh
      exact hbo hh
    exact mem_normalizer_iff_map_conj_eq.mpr he
  have he:MulAction.stabilizer N a⊓MulAction.stabilizer N b=
      (H⊓MulAction.stabilizer G b.val).subgroupOf N := by
    rw [hs]
    ext n
    change (n.val∈H ∧ n.val∈N) ∧ n • b=b ↔ n.val∈H ∧ n.val • b.val=b.val
    rw [Subtype.ext_iff]
    simp only [n.property,and_true]
    rfl
  rw [he,Nat.card_congr (subgroupOfEquivOfLe hHQ).toEquiv] at h3
  have hHb:MulAction.stabilizer H b.val=(H⊓MulAction.stabilizer G b.val).subgroupOf H := by
    ext x
    change x.val • b.val=b.val ↔ x.val∈H ∧ x.val • b.val=b.val
    simp only [x.property,true_and]
  have hHb3:Nat.card (MulAction.stabilizer H b.val)=3 := by
    rw [hHb,Nat.card_congr (subgroupOfEquivOfLe inf_le_left).toEquiv,h3]
  have ho:=Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H b.val)
  rw [Nat.card_prod,hHb3,hH] at ho
  have horbit:Nat.card (MulAction.orbit H b.val)=8 := by omega
  exact ⟨b.val,hbo,hbf,horbit⟩

theorem exists_eight_orbit_of_ti (f:Four→*G) (hf:Function.Injective f) (hi:f.range.index=15)
    (P:Sylow 3 G) [IsElementaryAbelian 3 P] (hP:Nat.card (P:Subgroup G)=9)
    (hTI:∀g:G,(P:Subgroup G)⊓(P:Subgroup G).map (MulAut.conj g).toMonoidHom=⊥ ∨
      (P:Subgroup G).map (MulAut.conj g).toMonoidHom=P)
    (hC:centralizer (P:Set G)≤P)
    (eN:(normalizer ((P:Subgroup G):Set G)⧸(P:Subgroup G).subgroupOf
      (normalizer ((P:Subgroup G):Set G)))≃*Multiplicative (ZMod 4)):
    ∃q:G⧸f.range,q≠((1:G):G⧸f.range) ∧
      q∈MulAction.fixedPoints (NativeFour.cubic.map f) (G⧸f.range) ∧
      Nat.card (MulAction.orbit f.range q)=8 := by
  apply exists_eight_orbit f hf hi (cubic_centralizer_card P hP hTI hC eN)
  apply ambient_cubic_normalizer_card P hP hTI hC eN
  rw [card_map_of_injective hf,NativeFour.cubic_card]
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
