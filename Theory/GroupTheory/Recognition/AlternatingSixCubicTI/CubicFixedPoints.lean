module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.CubicCentralizers
public import Mathlib.GroupTheory.GroupAction.Quotient

/-!
# Cubic fixed points in the actual fifteen-coset action

Sylow conjugacy inside the order-24 stabilizer identifies the fixed cosets
of a cubic subgroup with its ambient normalizer orbit. The literal orders
18 and 6 then give exactly three fixed cosets. The normalizer action and
original coset are retained for the eight-point suborbit construction.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open Subgroup
open scoped Pointwise
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
variable {G:Type*} [Group G] [Finite G]

theorem cubic_conjugate_in (H U V:Subgroup G) (hH:Nat.card H=24)
    (hU:Nat.card U=3) (hV:Nat.card V=3) (hUH:U≤H) (hVH:V≤H):
    ∃a∈H,U.map (MulAut.conj a).toMonoidHom=V := by
  let : Fact (Nat.Prime 3):=⟨by decide⟩
  have hu:Nat.card (U.subgroupOf H)=3^(Nat.card H).factorization 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hUH).toEquiv,hU,hH]
    decide +kernel
  have hv:Nat.card (V.subgroupOf H)=3^(Nat.card H).factorization 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv,hV,hH]
    decide +kernel
  let P:Sylow 3 H:=Sylow.ofCard (U.subgroupOf H) hu
  let Q:Sylow 3 H:=Sylow.ofCard (V.subgroupOf H) hv
  obtain ⟨a,ha⟩:=MulAction.exists_smul_eq H P Q
  have hh:(U.subgroupOf H).map (MulAut.conj a).toMonoidHom=V.subgroupOf H := congrArg Sylow.toSubgroup ha
  refine ⟨a,a.property,?_⟩
  have hm:=congrArg (fun J:Subgroup H=>J.map H.subtype) hh
  rw [map_subgroupOf_eq_of_le hVH] at hm
  calc
    U.map (MulAut.conj (a:G)).toMonoidHom =
        ((U.subgroupOf H).map H.subtype).map (MulAut.conj (a:G)).toMonoidHom := by rw [map_subgroupOf_eq_of_le hUH]
    _ = ((U.subgroupOf H).map (MulAut.conj a).toMonoidHom).map H.subtype := by
      rw [map_map,map_map]
      congr 1
    _ = V := hm

omit [Finite G] in
theorem fixed_coset_iff (H U:Subgroup G) (g:G):
    (g:G⧸H)∈MulAction.fixedPoints U (G⧸H) ↔ U.map (MulAut.conj g⁻¹).toMonoidHom≤H := by
  constructor
  · intro hh x hx
    obtain ⟨u,hu,rfl⟩:=hx
    have he:((u*g:G):G⧸H)=(g:G⧸H):=hh ⟨u,hu⟩
    have hm:=QuotientGroup.eq.mp he.symm
    simpa [MulAut.conj_apply,mul_assoc] using hm
  · intro hh u
    have hm:=hh (mem_map_of_mem (MulAut.conj g⁻¹).toMonoidHom u.property)
    change ((u.val*g:G):G⧸H)=(g:G⧸H)
    symm
    apply QuotientGroup.eq.mpr
    simpa [MulAut.conj_apply,mul_assoc] using hm

theorem cubic_fixedPoints_eq_normalizer_orbit (H U:Subgroup G)
    (hH:Nat.card H=24) (hU:Nat.card U=3) (hUH:U≤H):
    MulAction.fixedPoints U (G⧸H)=MulAction.orbit (normalizer (U:Set G)) ((1:G):G⧸H) := by
  ext x
  induction x using Quotient.inductionOn' with | h g =>
    constructor
    · intro hx
      have hV:= (fixed_coset_iff H U g).mp hx
      have hv:Nat.card (U.map (MulAut.conj g⁻¹).toMonoidHom)=3 := by
        rw [card_map_of_injective (MulAut.conj g⁻¹).injective,hU]
      obtain ⟨a,haH,ha⟩:=cubic_conjugate_in H U _ hH hU hv hUH hV
      have hn:g*a∈normalizer (U:Set G) := by
        rw [mem_normalizer_iff_map_conj_eq]
        calc
          U.map (MulAut.conj (g*a)).toMonoidHom =
              (U.map (MulAut.conj a).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
            rw [map_map]
            congr 1
            ext x
            simp [MulAut.conj_apply,mul_assoc]
          _ = (U.map (MulAut.conj g⁻¹).toMonoidHom).map (MulAut.conj g).toMonoidHom := by rw [ha]
          _ = U := by
            rw [map_map]
            convert U.map_id using 1
            ext x
            simp [MulAut.conj_apply,mul_assoc]
      refine ⟨⟨g*a,hn⟩,?_⟩
      change (((g*a)*1:G):G⧸H)=(g:G⧸H)
      rw [mul_one]
      apply QuotientGroup.eq.mpr
      simpa only [mul_inv_rev,inv_mul_cancel_right] using H.inv_mem haH
    · rintro ⟨n,hn⟩
      rw [←hn]
      change ((n.val*1:G):G⧸H)∈MulAction.fixedPoints U (G⧸H)
      rw [mul_one,fixed_coset_iff]
      have hn':U.map (MulAut.conj n.val⁻¹).toMonoidHom=U :=
        mem_normalizer_iff_map_conj_eq.mp ((normalizer (U:Set G)).inv_mem n.property)
      exact hn'.le.trans hUH

theorem cubic_fixedPoints_card (H U:Subgroup G)
    (hH:Nat.card H=24) (hU:Nat.card U=3) (hUH:U≤H)
    (hN:Nat.card (normalizer (U:Set G))=18)
    (hNH:Nat.card (H⊓normalizer (U:Set G):Subgroup G)=6):
    Nat.card (MulAction.fixedPoints U (G⧸H))=3 := by
  rw [cubic_fixedPoints_eq_normalizer_orbit H U hH hU hUH]
  let N:=normalizer (U:Set G)
  have hs:MulAction.stabilizer N ((1:G):G⧸H)=(H⊓N).subgroupOf N := by
    ext n
    change ((n.val*1:G):G⧸H)=((1:G):G⧸H) ↔ n.val∈H ∧ n.val∈N
    simp [QuotientGroup.eq,n.property]
  have hs6:Nat.card (MulAction.stabilizer N ((1:G):G⧸H))=6 := by
    rw [hs,Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
    exact hNH
  have hh:=Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup N ((1:G):G⧸H))
  rw [Nat.card_prod,hs6,hN] at hh
  change Nat.card (MulAction.orbit N ((1:G):G⧸H))=3
  omega
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
