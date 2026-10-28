module

public import Theory.GroupTheory.NormalFourCentralizerSeparation
public import Mathlib.GroupTheory.SpecificGroups.Quaternion

/-!
# Promoting the original quaternion sixteen

If a local involution centralizer has order dividing144, an embedded Q₁₆
is locally Sylow. Its unique involution forces its normalizer into that
centralizer, so local Sylow maximality promotes to the actual overgroup.
The literal subgroup image and quaternion marking are both retained.
Source: Aschbacher, *Sporadic Groups* (1994),45.8,printed pp245–246.
-/

public section
open Subgroup
namespace Subgroup
variable {G:Type*} [Group G] [Finite G]
private theorem quaternion_sixteen_involution (x:QuaternionGroup 4) (hx:orderOf x=2) :
    x=QuaternionGroup.a 4 := by
  have hn:x≠1:=by intro he;simp [he] at hx
  have hs:x^2=1:=by simpa only [hx] using pow_orderOf_eq_one x
  exact (by decide : ∀y:QuaternionGroup 4,y≠1→y^2=1→y=QuaternionGroup.a 4) x hn hs

theorem exists_sylow_of_quaternion_sixteen_local_bound
    (M S:Subgroup G) (z:G) (hz:orderOf z=2)
    (hzS:z∈S) (hSL:S≤M⊓centralizer ({z}:Set G))
    (e:S≃*QuaternionGroup 4)
    (hbound:Nat.card (M⊓centralizer ({z}:Set G):Subgroup G)∣144) :
    ∃P:Sylow 2 M,(P:Subgroup M).map M.subtype=S ∧ Nonempty (P≃*QuaternionGroup 4) := by
  let L:=M⊓centralizer ({z}:Set G)
  have hc:Nat.card S=16:=by rw [Nat.card_congr e.toEquiv,Nat.card_eq_fintype_card,QuaternionGroup.card]
  have he:16*S.relIndex L=Nat.card L:=by
    have hh:=relIndex_mul_relIndex (⊥:Subgroup G) S L bot_le hSL
    simpa only [relIndex_bot_left,hc] using hh
  have hd:S.relIndex L∣9:=by
    have hh:16*S.relIndex L∣16*9:=by rw [he];exact hbound
    exact (Nat.mul_dvd_mul_iff_left (by decide : 0<16)).mp hh
  have hlocal:¬2∣S.relIndex L:=fun hh=>(by decide : ¬2∣9) (hh.trans hd)
  have hp:IsPGroup 2 S:=IsPGroup.of_card (n:=4) hc
  have hcontrol:normalizer (S:Set G)⊓M≤L:=by
    intro n hn
    refine ⟨hn.2,mem_centralizer_singleton_iff.mpr ?_⟩
    let y:S:=⟨n*z*n⁻¹,(mem_normalizer_iff.mp hn.1 z).mp hzS⟩
    have hy:orderOf y=2:=by
      rw [orderOf_mk]
      exact (MulEquiv.orderOf_eq (MulAut.conj n) z).trans hz
    have hze:e ⟨z,hzS⟩=QuaternionGroup.a 4:=
      quaternion_sixteen_involution _ (by rw [MulEquiv.orderOf_eq,orderOf_mk];exact hz)
    have hye:e y=QuaternionGroup.a 4:=quaternion_sixteen_involution _ (by rw [MulEquiv.orderOf_eq];exact hy)
    have hyz:n*z*n⁻¹=z:=congrArg Subtype.val (e.injective (hye.trans hze.symm))
    exact mul_inv_eq_iff_eq_mul.mp hyz
  have hglobal:=not_dvd_relIndex_of_normalizer_inf_le S L M hp (hSL.trans inf_le_left) hlocal hcontrol
  let P:Sylow 2 M:=(hp.comap_subtype : IsPGroup 2 (S.subgroupOf M)).toSylow hglobal
  refine ⟨P,map_subgroupOf_eq_of_le (hSL.trans inf_le_left),?_⟩
  exact ⟨(subgroupOfEquivOfLe (hSL.trans inf_le_left)).trans e⟩
end Subgroup
