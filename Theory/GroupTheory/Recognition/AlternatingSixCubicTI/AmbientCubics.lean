module

public import Theory.GroupTheory.Recognition.AlternatingSixCubicTI.CubicCentralizers

/-!
# Normalizer order for every original cubic subgroup

Sylow conjugacy moves a cubic subgroup into the specified elementary nine. Its normalizer calculation is then transported back by the same actual inner automorphism.

Source: Aschbacher, *Sporadic Groups* (1994), Exercise 2(2), printed p.249.
-/

@[expose] public section

open Subgroup
namespace Theory.GroupTheory.Recognition.AlternatingSixCubicTI
variable {G:Type*} [Group G] [Finite G]

theorem ambient_cubic_normalizer_card
    (P:Sylow 3 G) [IsElementaryAbelian 3 P] (hP:Nat.card (P:Subgroup G)=9)
    (hTI:∀g:G,(P:Subgroup G)⊓(P:Subgroup G).map (MulAut.conj g).toMonoidHom=⊥ ∨
      (P:Subgroup G).map (MulAut.conj g).toMonoidHom=P)
    (hC:centralizer (P:Set G)≤P)
    (eN:(normalizer ((P:Subgroup G):Set G)⧸(P:Subgroup G).subgroupOf
      (normalizer ((P:Subgroup G):Set G)))≃*Multiplicative (ZMod 4))
    (U:Subgroup G) (hU:Nat.card U=3):Nat.card (normalizer (U:Set G))=18 := by
  let : Fact (Nat.Prime 3):=⟨by decide⟩
  have hp:IsPGroup 3 U:=IsPGroup.of_card (n:=1) (by simpa using hU)
  obtain ⟨R,hUR⟩:=hp.exists_le_sylow
  obtain ⟨g,hg⟩:=MulAction.exists_smul_eq G R P
  have hmap:(R:Subgroup G).map (MulAut.conj g).toMonoidHom=P := congrArg Sylow.toSubgroup hg
  have hUP:(U.map (MulAut.conj g).toMonoidHom)≤P := (map_mono hUR).trans_eq hmap
  have hcU:Nat.card (U.map (MulAut.conj g).toMonoidHom)=3 := by
    rw [card_map_of_injective (MulAut.conj g).injective,hU]
  have hh:=cubic_normalizer_card P hP hTI hC eN _ hcU hUP
  rw [←map_normalizer_eq_of_bijective U (MulAut.conj g).bijective,
    card_map_of_injective (MulAut.conj g).injective] at hh
  exact hh
end Theory.GroupTheory.Recognition.AlternatingSixCubicTI
