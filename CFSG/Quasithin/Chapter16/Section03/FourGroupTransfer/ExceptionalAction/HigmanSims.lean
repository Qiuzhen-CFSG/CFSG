module

public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.Contracts
public import CFSG.Quasithin.Chapter16.Section03.FourGroupTransfer.ComponentRestriction
public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-!
# The contradiction from the two HS centralizer layers

A component lies in the actual layer of its overgroup. If that layer is
simple, subnormality forces the component to be the entire layer. Thus
centralizer layers A₈ and A₆ for two elements of E# cannot both contain the
same component L. Their orders are different. This proves the contradiction
once the intrinsic HS action calculation supplies the two elements; it does
not assert the existence of those elements or identify cover centralizers
with quotient centralizers.

Source: Aschbacher–Smith, combined manuscript of 1 March 2004,
16.3.5, printed p.1179 / PDF p.1196.
-/

public section
namespace CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction
open Subgroup Theory.GroupTheory
variable {G : Type*} [Group G]

/-- A component is contained in the actual layer of its overgroup. -/
theorem component_le_layerIn {K H : Subgroup G} (hK : Theory.GroupTheory.IsComponentIn K H) :
    K ≤ ComponentTransfer.layerIn H := by
  intro x hx
  exact ⟨⟨x, hK.1 hx⟩, (le_sSup hK.2 : K.subgroupOf H ≤ componentLayer H) hx, rfl⟩

/-- If the layer is simple, it is the only component. The simplicity here
is of the actual layer, not of a quotient or an unconnected family label. -/
theorem component_eq_layerIn_of_simple {K H : Subgroup G}
    (hK : Theory.GroupTheory.IsComponentIn K H)
    [IsSimpleGroup (ComponentTransfer.layerIn H)] : K = ComponentTransfer.layerIn H := by
  let J := ComponentTransfer.layerIn H
  have hKJ : K ≤ J := component_le_layerIn hK
  have hcomp := Theory.GroupTheory.IsComponentIn.restrict hK hKJ (ComponentTransfer.layerIn_le H)
  have he : K.subgroupOf J = ⊤ := by
    rcases hcomp.2.1.lt_normal with he | ⟨N, hn, hKN, hN⟩
    · exact he
    · rcases hn.eq_bot_or_eq_top with hb | ht
      · have hbot : K.subgroupOf J = ⊥ := le_bot_iff.mp (hb ▸ hKN)
        have hmap := congrArg (Subgroup.map J.subtype) hbot
        have hzero : K = ⊥ := by
          simpa only [map_subgroupOf_eq_of_le hKJ, Subgroup.map_bot] using hmap
        exact (hK.ne_bot hzero).elim
      · exact (hN.ne ht).elim
  exact le_antisymm hKJ (subgroupOf_eq_top.mp he)

/-- Two nonidentity elements with centralizer layers A8 and A6 are
incompatible with the same K being a component for every element of E#. -/
theorem not_components_of_alternating_layers {E K I : Subgroup G}
    (hKI : K ≤ I) (hc : CentralizesAsComponent E K)
    {s t : G} (hs : s ∈ E) (hs1 : s ≠ 1) (ht : t ∈ E) (ht1 : t ≠ 1)
    (h8 : Nonempty (ComponentTransfer.layerIn (I ⊓ involutionCentralizer s) ≃*
      alternatingGroup (Fin 8)))
    (h6 : Nonempty (ComponentTransfer.layerIn (I ⊓ involutionCentralizer t) ≃*
      alternatingGroup (Fin 6))) : False := by
  obtain ⟨e8⟩ := h8
  obtain ⟨e6⟩ := h6
  let : IsSimpleGroup (alternatingGroup (Fin 8)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  let : IsSimpleGroup (ComponentTransfer.layerIn (I ⊓ involutionCentralizer s)) :=
    (MulEquiv.isSimpleGroup_congr e8).mpr inferInstance
  let : IsSimpleGroup (ComponentTransfer.layerIn (I ⊓ involutionCentralizer t)) :=
    (MulEquiv.isSimpleGroup_congr e6).mpr inferInstance
  have hKs := hc s hs hs1
  have hKt := hc t ht ht1
  have hes := component_eq_layerIn_of_simple
    (Theory.GroupTheory.IsComponentIn.restrict hKs (le_inf hKI hKs.1) inf_le_right)
  have het := component_eq_layerIn_of_simple
    (Theory.GroupTheory.IsComponentIn.restrict hKt (le_inf hKI hKt.1) inf_le_right)
  have hc8 : Nat.card K = Nat.card (alternatingGroup (Fin 8)) := by
    rw [hes]
    exact Nat.card_congr e8.toEquiv
  have hc6 : Nat.card K = Nat.card (alternatingGroup (Fin 6)) := by
    rw [het]
    exact Nat.card_congr e6.toEquiv
  rw [nat_card_alternatingGroup, Nat.card_fin] at hc8 hc6
  norm_num [Nat.factorial] at hc8 hc6
  omega

end CFSG.Quasithin.Chapter16.FourGroupTransfer.ExceptionalAction
