module
public import Theory.GroupTheory.NormalFourCentralizer
/-!
# Involution centralizers controlled by a normal four-group

A normal elementary four-group in a two-group makes each of its involution
centralizers have index at most two. When the ambient overgroup centralizer
has half the two-group's order, containment forces equality and index two.
This is the counting step used in Aschbacher--Smith 2.4.29, printed p.545.
-/
public section
open Subgroup
namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

theorem centralizer_eq_sylow_of_normal_four_and_card
    (T M : Subgroup G) (hTM : T ≤ M) (hp : IsPGroup 2 T)
    (W : Subgroup T) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W=4)
    (u : T) (huW : u∈W) (hT : Nat.card T=256)
    (hM : Nat.card (M ⊓ centralizer ({(u:G)} : Set G) : Subgroup G)=128) :
    M ⊓ centralizer ({(u:G)} : Set G)=T ⊓ centralizer ({(u:G)} : Set G) ∧
      (T ⊓ centralizer ({(u:G)} : Set G)).relIndex T=2 := by
  let C := centralizer ({(u:G)} : Set G)
  let Ci := centralizer ({u} : Set T)
  have hmap : Ci.map T.subtype=T ⊓ C := by
    ext x
    constructor
    · rintro ⟨a,ha,rfl⟩
      exact ⟨a.property,mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp ha))⟩
    · rintro ⟨hx,hc⟩
      exact ⟨⟨x,hx⟩,mem_centralizer_singleton_iff.mpr
        (Subtype.ext (mem_centralizer_singleton_iff.mp hc)),rfl⟩
  have hi : Ci.index≤2 :=
    (index_antitone (centralizer_le (Set.singleton_subset_iff.mpr huW))).trans
      (centralizer_index_le_two_of_normal_four hp W hW)
  have hci : Ci.index * Nat.card (T ⊓ C : Subgroup G)=256 := by
    rw [←hmap,card_map_of_injective T.subtype_injective]
    exact Ci.index_mul_card.trans hT
  have hle : T ⊓ C≤M ⊓ C := inf_le_inf_right _ hTM
  have hbound := card_le_of_le hle
  rw [hM] at hbound
  have hc : Nat.card (T ⊓ C : Subgroup G)=128 := by nlinarith
  refine ⟨(eq_of_le_of_card_ge hle (hM.trans hc.symm).le).symm,?_⟩
  have hh := relIndex_mul_relIndex (⊥:Subgroup G) (T ⊓ C) T bot_le inf_le_left
  simp only [relIndex_bot_left,hc,hT] at hh
  nlinarith

end Subgroup
