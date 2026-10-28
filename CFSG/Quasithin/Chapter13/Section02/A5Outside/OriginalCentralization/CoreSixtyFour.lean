module

public import CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization.NonsolvableCores
public import Theory.GroupTheory.PGroup.SmallCentralQuotientDerived

/-!
# The derived subgroup of a small original A₅ core

The same Context places its natural sixteen centrally in the actual two-core.
A core of order at most sixty-four therefore has central quotient of order
at most four, and its derived subgroup is cyclic. The original commuting
pair obstruction can consequently exclude this whole range, without assuming
that the core itself is abelian or lifting an elementary group from a quotient.

Source application: Aschbacher--Smith 13.2.8(1), printed p.880.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
open Section05.A5Source
variable {G : Type*} [Group G] [Finite G]

theorem core_cyclic_derived_of_card_le_sixtyFour
    {T : Sylow 2 G} {K W W₁ W₂ W₃ H : Subgroup G}
    (e : Context T K W W₁ W₂ W₃) (hjoin : K ⊔ (T : Subgroup G) = H)
    (hsmall : Nat.card (pCore 2 H) ≤ 64) :
    IsCyclic (_root_.commutator (pCore 2 H)) := by
  let Q := H.pCoreIn 2
  have hWQ : W ≤ Q := by
    change W ≤ H.pCoreIn 2
    rw [← hjoin]
    exact e.chosen.le_componentCore.trans
      (pCoreIn_mono_of_normalizes le_sup_left (sup_le K.le_normalizer e.normalizes_L))
  have hQW : Q ≤ centralizer (W : Set G) := by
    change H.pCoreIn 2 ≤ _
    rw [← hjoin]
    exact e.chosen.core_centralizes
  have hWZ : W.subgroupOf Q ≤ center Q := by
    intro w hw
    rw [mem_center_iff]
    intro q
    exact Subtype.ext ((hQW q.property) w hw).symm
  have hcenter : 16 ≤ Nat.card (center Q) := by
    have hcard : Nat.card (W.subgroupOf Q) = 16 :=
      (Nat.card_congr (subgroupOfEquivOfLe hWQ).toEquiv).trans e.module_card
    exact hcard ▸ card_le_of_le hWZ
  have hcardQ : Nat.card Q ≤ 64 := by
    change Nat.card (H.pCoreIn 2) ≤ 64
    rwa [pCoreIn, card_map_of_injective H.subtype_injective]
  have hquot : Nat.card (Q ⧸ center Q) ≤ 4 := by
    have hm := (center Q).card_mul_index
    change Nat.card (center Q) * Nat.card (Q ⧸ center Q) = Nat.card Q at hm
    nlinarith
  let := (isPGroup_pCoreIn 2 H).isCyclic_commutator_of_card_center_quotient_le_four hquot
  let a := (pCore 2 H).equivMapOfInjective H.subtype H.subtype_injective
  have hm : (_root_.commutator (pCore 2 H)).map a.toMonoidHom ≤ _root_.commutator Q := by
    rw [map_commutator_eq]
    exact commutator_mono le_top le_top
  let f : _root_.commutator (pCore 2 H) →* _root_.commutator Q :=
    (a.toMonoidHom.comp (_root_.commutator (pCore 2 H)).subtype).codRestrict _
      (fun x => hm (mem_map_of_mem a.toMonoidHom x.property))
  exact isCyclic_of_injective f
    (fun x y h => Subtype.ext (a.injective (congrArg Subtype.val h)))

end CFSG.Quasithin.Chapter13.Section02.A5Outside.OriginalCentralization
