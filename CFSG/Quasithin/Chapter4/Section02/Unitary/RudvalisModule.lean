module
public import CFSG.Quasithin.Chapter4.Section02.Unitary.OrdinaryAction
public import Theory.SpecificGroups.Rudvalis.Model.TwoRankSix

/-!
# The full ordinary module image in the Rudvalis row

The unitary action gives a lower bound of 64 for the elementary module image
in the actual central quotient. The intrinsic Rudvalis two-rank bound gives
the matching upper bound. This identifies the order of the full image without
assuming a block recognition or replacing the component by an unmarked model.
The original chosen-module application is OriginalOddNormalizer.MarkedAction.
Source: Aschbacher–Smith C.3.1(9),4.2.13, pp.149–151,611–612.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC.HypothesisC28
variable {G : Type*} [Group G] [Finite G] {H M L R V : Subgroup G}
local notation "D" => commutator (Atlas.G2.Model (ZMod 2))

/-- The literal original module image has order 64 in the Rudvalis row. -/
theorem unitary_ordinary_rudvalis_module_card
    (h : HypothesisC28 KnownSimple.IsKnownSimple H M L R V)
    (a : L ⧸ pCore 2 L ≃* D) (K : Subgroup H) (hK : IsComponent H K)
    (e : K ⧸ center K ≃* Rudvalis.Model) :
    Nat.card (((V.subgroupOf H).subgroupOf K).map (QuotientGroup.mk' (center K))) = 64 := by
  obtain ⟨_,hel,_,_,hcard,_⟩ := h.unitary_ordinary_module_image a K hK
  let E := ((V.subgroupOf H).subgroupOf K).map (QuotientGroup.mk' (center K))
  let := hel
  let : IsElementaryAbelian 2 (E.map e.toMonoidHom) := IsElementaryAbelian.map _
  have hu := (primeRank_le_iff_elementary_card_le Rudvalis.Model).mp
    Rudvalis.primeRank_le_six (E.map e.toMonoidHom) inferInstance
  rw [card_map_of_injective e.injective] at hu
  exact Nat.le_antisymm hu hcard

end CFSG.Quasithin.ChapterC.HypothesisC28
