module
public import CFSG.Quasithin.ChapterC.Section01.BlockStructure.Commutation.CubicSetup
public import GorensteinWalter.NormalKleinFourIndexThree
public import Theory.GroupTheory.GeneralizedFitting.CentralizerViaCComponents

/-!
# The actual group of an alternating-three block

Its short-group quotient has order three, so the two-core equals its
elementary four-group layer. Characteristic two makes that layer self
centralizing. The faithful four-point affine action identifies the group
with A₄, and hence its center is trivial.

Source: Aschbacher--Smith C.1.7--12 and 15.4.7, pp.123--124,1158.
-/

public section
open Subgroup Theory.GroupTheory
namespace CFSG.Quasithin.ChapterC
variable {L : Type*} [Group L]
/-- The defining natural A₃ block is the literal alternating four-group. -/
theorem IsAlternatingBlock.equiv_alternatingFour (h : IsAlternatingBlock L 3) :
    Nonempty (L ≃* alternatingGroup (Fin 4)) := by
  let := h.2.1.finite
  have hc : Nat.card (L ⧸ pCore 2 L) = 3 := by
    obtain ⟨a⟩ := h.2.2.quotient_iso
    rw [Nat.card_congr a.toEquiv,nat_card_alternatingGroup,Nat.card_fin]
    rfl
  have hfour := h.2.1.core_card_four_of_quotient_three hc
  let : IsElementaryAbelian 2 (pCore 2 L) := by
    rw [h.2.1.core_eq_blockU_of_quotient_three hc]
    exact h.2.1.elementary
  let : Nontrivial (pCore 2 L) := by
    apply not_subsingleton_iff_nontrivial.mp
    intro hs
    let := hs
    have hone := Nat.card_of_subsingleton (1 : pCore 2 L)
    omega
  have hklein : IsKleinFour (pCore 2 L) := ⟨hfour,IsElementaryAbelian.exponent_eq_prime⟩
  have hcent : centralizer (pCore 2 L : Set L) = pCore 2 L := by
    apply le_antisymm
    · rw [←h.2.1.fitting]
      exact centralizer_generalizedFitting_le L
    · exact le_centralizer_iff_isMulCommutative.mpr inferInstance
  exact GorensteinWalter.mulEquiv_alternatingGroup_four_of_normal_kleinFour_index_three
    (pCore 2 L) inferInstance hklein hcent hc
/-- In particular an alternating-three block is centerless. -/
theorem IsAlternatingBlock.center_eq_bot (h : IsAlternatingBlock L 3) :
    center L = ⊥ := by
  obtain ⟨a⟩ := h.equiv_alternatingFour
  apply card_eq_one.mp
  rw [Nat.card_congr (centerCongr a).toEquiv,
    alternatingGroup.center_eq_bot (by norm_num : 4 ≤ Nat.card (Fin 4)),card_bot]
end CFSG.Quasithin.ChapterC
