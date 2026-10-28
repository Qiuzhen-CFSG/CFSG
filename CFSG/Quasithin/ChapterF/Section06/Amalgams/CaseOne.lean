module

public import CFSG.Quasithin.ChapterF.Section06.Amalgams.LocalStructure
public import Theory.GroupTheory.Amalgam.SymmetricThreePair

/-!
# The first Goldschmidt amalgam

When the common Sylow subgroup has order two, its index-two local cores
are trivial. The given quotient equivalences therefore identify both
vertices with S₃. Conjugating the two involution images gives an amalgam
isomorphism with both inclusion squares commuting and the whole middle
subgroup retained.

Source: Aschbacher–Smith F.6.5(2)(i), printed p.305.
-/

public section

open Subgroup Theory.GroupTheory

namespace CFSG.Quasithin.ChapterF
open Theory.GroupTheory.RankTwoAmalgam
variable {G : Type*} [Group G] [Finite G] {G₁ G₂ : Subgroup G}

 theorem IsGoldschmidtTriple.left_core_eq_bot_of_intersection_card_two
    (h : IsGoldschmidtTriple G₁ G₂) (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 2) :
    pCore 2 G₁ = ⊥ := by
  let Q := (pCore 2 G₁).map G₁.subtype
  let K := Q.subgroupOf (G₁ ⊓ G₂)
  have hi : K.index = 2 := h.left_core_index
  have hc := K.index_mul_card
  rw [hi, hT] at hc
  have hK : Nat.card K = 1 := by omega
  have hQ : Nat.card Q = 1 := by
    rw [← Nat.card_congr (subgroupOfEquivOfLe h.local_twoCore_le_intersection).toEquiv]
    exact hK
  apply Subgroup.card_eq_one.mp
  rw [Nat.card_congr ((pCore 2 G₁).equivMapOfInjective G₁.subtype G₁.subtype_injective).toEquiv]
  exact hQ

 theorem IsGoldschmidtTriple.case_one_of_intersection_card_two
    (h : IsGoldschmidtTriple G₁ G₂) (hT : Nat.card (G₁ ⊓ G₂ : Subgroup G) = 2) :
    Nonempty (RankTwoAmalgam.Iso
      (RankTwoAmalgam.ofSubgroups G₁ (G₁ ⊓ G₂) G₂ inf_le_left inf_le_right)
      RankTwoAmalgam.symmetricThreePair) := by
  obtain ⟨e₁⟩ := h.quotient_left
  obtain ⟨e₂⟩ := h.quotient_right
  let a := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (h.left_core_eq_bot_of_intersection_card_two hT).symm).trans e₁)
  let b := QuotientGroup.quotientBot.symm.trans
    ((QuotientGroup.quotientMulEquivOfEq
      (h.symm.left_core_eq_bot_of_intersection_card_two
        (by simpa only [inf_comm G₂ G₁] using hT)).symm).trans e₂)
  exact RankTwoAmalgam.iso_symmetricThreePair _
    (Subgroup.inclusion_injective inf_le_left)
    (Subgroup.inclusion_injective inf_le_right) hT
    a b
end CFSG.Quasithin.ChapterF
