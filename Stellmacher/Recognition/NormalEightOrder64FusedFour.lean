module

public import Theory.GroupTheory.PGroup.FusedFourCharacteristic
public import Theory.SpecificGroups.C4SquareSignSwap
public import Theory.GroupTheory.PGroup.OrderThirtyTwoCharacteristicExtraction
public import Theory.GroupTheory.PGroup.InverterCoreIndexTwoEight

/-!
# Excluding a fused normal four at order sixty-four

The centralizer of the unique fused normal four has order 32, center of
order at least four, no characteristic subgroup of order two, and no
characteristic elementary subgroup of order at least eight. These facts
reduce the exclusion to two intrinsic statements: recognition of this
order-32 group as the generalized dihedral group on `C₄ × C₄`, and the
existence of a normal elementary eight in an index-two extension of that
group with a unique central involution.

The latter extension condition matters: the generalized dihedral group
itself satisfies all the centralizer conditions. The intrinsic recognition
and extension theorems supply a normal elementary eight in the Sylow subgroup,
contradicting the assumed absence of such subgroups. Ambient simplicity and
local solvability are unnecessary for this route.

Source: Janko–Thompson, Math. Z. 113 (1970), results 1.3–1.4, printed
p.386, and the index-two paragraph on p.389. The two small-order intrinsic
steps replace the full recognition alternatives for this specialization.
-/

namespace Stellmacher.Recognition.NormalEightOrder64FusedFour

open Subgroup

variable {G : Type*} [Group G] [Finite G]

/-- The four-centralizer has order thirty-two and contains a central four. -/
public theorem centralizer_card_and_center_bound
    (S : Sylow 2 G) (hS : Nat.card S = 64)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) :
    (centralizer (W : Set S)).index = 2 ∧
      Nat.card (centralizer (W : Set S)) = 32 ∧
      4 ≤ Nat.card (center (centralizer (W : Set S))) := by
  let C := centralizer (W : Set S)
  have hi : C.index = 2 :=
    centralizer_index_eq_two_of_normal_four_of_card_omega_one_center_eq_two
      S.isPGroup' hZ W hW
  have hc : Nat.card C = 32 := by
    have hh := C.card_mul_index
    rw [hi, hS] at hh
    omega
  have hWC : W ≤ C := le_centralizer W
  have hWZ : W.subgroupOf C ≤ center C := by
    intro w hw
    apply mem_center_iff.mpr
    intro c
    exact Subtype.ext (c.property w hw).symm
  refine ⟨hi, hc, ?_⟩
  have hh := card_le_of_le hWZ
  rwa [Nat.card_congr (subgroupOfEquivOfLe hWC).toEquiv, hW] at hh

/-- Local data for recognizing the centralizer, using the normal-only bound. -/
public theorem centralizer_recognition_data
    (S : Sylow 2 G) (hS : Nat.card S = 64)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    Nat.card (centralizer (W : Set S)) = 32 ∧
      4 ≤ Nat.card (center (centralizer (W : Set S))) ∧
      (∀ K : Subgroup (centralizer (W : Set S)), K.Characteristic → Nat.card K ≠ 2) ∧
      (∀ K : Subgroup (centralizer (W : Set S)), K.Characteristic →
        IsElementaryAbelian 2 K → Nat.card K < 8) := by
  obtain ⟨_, hc, hz⟩ := centralizer_card_and_center_bound S hS hZ W hW
  refine ⟨hc, hz, ?_, ?_⟩
  · intro K hK
    let : K.Characteristic := hK
    exact S.centralizer_fused_four_no_characteristic_two hno hZ W hW hunique hfused K
  · intro K hK he
    let : K.Characteristic := hK
    let : IsElementaryAbelian 2 K := he
    exact S.centralizer_four_characteristic_elementary_card_lt_eight hno W K

/-- Recognition of the order-32 centralizer and the intrinsic extension
lemma together exclude fusion at order sixty-four. This interface separates
the two intrinsic inputs from the ambient fusion argument. -/
public theorem false_of_recognition_and_extension
    (S : Sylow 2 G) (hS : Nat.card S = 64)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G))
    (hrecognition :
      Nat.card (centralizer (W : Set S)) = 32 →
      4 ≤ Nat.card (center (centralizer (W : Set S))) →
      (∀ K : Subgroup (centralizer (W : Set S)), K.Characteristic → Nat.card K ≠ 2) →
      (∀ K : Subgroup (centralizer (W : Set S)), K.Characteristic →
        IsElementaryAbelian 2 K → Nat.card K < 8) →
      Nonempty (centralizer (W : Set S) ≃* C4SquareSignSwap.inverterCore))
    (hextension : ∀ C : Subgroup S, C.index = 2 →
      Nonempty (C ≃* C4SquareSignSwap.inverterCore) →
      ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E) :
    False := by
  obtain ⟨hc, hz, hchar, helem⟩ :=
    centralizer_recognition_data S hS hZ hno W hW hunique hfused
  have hi := (centralizer_card_and_center_bound S hS hZ W hW).1
  exact hno (hextension _ hi (hrecognition hc hz hchar helem))

/-- A unique normal elementary four cannot have all its nonidentity elements
fused in the ambient group when the Sylow subgroup has order sixty-four,
central omega of order two, and no normal elementary eight. -/
public theorem false_of_fused_normal_four
    (S : Sylow 2 G) (hS : Nat.card S = 64)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hfused : ∀ x y : W, x ≠ 1 → y ≠ 1 → IsConj ((x : S) : G) ((y : S) : G)) :
    False := by
  exact false_of_recognition_and_extension S hS hZ hno W hW hunique hfused
    OrderThirtyTwoCharacteristicExtraction.recognition
    (exists_normal_elementary_eight_of_inverterCore_index_two hZ)

end Stellmacher.Recognition.NormalEightOrder64FusedFour
