module

public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicInsideFusion
public import Stellmacher.Recognition.NormalEightNonnormalNoncyclicRotationSetup
public import Theory.GroupTheory.PGroup.LargeHallIndexedRotations
public import Theory.GroupTheory.PGroup.LargeHallRotationCenter

/-!
# Index and fusion for the intrinsic noncyclic rotation product

The quotient-core closure of the elements with nontrivial fourth power is the
product of the extraspecial eight with the characteristic cyclic rotations of
the Hall tail.  The rotations have index two in the tail, so the intrinsic
product has index two in the quotient core.  Its pullback to the original
Sylow group consequently has index four.  The ambient involution fusion is
provided by the local quotient action in `NormalEightNonnormalNoncyclicInsideFusion`.
-/

namespace Stellmacher.Recognition.NormalEightNonnormalImage
open Subgroup NormalFourCentralOmegaTwo
variable {G : Type*} [Group G] [Finite G]

/-- The intrinsic rotation product has index four in the original Sylow group. -/
public theorem noncyclicRotationPreimage_index_eq_four
    (_hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (_hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (_hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (hi : (omegaCorePreimage S).index = 2) :
    (noncyclicRotationPreimage S).index = 4 := by
  let P := pCore 2 (OmegaQuotient S)
  let M : Subgroup P := closure {x : P | x ^ 4 ≠ 1}
  let : IsCyclic (center P) :=
    omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  obtain ⟨R, hRc, hRcyc, hRi, hRcard, houtD, _hRcenter⟩ :=
    hD.exists_characteristic_large_rotation_index_two
      (pCore_isPGroup.to_subgroup D) hn hlarge
  let : R.Characteristic := hRc
  let : IsCyclic R := hRcyc
  let C : Subgroup P := R.map D.subtype
  let : IsCyclic C :=
    (R.equivMapOfInjective D.subtype D.subtype_injective).isCyclic.mp inferInstance
  let : C.Normal := ConjAct.normal_of_characteristic_of_normal
  have hCcard : Nat.card C = Nat.card R := by
    exact card_map_of_injective D.subtype_injective
  have hC8 : 8 ≤ Nat.card C := hCcard ▸ hRcard
  have hBD : C ≤ D := map_subtype_le R
  have hA4 (a : P) (ha : a ∈ B) : a ^ 4 = (1 : P) := by
    exact congrArg Subtype.val (IsExtraspecial.pow_four_eq_one (⟨a, ha⟩ : B))
  have hout (d : P) (hd : d ∈ D) (hdC : d ∉ C) : d ^ 4 = (1 : P) := by
    exact congrArg Subtype.val (houtD ⟨d, hd⟩ (fun hh => hdC ⟨⟨d, hd⟩, hh, rfl⟩))
  have hM : B ⊔ C = M := by
    exact sup_eq_closure_nontrivial_fourth_powers B D C hA4 hc hg hBD hC8 hout
  have hCne : C ≠ ⊥ := by
    intro h
    have : Nat.card C = 1 := by simp [h]
    omega
  obtain ⟨_hcycM, hMindexCenter, hMcenterCard⟩ :=
    cyclic_center_index_four_of_extraspecial_cyclic_product
      pCore_isPGroup B C hB hCne (hBD.trans hc)
  have hPcard : Nat.card P * 2 = Nat.card B * Nat.card D :=
    card_mul_two_eq_of_extraspecial_of_cyclic_center
      pCore_isPGroup B D (by
        intro h
        have : Nat.card D = 1 := by simp [h]
        omega) hc hg
  have hDcard : Nat.card D = 2 * Nat.card R := by
    have hh := R.index_mul_card
    rw [hRi] at hh
    omega
  have hMcard : Nat.card M = 4 * Nat.card R := by
    have hh := (center M).card_mul_index
    have hcenterCard : Nat.card (center M) = Nat.card C := by
      rw [← hM]
      exact hMcenterCard
    have hcenterIndex : (center M).index = 4 := by
      rw [← hM]
      exact hMindexCenter
    rw [hcenterCard, hcenterIndex, hCcard] at hh
    omega
  have hPtwoM : Nat.card P = 2 * Nat.card M := by
    rw [hB, hDcard] at hPcard
    rw [hMcard]
    omega
  have hMindex : M.index = 2 := by
    have hh := M.index_mul_card
    rw [hPtwoM] at hh
    have hp : 0 < Nat.card M := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hp hh
  rw [noncyclicRotationPreimage_eq_map_quotient_core]
  rw [← map_map]
  rw [index_map_subtype, index_map_of_bijective (omegaCorePreimageEquiv S).symm.bijective]
  rw [hMindex, hi]

/-- The large-tail hypotheses give both index four and inside involution fusion. -/
public theorem noncyclicRotationPreimage_index_four_and_involution_fusion
    (hN : IsNTwoGroup G) (S : Sylow 2 G)
    (hno : ¬ ∃ U : Subgroup S, U.Normal ∧ IsElementaryAbelian 2 U ∧ 8 ≤ Nat.card U)
    (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (B D : Subgroup (pCore 2 (OmegaQuotient S))) [B.Normal] [D.Normal]
    [IsExtraspecial 2 B] (hB : Nat.card B = 8)
    (hD : IsBinaryHallFactor D) (hn : ¬ IsCyclic D)
    (hc : D ≤ centralizer (B : Set (pCore 2 (OmegaQuotient S))))
    (hg : B ⊔ D = ⊤) (hlarge : 16 ≤ Nat.card D)
    (hi : (omegaCorePreimage S).index = 2)
    (u : S) (hu : u ∈ noncyclicRotationPreimage S) (hu2 : orderOf u = 2) :
    (noncyclicRotationPreimage S).index = 4 ∧
      ∃ w : S, w ∈ W ∧ IsConj (u : G) (w : G) := by
  refine ⟨noncyclicRotationPreimage_index_eq_four hN S hno hZ W hW hunique hnormal
    B D hB hD hn hc hg hlarge hi, ?_⟩
  exact exists_isConj_mem_four_of_mem_noncyclicRotationPreimage
    hN S hno hZ W hW hunique hnormal B D hB hD hn hc hg hlarge u hu hu2

end Stellmacher.Recognition.NormalEightNonnormalImage
