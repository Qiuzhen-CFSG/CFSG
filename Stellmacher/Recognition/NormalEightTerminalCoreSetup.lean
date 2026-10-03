module

public import Stellmacher.Recognition.NormalEightNonnormalSetup
public import Theory.GroupTheory.PGroup.OrderSixteenNormalFourCore

/-!
# Shared geometry for the normal-only terminal alternative

The unique central involution belongs to the chosen normal four even when
only normal elementary subgroups are bounded. The genuine Sylow preimage
of the quotient two-core inherits symplectic type and cyclic center. It also
contains a second core-normal four: otherwise the first would be
characteristic in the core and normal in the entire quotient.

These are the shared inputs for the inside-core fusion and outside-core
affine alternatives of Janko–Thompson (1970), Lemma 4.1, printed p.393.
The quotient and its preimage are the actual objects from
`NormalFourOddCoreSetup`, not abstract groups of the same order.
-/

namespace Stellmacher.Recognition.NormalEightTerminalCoreSetup

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The central involution lies in the chosen normal four under the normal-only bound. -/
public theorem exists_central_involution_in_four
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E) :
    ∃ z : W, orderOf (z : S) = 2 ∧ (z : S) ∈ center S := by
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card'
    (G := omega₁ (center S) (p := 2)) 2 (by rw [hZ])
  have hmem : ((w : center S) : S) ∈ W :=
    omega_one_center_le_normal_four_of_no_normal_eight hno W hW
      (mem_map.mpr ⟨w, w.property, rfl⟩)
  exact ⟨⟨w, hmem⟩, (orderOf_coe (w : center S)).trans ((orderOf_coe w).trans hw),
    (w : center S).property⟩

/-- Symplectic type transfers to the genuine Sylow core preimage. -/
public theorem omegaCorePreimage_symplectic
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal) :
    IsBinarySymplecticType (omegaCorePreimage S) :=
  (NormalEightNonnormalImage.omegaQuotient_pCore_symplectic S hno W hunique hnormal).of_mulEquiv
    (omegaCorePreimageEquiv S).symm

/-- Cyclicity of the core center transfers without an elementary rank bound. -/
public theorem omegaCorePreimage_center_isCyclic
    (S : Sylow 2 G)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (W : Subgroup S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F →
      Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal) :
    IsCyclic (center (omegaCorePreimage S)) :=
  (centerCongr (omegaCorePreimageEquiv S)).isCyclic.mpr
    (NormalEightNonnormalImage.omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal)

/-- The actual core preimage is not a pure Hall factor. -/
public theorem omegaCorePreimage_not_hall (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hnormal : ¬ (fourImage S W).Normal) :
    ¬ IsBinaryHallFactor (omegaCorePreimage S) := by
  intro h
  exact NormalEightNonnormalImage.omegaQuotient_pCore_not_hall hN S hZ W hW hno hnormal
    (h.of_mulEquiv (omegaCorePreimageEquiv S))

/-- Nonnormality in the quotient supplies a second four normalized by the core. -/
public theorem core_distinct_four
    (S : Sylow 2 G) (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W]
    (hW : Nat.card W = 4) (hWH : W ≤ omegaCorePreimage S)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal) :
    ∃ F : Subgroup S, IsElementaryAbelian 2 F ∧ Nat.card F = 4 ∧
      F ≤ omegaCorePreimage S ∧ omegaCorePreimage S ≤ normalizer (F : Set S) ∧ F ≠ W := by
  let H := omegaCorePreimage S
  let K := pCore 2 (OmegaQuotient S)
  let e := omegaCorePreimageEquiv S
  let U := W.subgroupOf H
  let : IsElementaryAbelian 2 U := IsElementaryAbelian.subgroupOf hWH
  let V := U.map e.toMonoidHom
  let : V.Normal := e.normal_map_iff.mpr inferInstance
  let : IsElementaryAbelian 2 V := IsElementaryAbelian.map _
  have hU : Nat.card U = 4 := (Nat.card_congr (subgroupOfEquivOfLe hWH).toEquiv).trans hW
  have hV : Nat.card V = 4 := (card_map_of_injective e.injective).trans hU
  obtain ⟨B, hBn, hBe, hB, hBV⟩ := exists_distinct_normal_four_of_no_ambient_normal_four K
    (omegaQuotient_no_normal_four S W hunique hnormal) V hV
  let : B.Normal := hBn
  let : IsElementaryAbelian 2 B := hBe
  let A := B.map e.symm.toMonoidHom
  let : A.Normal := e.symm.normal_map_iff.mpr hBn
  let : IsElementaryAbelian 2 A := IsElementaryAbelian.map _
  let F := A.map H.subtype
  have hF : Nat.card F = 4 := by
    rw [card_map_of_injective H.subtype_injective, card_map_of_injective e.symm.injective, hB]
  have hFH : F ≤ H := map_subtype_le A
  have hAF : F.subgroupOf H = A := comap_map_eq_self_of_injective H.subtype_injective A
  have hFn : (F.subgroupOf H).Normal := hAF.symm ▸ inferInstance
  refine ⟨F, IsElementaryAbelian.map _, hF, hFH,
    (normal_subgroupOf_iff_le_normalizer hFH).mp hFn, ?_⟩
  intro hFW
  have hAU : A = U := hAF.symm.trans (congrArg (fun B : Subgroup S => B.subgroupOf H) hFW)
  apply hBV
  change B = U.map e.toMonoidHom
  rw [← hAU]
  change B = (B.map e.symm.toMonoidHom).map e.toMonoidHom
  ext b
  simp only [mem_map_equiv, MulEquiv.symm_symm, e.apply_symm_apply]

end Stellmacher.Recognition.NormalEightTerminalCoreSetup
