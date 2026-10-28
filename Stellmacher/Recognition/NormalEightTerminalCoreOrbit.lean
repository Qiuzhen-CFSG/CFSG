module

public import Stellmacher.Recognition.NormalEightTerminalCoreSetup
public import Theory.GroupTheory.PGroup.OrderSixteenCoreOrbit

/-!
# Order-sixteen core geometry under the normal-only elementary bound

The actual quotient two-core has symplectic type and cyclic center and is not
a Hall factor. Its order sixteen therefore forces a center of order four and
elementary rank at most two. These conclusions transfer to its genuine Sylow
preimage. The intrinsic three-four orbit calculation then fuses every core
involution into the prescribed barred four.

Source: Janko–Thompson, Math. Z. 113 (1970), §4, printed p.393. Only normal
elementary subgroups of the Sylow are bounded in the hypotheses.
-/

namespace Stellmacher.Recognition.NormalEightTerminalCoreOrbit

open Subgroup NormalFourCentralOmegaTwo

variable {G : Type*} [Group G] [Finite G]

/-- The center of the actual quotient core has order four. -/
public theorem omegaQuotient_pCore_center_card (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16) :
    Nat.card (center (pCore 2 (OmegaQuotient S))) = 4 := by
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    NormalEightNonnormalImage.omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  exact IsBinarySymplecticType.center_card_eq_four_of_card_sixteen pCore_isPGroup hcore
    (NormalEightNonnormalImage.omegaQuotient_pCore_symplectic S hno W hunique hnormal)
    (NormalEightNonnormalImage.omegaQuotient_pCore_not_hall hN S hZ W hW hno hnormal)

/-- The center of the genuine Sylow core preimage has order four. -/
public theorem omegaCorePreimage_center_card (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16) :
    Nat.card (center (omegaCorePreimage S)) = 4 :=
  (Nat.card_congr (centerCongr (omegaCorePreimageEquiv S)).toEquiv).trans
    (omegaQuotient_pCore_center_card hN S hZ W hW hno hunique hnormal hcore)

/-- Every elementary subgroup inside the order-sixteen core has order below eight. -/
public theorem omegaCorePreimage_elementary_card_lt_eight (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16) :
    ∀ U : Subgroup (omegaCorePreimage S), IsElementaryAbelian 2 U → Nat.card U < 8 := by
  let : IsCyclic (center (omegaCorePreimage S)) :=
    NormalEightTerminalCoreSetup.omegaCorePreimage_center_isCyclic S hno W hunique hnormal
  exact elementary_card_lt_eight_of_card_sixteen_center_four
    ((card_omegaCorePreimage S).trans hcore)
    (omegaCorePreimage_center_card hN S hZ W hW hno hunique hnormal hcore)

/-- Every involution lying over the core has quotient orbit meeting the prescribed four. -/
public theorem core_involution_quotient_orbit (hN : IsNTwoGroup G)
    (S : Sylow 2 G) (hZ : Nat.card (omega₁ (center S) (p := 2)) = 2)
    (W : Subgroup S) [W.Normal] [IsElementaryAbelian 2 W] (hW : Nat.card W = 4)
    (hno : ¬ ∃ E : Subgroup S, E.Normal ∧ IsElementaryAbelian 2 E ∧ 8 ≤ Nat.card E)
    (hunique : ∀ F : Subgroup S, F.Normal → IsElementaryAbelian 2 F → Nat.card F = 4 → F = W)
    (hnormal : ¬ (fourImage S W).Normal)
    (hcore : Nat.card (pCore 2 (OmegaQuotient S)) = 16)
    (t : S) (ht : orderOf t = 2) (htcore : t ∈ omegaCorePreimage S) :
    ∃ v ∈ fourImage S W, IsConj (omegaQuotientHom S t) v := by
  have hle := NormalEightNonnormalImage.fourImage_le_pCore hN S hZ W hW hno
  let F := (fourImage S W).subgroupOf (pCore 2 (OmegaQuotient S))
  let : IsElementaryAbelian 2 (fourImage S W) := fourImage_elementary S W
  let : F.Normal := by
    apply (normal_subgroupOf_iff_le_normalizer hle).mpr
    have hn := W.le_normalizer_map (omegaQuotientHom S)
    rw [W.normalizer_eq_top, ← MonoidHom.range_eq_map, omegaQuotientHom_range,
      ← fourImage_eq_map] at hn
    exact (pCore_isPGroup.le_sylow_of_normal (omegaQuotientSylow S)).trans hn
  let : IsElementaryAbelian 2 F := IsElementaryAbelian.subgroupOf hle
  have hF : Nat.card F = 4 :=
    (Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv).trans (fourImage_card S W hW)
  let t' : pCore 2 (OmegaQuotient S) := ⟨omegaQuotientHom S t, htcore⟩
  have ht' : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe t']
    exact (orderOf_injective _ (omegaQuotientHom_injective S) t).trans ht
  let : IsCyclic (center (pCore 2 (OmegaQuotient S))) :=
    NormalEightNonnormalImage.omegaQuotient_pCore_center_isCyclic S hno W hunique hnormal
  obtain ⟨u, hu⟩ := OrderSixteenCoreOrbit.Subgroup.exists_isConj_mem_normal_four
    (pCore 2 (OmegaQuotient S)) hcore
    (omegaQuotient_pCore_center_card hN S hZ W hW hno hunique hnormal hcore)
    (omegaQuotient_no_normal_four S W hunique hnormal) F hF t' ht'
  exact ⟨((u : pCore 2 (OmegaQuotient S)) : OmegaQuotient S), u.property, hu⟩

end Stellmacher.Recognition.NormalEightTerminalCoreOrbit
