module

public import Theory.GroupTheory.CComponent.LocalImageEquality
public import Theory.GroupTheory.PCoreFrattiniTransport
public import Mathlib.GroupTheory.Sylow

/-!
# Quotient order detects equality of local C-components

Pass to the actual two-core quotient. A two-group kernel preserves the
intrinsic two-core quotient of the smaller subgroup, so the order bound
forces its image to be the whole quotient. The ambient two-core lies in
the supplied Sylow, and local C-component minimality lifts the equality.

Source: the local-component comparison in Aschbacher--Smith, 12.9.3,
printed pp.858--859, using A.3.3 and A.3.11.
-/

public section
open Subgroup

namespace Subgroup
variable {G : Type*} [Group G] [Finite G]

/-- A local C-component whose two-core quotient fills the containing
component quotient must be the entire group. The Sylow is the original actor. -/
theorem local_cComponent_eq_top_of_twoCore_card_le (S : Sylow 2 G) (B : Subgroup G)
    (hB : (B.subgroupOf (B ⊔ (S : Subgroup G))).IsCComponent)
    (hG : (⊤ : Subgroup G).IsCComponent)
    (hc : Nat.card (G ⧸ pCore 2 G) ≤ Nat.card (B ⧸ pCore 2 B)) : B = ⊤ := by
  let q := QuotientGroup.mk' (pCore 2 G)
  have hk : IsPGroup 2 q.ker := by
    rw [QuotientGroup.ker_mk']; exact pCore_isPGroup
  have hkb : IsPGroup 2 (q.subgroupMap B).ker := by
    rw [ker_subgroupMap]
    exact hk.comap_subtype
  let e := (q.subgroupMap B).pCoreQuotientEquiv (q.subgroupMap_surjective B) hkb
  have hle : Nat.card (G ⧸ pCore 2 G) ≤ Nat.card (B.map q) := by
    calc
      Nat.card (G ⧸ pCore 2 G) ≤ Nat.card (B ⧸ pCore 2 B) := hc
      _ = Nat.card (B.map q ⧸ pCore 2 (B.map q)) := Nat.card_congr e.toEquiv
      _ ≤ Nat.card (B.map q) := Nat.le_of_dvd Nat.card_pos (pCore 2 (B.map q)).card_quotient_dvd_card
  have he : B.map q = ⊤ := eq_top_of_card_eq _ (le_antisymm (card_le_card_group _) hle)
  apply local_cComponent_eq_of_map_eq hB hG le_top q
  · rw [QuotientGroup.ker_mk']; exact pCore_isPGroup.le_sylow_of_normal S
  · simpa only [map_top_of_surjective q (QuotientGroup.mk'_surjective _)] using he
end Subgroup
