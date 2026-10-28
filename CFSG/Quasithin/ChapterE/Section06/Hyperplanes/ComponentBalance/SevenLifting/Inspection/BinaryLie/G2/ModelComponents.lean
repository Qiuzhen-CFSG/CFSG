module

public import CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.SevenLifting.Inspection.BinaryLie.Obstructions
public import Theory.AtlasPort.LinearGroups.G2.Order
public import Theory.AtlasPort.LinearGroups.G2.Simplicity

/-!
# Whole-model and binary endpoints for the G₂ inspection

The two seven models have orders 2520 and 7560. Simplicity and the proved order
formula exclude both as ordinary components of a whole G₂ group over a field
of order at least four. The binary order obstruction is used separately in the
field-degree induction, since the full G₂(2) is not simple.

Source: Aschbacher–Smith, E.6.18, printed p.252; Theorem C and Remark A.2.4,
printed p.33. The actual octonion-model order and simplicity are imported.
-/

public section

open Subgroup Theory.GroupTheory Atlas.G2
namespace CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.G2

private theorem seven_card_le {X : Type*} [Group X] (L : Subgroup X)
    (hs : IsSeven L) : Nat.card L ≤ 7560 := by
  have ha : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
    rw [nat_card_alternatingGroup]
    norm_num
  rcases hs with hs | hs
  · obtain ⟨e⟩ := hs
    rw [Nat.card_congr e.toEquiv, ha]
    omega
  · obtain ⟨_, ⟨ez⟩, ⟨eq⟩⟩ := hs
    rw [← (center L).card_mul_index, index_eq_card,
      Nat.card_congr ez.toEquiv, Nat.card_congr eq.toEquiv, ha]
    norm_num [Nat.card_eq_fintype_card]

/-- A whole even G₂ model of order at least four has no seven component. -/
theorem model_component_not_seven {F : Type*} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) (L : Subgroup (Model F))
    (hc : IsComponent (Model F) L) : ¬ IsSeven L := by
  intro hs
  have hsimple := Atlas.G2.isSimple (by omega : 2 < Nat.card F)
  rcases hc.1.eq_bot_or_top_of_isSimpleGroup hsimple with h | h
  · have hd := seven_card_dvd hs
    simp only [h, Subgroup.card_bot] at hd
    norm_num at hd
  · have hu := seven_card_le L hs
    have hl : 7560 < Nat.card (Model F) := by
      rw [Atlas.G2.card_Model]
      calc
        7560 < 4 ^ 6 * (4 ^ 6 - 1) * (4 ^ 2 - 1) := by norm_num
        _ ≤ Nat.card F ^ 6 * (Nat.card F ^ 6 - 1) * (Nat.card F ^ 2 - 1) := by
          gcongr
    simp only [h, Subgroup.card_top] at hu
    exact not_le_of_gt hl hu

end CFSG.Quasithin.ChapterE.Section06.Hyperplanes.ComponentBalance.BinaryLie.G2
