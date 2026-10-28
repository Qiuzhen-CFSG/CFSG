module
public import CFSG.Quasithin.ChapterC.Section01.BlockTypes.SL2CoverBounds
public import Theory.AtlasPort.LinearGroups.SL2Order
/-!
# Orders of the original natural rank-one block

When the actual two-core is its elementary module, its quotient by the center
has order q³(q²−1). The center factor cancels from the natural-module and
SL₂ quotient counts. This is the low-rank overcomponent test in
Aschbacher–Smith 2.4.11, printed p.532.
-/
public section
open Subgroup
namespace CFSG.Quasithin.ChapterC
theorem IsL2EvenBlock.center_quotient_card {L : Type*} [Group L] [Finite L]
    {n : ℕ} (h : IsL2EvenBlock L n) (hc : pCore 2 L = blockU L) :
    Nat.card (L ⧸ center L) = 2^(3*n) * ((2^n)^2-1) := by
  obtain ⟨F,_,_,hF,_,r,⟨m⟩,hm⟩ := h.2.2
  have hquot : Nat.card (L ⧸ pCore 2 L) = 2^n * ((2^n)^2-1) := by
    rw [Nat.card_congr m.quotientIso.toEquiv, Atlas.card_sl_two, hF]
  have hfixed : Nat.card (blockFixed L) = Nat.card (center L) :=
    Nat.card_congr (subgroupOfEquivOfLe (h.center_le_module hc)).toEquiv
  have hU : Nat.card (blockU L) = 2^(n*2) * Nat.card (center L) := by
    rw [card_eq_card_quotient_mul_card_subgroup (blockFixed L), hfixed]
    rw [show Nat.card (blockU L ⧸ blockFixed L) = 2^(n*2) from h.module_card]
  have hcard := card_eq_card_quotient_mul_card_subgroup (pCore 2 L)
  rw [hquot,hc,hU,card_eq_card_quotient_mul_card_subgroup (center L)] at hcard
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := center L))
  calc
    Nat.card (L ⧸ center L) * Nat.card (center L) =
        2^n * ((2^n)^2-1) * (2^(n*2) * Nat.card (center L)) := hcard
    _ = (2^(3*n) * ((2^n)^2-1)) * Nat.card (center L) := by
      rw [show 3*n=n+n*2 by omega, pow_add]
      ring
end CFSG.Quasithin.ChapterC
