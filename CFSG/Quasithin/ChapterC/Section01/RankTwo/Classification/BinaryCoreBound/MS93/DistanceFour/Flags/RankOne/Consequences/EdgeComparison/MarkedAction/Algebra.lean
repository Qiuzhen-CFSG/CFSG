module

public import CFSG.Quasithin.ChapterC.Section01.RankTwo.Classification.BinaryCoreBound.MS93.DistanceFour.Flags.RankOne.Consequences.Residual

/-!
# Removing the fixed summand in the marked edge action

Fixed points commute with adjoining a centralizing summand. An idempotent
nonzero commutator contained in a group of order four is the whole group:
a proper nonzero commutator would have order two and hence trivial action.
The resulting moving four-group has no nonidentity fixed point, since such
fixed points would give another invariant quotient of order two.

These are the elementary action steps used for the natural plane in MS93
(4.6.9), printed p.908. No ambient finiteness or chosen matrix marking is
assumed in these algebraic helpers.
-/

public section

open Subgroup
open scoped Pointwise
namespace CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.MarkedAction
variable {G : Type*} [Group G]

/-- Taking fixed points commutes with adjoining a summand centralized by the actor. -/
theorem fixed_sup_of_centralizing (U F H : Subgroup G)
    (hFU : F ≤ normalizer (U : Set G)) (hFH : F ≤ centralizer (H : Set G)) :
    (U ⊔ F) ⊓ centralizer (H : Set G) =
      (U ⊓ centralizer (H : Set G)) ⊔ F := by
  apply le_antisymm
  · intro x hx
    have hmul : x ∈ (U : Set G) * (F : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left U F hFU]
      exact hx.1
    obtain ⟨u, hu, f, hf, rfl⟩ := hmul
    have huC : u ∈ centralizer (H : Set G) := by
      simpa only [mul_inv_cancel_right] using
        (centralizer (H : Set G)).mul_mem hx.2
          ((centralizer (H : Set G)).inv_mem (hFH hf))
    exact mul_mem_sup ⟨hu, huC⟩ hf
  · exact sup_le (le_inf (inf_le_left.trans le_sup_left) inf_le_right)
      (le_inf le_sup_right hFH)

private theorem card_one_two_four (W C : Subgroup G) (hW : Nat.card W = 4)
    (hCW : C ≤ W) : Nat.card C = 1 ∨ Nat.card C = 2 ∨ Nat.card C = 4 := by
  have hd := card_dvd_of_le hCW
  rw [hW] at hd
  have hm : Nat.card C ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hd, by decide⟩
  rw [show Nat.divisors 4 = {1, 2, 4} by decide] at hm
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hm

/-- An idempotent nonzero action whose image lies in a four-group moves the
whole four-group and has no nonidentity fixed element there. -/
theorem moving_four_fixed_free (V W H : Subgroup G) (hW : Nat.card W = 4)
    (hHW : H ≤ normalizer (W : Set G)) (himage : ⁅V,H⁆ ≤ W)
    (hne : ⁅V,H⁆ ≠ ⊥) (hi : ⁅⁅V,H⁆,H⁆ = ⁅V,H⁆) :
    ⁅V,H⁆ = W ∧ ⁅W,H⁆ = W ∧ W ⊓ centralizer (H : Set G) = ⊥ := by
  let C := ⁅V,H⁆
  let : Finite W := Nat.finite_of_card_ne_zero (by omega : Nat.card W ≠ 0)
  let : Finite C := Finite.of_injective (inclusion himage) (inclusion_injective _)
  have hCW : C = W := by
    rcases card_one_two_four W C hW himage with hc | hc | hc
    · exact (hne (card_eq_one.mp hc)).elim
    · have hb : ⁅C,H⁆ ≤ ⊥ := commutator_le_of_normalized_index_two C ⊥ H bot_le
        (by simpa only [relIndex_bot_left] using hc)
        (normalizer_commutator_ge_right V H)
        (le_normalizer_iff_commutator_le_right.mpr (by rw [commutator_bot_right]))
      exact (hne (le_bot_iff.mp (hi ▸ hb))).elim
    · exact eq_of_le_of_card_ge himage (by rw [hW, hc])
  have hmove : ⁅W,H⁆ = W := by rw [← hCW]; exact hi
  refine ⟨hCW, hmove, ?_⟩
  let F := W ⊓ centralizer (H : Set G)
  have hFW : F ≤ W := inf_le_left
  have hFC : F ≤ centralizer (H : Set G) := inf_le_right
  let : Finite F := Finite.of_injective (inclusion hFW) (inclusion_injective _)
  rcases card_one_two_four W F hW hFW with hf | hf | hf
  · exact card_eq_one.mp hf
  · have hindex : F.relIndex W = 2 := by
      have ht := (F.subgroupOf W).index_mul_card
      rw [Nat.card_congr (subgroupOfEquivOfLe hFW).toEquiv, hW, hf] at ht
      change F.relIndex W * 2 = 4 at ht
      omega
    have hHF : H ≤ normalizer (F : Set G) :=
      (le_centralizer_iff.mpr hFC).trans (Subgroup.centralizer_le_normalizer _)
    have hWF : W ≤ F := hmove ▸
      commutator_le_of_normalized_index_two W F H hFW hindex hHW hHF
    have hh := card_le_of_le hWF
    rw [hW, hf] at hh
    omega
  · have he : F = W := eq_of_le_of_card_ge hFW (by rw [hW, hf])
    have hb : W = ⊥ := hmove.symm.trans
      (commutator_eq_bot_iff_le_centralizer.mpr (he ▸ hFC))
    have hc := card_eq_one.mpr hb
    omega

end CFSG.Quasithin.ChapterC.BinaryMS.MS93.DistanceFour.Flags.RankOne.MarkedAction
