module
public import Theory.Representation.BinaryOffender.FourDimensionalCubic

/-!
# A fixed line from cubic ratio three halves

An elementary four-group acts cubically in characteristic two. In a binary
four-space with cubic ratio three halves, its fixed codimension is at least
three. A two-group fixes a nonzero vector, so the codimension is exactly
three and the fixed subgroup has order two.

Application: the full Omega row in Aschbacher--Smith 15.2.3, using 14.1.17.
-/

public section
open Subgroup Representation
open scoped ENNReal
namespace Representation.BinaryOffender
theorem fixed_card_of_four_group_cubic_ratio
    {D V : Type*} [Group D] [Finite D] [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V]
    (ρ : Representation (ZMod 2) D V) (hdim : Module.finrank (ZMod 2) V = 4)
    (hq : cubicRatio ρ = 3 / 2)
    (A : Subgroup D) (hA : IsElementaryAbelian 2 A) (hc : Nat.card A = 4) :
    Nat.card (fixedSpace ρ A) = 2 := by
  have hne : A ≠ ⊥ := by intro he; rw [he,card_bot] at hc; omega
  have hr : rank A = 2 := by norm_num [rank,hc]
  have hlow : (3 / 2 : ℝ≥0∞) ≤ actionRatio ρ A := by
    rw [← hq]
    exact iInf_le_of_le A (iInf_le_of_le
      ⟨⟨hne,hA⟩,isCubic_of_elementary_card_four ρ A hA hc⟩ le_rfl)
  have hcod : 3 ≤ fixedCodim ρ A := by
    rw [actionRatio,hr] at hlow
    norm_num only [Nat.cast_ofNat] at hlow
    rw [ENNReal.le_div_iff_mul_le (Or.inl (by norm_num)) (Or.inr (by simp))] at hlow
    rw [ENNReal.div_mul_cancel (a := (2 : ℝ≥0∞)) (by norm_num) (by simp)] at hlow
    exact_mod_cast hlow
  let := hA
  have hu := fixedCodim_le_three_of_four_dimensional ρ hdim A
    (IsElementaryAbelian.isPGroup 2 A)
  have hsum := fixedCodim_add_finrank ρ A
  have hf : Module.finrank (ZMod 2) (fixedSpace ρ A) = 1 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2),Nat.card_zmod,hf]
  rfl
end Representation.BinaryOffender
