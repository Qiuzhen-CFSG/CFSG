module
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed.Comparison
public import Theory.Representation.MathieuCodeRestriction.CodeLocal.SmallKernelFixed.Counts

/-!
# Dimensions from the native fixed-word certificates

The native message equivalence identifies cyclic and common Golay fixed spaces
with the checked masks. Their cardinalities 256 and 32 therefore give dimensions
eight and five over F2. The final module passes to the literal code quotient.

Source: Aschbacher--Smith, H.16.2 and H.16.8, printed pp.402--405.
-/

open Sporadic.Mathieu
open Representation.BinaryOffender
public section
namespace MathieuCode.SmallKernelFixed

/-- Fixedness of a native Golay word is exactly the certified mask bit. -/
theorem golayWord_fixed_iff_mask (n : Fin 16) (u : Fin 4096) :
    golayRepresentation (translation n) (golayWord u) = golayWord u ↔
      (fixedMasks n).getLsb u = true := by
  rw [golayWord_fixed_iff_difference, difference_zero_iff_mask]


/-- Fixed-word counting gives dimension eight before quotienting by constants. -/
theorem golay_translation_finrank (n : Fin 16) (hn : n ≠ 0) :
    Module.finrank (ZMod 2) (fixedSpace golayRepresentation (Subgroup.zpowers (translation n))) = 8 := by
  let e : {u : Fin 4096 // (fixedMasks n).getLsb u = true} ≃
      fixedSpace golayRepresentation (Subgroup.zpowers (translation n)) :=
    golayWordEquiv.subtypeEquiv (fun u => by
      change _ ↔ golayWord u ∈ _
      rw [mem_fixedSpace_zpowers_iff, golayWord_fixed_iff_mask])
  have hc : Nat.card (fixedSpace golayRepresentation (Subgroup.zpowers (translation n))) = 256 := by
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype,
      bitVec_support_card, fixedMasks_size n hn]
  apply Nat.pow_right_injective (by decide : 1 < 2)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact hc

/-- Independent translations have a five-dimensional common Golay fixed space. -/
theorem golay_pair_finrank (n m : Fin 16) (hn : n ≠ 0) (hm : m ≠ 0) (hnm : n ≠ m) :
    Module.finrank (ZMod 2)
      (fixedSpace golayRepresentation (Subgroup.zpowers (translation n)) ⊓
        fixedSpace golayRepresentation (Subgroup.zpowers (translation m)) : Submodule (ZMod 2) golay) = 5 := by
  let e : {u : Fin 4096 // ((fixedMasks n) &&& (fixedMasks m)).getLsb u = true} ≃
      (fixedSpace golayRepresentation (Subgroup.zpowers (translation n)) ⊓
        fixedSpace golayRepresentation (Subgroup.zpowers (translation m)) : Submodule (ZMod 2) golay) :=
    golayWordEquiv.subtypeEquiv (fun u => by
      change _ ↔ golayWord u ∈ _
      simp only [Submodule.mem_inf, mem_fixedSpace_zpowers_iff, golayWord_fixed_iff_mask]
      simp)
  have hc : Nat.card (fixedSpace golayRepresentation (Subgroup.zpowers (translation n)) ⊓
        fixedSpace golayRepresentation (Subgroup.zpowers (translation m)) : Submodule (ZMod 2) golay) = 32 := by
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_subtype,
      bitVec_support_card, fixedMasks_pair_size n m hn hm hnm]
  apply Nat.pow_right_injective (by decide : 1 < 2)
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod] at hc
  exact hc

end MathieuCode.SmallKernelFixed
