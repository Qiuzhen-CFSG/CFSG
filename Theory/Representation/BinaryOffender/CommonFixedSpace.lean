module

public import Theory.Representation.BinaryOffender.CommutatorRank

/-!
# Elementary actors with a common fixed space

If every nonidentity element has the same fixed space, displacement of a
moving vector embeds the actor into that space. In characteristic two an
involution fixes its displacement, so the image lies in the common fixed
space; equality of two displacements would make their quotient fix the
moving vector. This is the cardinality step in the terminal argument of
Aschbacher–Smith 13.4.1, printed p.915.
-/

public noncomputable section
open Subgroup Representation.BinaryOffender
namespace Representation.BinaryOffender
variable {G V : Type*} [Group G] [AddCommGroup V] [Module (ZMod 2) V]

/-- A moving point embeds a common-fixed-space actor into its fixed space,
by the actual displacement map. -/
theorem card_le_fixedSpace_of_common_fixedSpace [Finite V]
    (ρ : Representation (ZMod 2) G V) (A : Subgroup G) [IsElementaryAbelian 2 A]
    (hc : ∀ a ∈ A, a ≠ 1 → fixedSpace ρ (zpowers a) ≤ fixedSpace ρ A)
    (v : V) (hv : v ∉ fixedSpace ρ A) : Nat.card A ≤ Nat.card (fixedSpace ρ A) := by
  have hd (a : A) : ρ a.val v - v ∈ fixedSpace ρ A := by
    by_cases ha : a.val = 1
    · simp [ha]
    apply hc a.val a.property ha
    rw [mem_fixedSpace_zpowers_iff, map_sub]
    have hs : a.val ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian a.val a.property
    have he : ρ a.val (ρ a.val v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, ← pow_two, hs, map_one]
      rfl
    rw [he]
    have hneg (w : V) : -w = w := by
      apply neg_eq_iff_add_eq_zero.mpr
      have hh := @two_smul (ZMod 2) V _ _ _ w
      rw [show (2 : ZMod 2) = 0 by decide, zero_smul] at hh
      exact hh.symm
    simp only [sub_eq_add_neg, hneg, add_comm]
  let f : A → fixedSpace ρ A := fun a => ⟨ρ a.val v - v, hd a⟩
  apply Nat.card_le_card_of_injective f
  intro a b hab
  have he : ρ a.val v = ρ b.val v :=
    sub_left_inj.mp (congrArg Subtype.val hab)
  by_contra hne
  have hba : b.val⁻¹ * a.val ≠ 1 := by
    intro hh
    exact hne (Subtype.ext (inv_mul_eq_one.mp hh).symm)
  apply hv
  apply hc _ (A.mul_mem (A.inv_mem b.property) a.property) hba
  rw [mem_fixedSpace_zpowers_iff, map_mul, Module.End.mul_apply, he,
    ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
  rfl

end Representation.BinaryOffender
