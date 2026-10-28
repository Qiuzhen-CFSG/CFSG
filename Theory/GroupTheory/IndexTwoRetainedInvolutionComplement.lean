module
public import Theory.GroupTheory.NormalizingInvolutionCard
public import Mathlib.GroupTheory.Index

/-!
# Extending a complement by a specified outside involution

A complement inside an index-two subgroup extends by any actual outside
involution normalizing it. The new complement retains the specified
involution, rather than selecting an unrelated complement.
-/

public noncomputable section
namespace Subgroup
open scoped Pointwise

/-- An actual normalizing involution outside the index-two subgroup extends
its given complement to a complement in the whole finite group. -/
theorem isComplement'_sup_zpowers_of_index_two
    {G : Type*} [Group G] [Finite G]
    (V D H : Subgroup G) (hVH : V ≤ H) (hDH : D ≤ H)
    (hcomp : (V.subgroupOf H).IsComplement' (D.subgroupOf H))
    (hi : H.index = 2) (w : G) (hw : w ^ 2 = 1)
    (hout : w ∉ H) (hnorm : w ∈ normalizer (D : Set G)) :
    V.IsComplement' (D ⊔ zpowers w) := by
  classical
  have hwd : w ∉ D := fun h => hout (hDH h)
  have hwo : orderOf w = 2 := orderOf_eq_prime hw (fun h => hout (h ▸ H.one_mem))
  have hdis : Disjoint V (D ⊔ zpowers w) := by
    apply disjoint_def.mpr
    intro x hxV hxK
    have hx : x ∈ (D : Set G) * (zpowers w : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left D (zpowers w) (zpowers_le.mpr hnorm)]
      exact hxK
    obtain ⟨d,hd,b,hb,rfl⟩ := hx
    change b ∈ zpowers w at hb
    rw [mem_zpowers_iff_mem_range_orderOf,hwo] at hb
    obtain ⟨n,hn,rfl⟩ := Finset.mem_image.mp hb
    have hn2 := Finset.mem_range.mp hn
    interval_cases n
    · simp only [pow_zero,mul_one] at hxV ⊢
      exact congrArg Subtype.val
        (disjoint_def.mp hcomp.disjoint (show (⟨d,hDH hd⟩ : H) ∈ V.subgroupOf H from hxV)
          (show (⟨d,hDH hd⟩ : H) ∈ D.subgroupOf H from hd))
    · simp only [pow_one] at hxV
      exact (hout (by
        have hm := H.mul_mem (H.inv_mem (hDH hd)) (hVH hxV)
        simpa only [inv_mul_cancel_left] using hm)).elim
  have hcH : Nat.card V * Nat.card D = Nat.card H := by
    have hh := hcomp.card_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe hVH).toEquiv,
      Nat.card_congr (subgroupOfEquivOfLe hDH).toEquiv] at hh
    exact hh
  apply isComplement'_of_card_mul_and_disjoint _ hdis
  rw [card_sup_zpowers_of_normalizing_involution D w hw hwd hnorm,
    ← H.index_mul_card,hi,← hcH]
  ring

end Subgroup
