module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CubicNormalizer.FixedPoints
public import Theory.ElementaryAbelian.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.Tactic.NormNum

/-!
# The absence of offenders in the binary plus-four cubic normalizer

Let C be an order-three subgroup of O₄⁺(2), centralized by a nonidentity
actor with totally singular displacement. Every nontrivial elementary
abelian two-subgroup A of N(C) satisfies |A| |C_V(A)| < |V| = 16.

The marked normalizer has order 36, so A has order two or four. A nonidentity
involution fixes four vectors, and a pair of distinct commuting involutions
fixes two. These are the action-compatible calculations for the actual wreath
model, and they give |A| |C_V(A)| ≤ 8 in either case.

Source: Aschbacher–Smith, Proposition 13.5.16, printed p.921, the
characteristic-subgroup argument following the plus-four action in 13.5.15.
-/

namespace BinaryFourPlus.CubicNormalizer
open Subgroup
open scoped IsMulCommutative

private instance : Finite Wreath := by
  unfold Wreath
  infer_instance

private theorem elementary_card_cases
    (C : Subgroup Wreath) (hC : Nat.card C = 3)
    (s : Wreath) (hs : s ≠ 1) (hss : SingularDisplacements s)
    (hcentral : s ∈ centralizer (C : Set Wreath))
    (A : Subgroup Wreath) [IsElementaryAbelian 2 A]
    (hAN : A ≤ normalizer (C : Set Wreath)) (hA : A ≠ ⊥) :
    Nat.card A = 2 ∨ Nat.card A = 4 := by
  have hN := (normalizer_centralizer_card C hC s hs hss hcentral).1
  have hd : Nat.card A ∣ 36 := hN ▸ card_dvd_of_le hAN
  obtain ⟨n, hn⟩ := (IsElementaryAbelian.isPGroup 2 A).exists_card_eq
  have hnlt : n < 3 := by
    by_contra h
    have h8 : 8 ∣ 36 :=
      (show 2 ^ 3 ∣ 2 ^ n from pow_dvd_pow 2 (by omega)).trans (hn ▸ hd)
    norm_num at h8
  have hAcard : 1 < Nat.card A := A.one_lt_card_iff_ne_bot.mpr hA
  rcases (by omega : n = 0 ∨ n = 1 ∨ n = 2) with rfl | rfl | rfl
  · rw [pow_zero] at hn
    omega
  · exact Or.inl (by simpa only [pow_one] using hn)
  · exact Or.inr (by simpa only [Nat.reducePow] using hn)

private theorem exists_two_nonidentity
    (A : Subgroup Wreath) (hA : Nat.card A = 4) :
    ∃ a b : A, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  let : Fintype A := Fintype.ofFinite A
  have hAn : A ≠ ⊥ := by
    intro hb
    simp [hb] at hA
  obtain ⟨a, ha⟩ := (ne_bot_iff_exists_ne_one (H := A)).mp hAn
  have hb : ∃ b : A, b ≠ 1 ∧ b ≠ a := by
    by_contra h
    push Not at h
    have hsub : (Finset.univ : Finset A) ⊆ {1, a} := by
      intro b _
      by_cases hb : b = 1
      · simp [hb]
      · simp [h b hb]
    have hc := (Finset.card_le_card hsub).trans Finset.card_le_two
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hA] at hc
    omega
  obtain ⟨b, hb, hba⟩ := hb
  exact ⟨a, b, ha, hb, Ne.symm hba⟩

/-- Every nontrivial elementary two-subgroup of the actual cubic normalizer
has product of its order and its number of fixed vectors at most eight. -/
public theorem elementary_fixed_card_le_eight
    (C : Subgroup Wreath) (hC : Nat.card C = 3)
    (s : Wreath) (hs : s ≠ 1) (hss : SingularDisplacements s)
    (hcentral : s ∈ centralizer (C : Set Wreath))
    (A : Subgroup Wreath) [IsElementaryAbelian 2 A]
    (hAN : A ≤ normalizer (C : Set Wreath)) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card {v : V // ∀ a : A, (wreathToIsometry a.val).val v = v} ≤ 8 := by
  rcases elementary_card_cases C hC s hs hss hcentral A hAN hA with h2 | h4
  · obtain ⟨a, ha⟩ := (ne_bot_iff_exists_ne_one (H := A)).mp hA
    have ha1 : (a : Wreath) ≠ 1 := fun h => ha (Subtype.ext h)
    have ha2 : (a : Wreath) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ a.property
    have hf := cubicNormalizer_involution_fixed_card C hC s hs hss hcentral
      a (hAN a.property) ha2 ha1
    have hle : Nat.card {v : V // ∀ a : A, (wreathToIsometry a.val).val v = v} ≤ 4 := by
      apply le_trans (Nat.card_le_card_of_injective
        (fun v : {v : V // ∀ a : A, (wreathToIsometry a.val).val v = v} =>
          (⟨v.val, v.property a⟩ : {v : V // (wreathToIsometry a.val).val v = v}))
        (fun _ _ h => Subtype.ext (congrArg
          (fun z : {v : V // (wreathToIsometry a.val).val v = v} => z.val) h))) hf.le
    rw [h2]
    omega
  · obtain ⟨a, b, ha, hb, hab⟩ := exists_two_nonidentity A h4
    have ha1 : (a : Wreath) ≠ 1 := fun h => ha (Subtype.ext h)
    have hb1 : (b : Wreath) ≠ 1 := fun h => hb (Subtype.ext h)
    have hab' : (a : Wreath) ≠ b := fun h => hab (Subtype.ext h)
    have ha2 : (a : Wreath) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ a.property
    have hb2 : (b : Wreath) ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian _ b.property
    have hc : Commute (a : Wreath) b :=
      congrArg Subtype.val (mul_comm a b)
    have hf := cubicNormalizer_involution_pair_fixed_card C hC s hs hss hcentral
      a b (hAN a.property) (hAN b.property) ha2 hb2 ha1 hb1 hab' hc
    have hle : Nat.card {v : V // ∀ a : A, (wreathToIsometry a.val).val v = v} ≤ 2 := by
      apply le_trans (Nat.card_le_card_of_injective
        (fun v : {v : V // ∀ a : A, (wreathToIsometry a.val).val v = v} =>
          (⟨v.val, v.property a, v.property b⟩ :
            {v : V // (wreathToIsometry a.val).val v = v ∧ (wreathToIsometry b.val).val v = v}))
        (fun _ _ h => Subtype.ext (congrArg
          (fun z : {v : V // (wreathToIsometry a.val).val v = v ∧
            (wreathToIsometry b.val).val v = v} => z.val) h))) hf.le
    rw [h4]
    omega

/-- The natural binary plus-four module has no nontrivial elementary offender
inside the marked cubic normalizer. -/
public theorem elementary_fixed_card_lt
    (C : Subgroup Wreath) (hC : Nat.card C = 3)
    (s : Wreath) (hs : s ≠ 1) (hss : SingularDisplacements s)
    (hcentral : s ∈ centralizer (C : Set Wreath))
    (A : Subgroup Wreath) [IsElementaryAbelian 2 A]
    (hAN : A ≤ normalizer (C : Set Wreath)) (hA : A ≠ ⊥) :
    Nat.card A * Nat.card {v : V // ∀ a : A, (wreathToIsometry a.val).val v = v} < 16 :=
  lt_of_le_of_lt (elementary_fixed_card_le_eight C hC s hs hss hcentral A hAN hA) (by decide)

end BinaryFourPlus.CubicNormalizer
