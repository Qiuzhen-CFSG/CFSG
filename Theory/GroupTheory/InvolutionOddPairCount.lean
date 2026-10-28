module

public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.GroupTheory.Subgroup.Centralizer
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Set.Card
import Mathlib.Tactic.Group
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push

/-!
# Odd-product pairs of involutions with elementary centralizers

If every involution centralizer has exponent two, any even-order element
has square one: it centralizes its own half-order involution. Thus two
involutions have even-order product exactly when they are distinct and
commute. For a fixed involution, the forbidden second factors are its
centralizer minus the identity and itself. A sigma-type count then counts
all ordered odd-product pairs, retaining the equal-factor pairs.

This is the elementary counting step in GLS, Volume 4, Chapter 2,
Lemma 12.8(a), specialized here only by the centralizer hypotheses.
The characteristic-two PSL₂ application is in
`Theory.SpecificGroups.PSL2.OddInvolutionPairs`.
-/

noncomputable section
namespace Theory.GroupTheory.InvolutionOddPairCount
open Subgroup
open scoped BigOperators
variable {G : Type*} [Group G] [Finite G]

private theorem square_of_even_order
    (hC : ∀ a : G, orderOf a = 2 → ∀ b : G, Commute a b → b ^ 2 = 1)
    {x : G} (hx : Even (orderOf x)) : x ^ 2 = 1 := by
  let w := x ^ (orderOf x / 2)
  have hw : orderOf w = 2 := orderOf_pow_orderOf_div (orderOf_pos x).ne' (even_iff_two_dvd.mp hx)
  exact hC w hw x ((Commute.refl x).pow_left _)

/-- In a finite group with elementary involution centralizers, the forbidden
second factors are precisely the distinct commuting involutions. -/
public theorem not_odd_order_mul_iff
    (hC : ∀ a : G, orderOf a = 2 → ∀ b : G, Commute a b → b ^ 2 = 1)
    {a b : G} (ha : orderOf a = 2) (hb : orderOf b = 2) :
    ¬ Odd (orderOf (a * b)) ↔ b ≠ a ∧ Commute a b := by
  have haa : a * a = 1 := by simpa only [ha, pow_two] using pow_orderOf_eq_one a
  have hbb : b * b = 1 := by simpa only [hb, pow_two] using pow_orderOf_eq_one b
  have hai : a⁻¹ = a := inv_eq_iff_mul_eq_one.mpr haa
  have hbi : b⁻¹ = b := inv_eq_iff_mul_eq_one.mpr hbb
  constructor
  · intro hn
    refine ⟨?_, ?_⟩
    · rintro rfl
      simp [hbb] at hn
    · have hs := square_of_even_order hC (Nat.not_odd_iff_even.mp hn)
      have hi : (a * b)⁻¹ = a * b := inv_eq_iff_mul_eq_one.mpr (by simpa only [pow_two] using hs)
      rw [mul_inv_rev, hai, hbi] at hi
      exact hi.symm
  · rintro ⟨hne, hc⟩ ho
    have hsq : (a * b) ^ 2 = 1 := by rw [hc.mul_pow, pow_two, pow_two, haa, hbb, one_mul]
    have hn1 : a * b ≠ 1 := by
      intro he
      have hh : b = a⁻¹ := eq_inv_of_mul_eq_one_right he
      exact hne (hh.trans hai)
    have he : orderOf (a * b) = 2 := orderOf_eq_prime hsq hn1
    rw [he] at ho
    exact (by decide : ¬ Odd (2 : ℕ)) ho

private theorem card_except_two {C : Type*} [Finite C] (a b : C) (hne : a ≠ b) :
    Nat.card {x : C // x ≠ a ∧ x ≠ b} = Nat.card C - 2 := by
  classical
  let : Fintype C := Fintype.ofFinite _
  have he : (fun x : C => x ≠ a ∧ x ≠ b) = (fun x => ¬(x = a ∨ x = b)) := by
    funext x
    exact propext not_or.symm
  rw [he, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  have ht : Nat.card {x : C // x = a ∨ x = b} = 2 := by
    change Nat.card ({a, b} : Set C) = 2
    exact Set.ncard_pair hne
  rw [ht]

/-- Count the allowed second factors, including the first factor itself. -/
public theorem card_second_factors
    (hC : ∀ a : G, orderOf a = 2 → ∀ b : G, Commute a b → b ^ 2 = 1)
    (a : G) (ha : orderOf a = 2) :
    Nat.card {b : {b : G // orderOf b = 2} // Odd (orderOf (a * b.val))} =
      Nat.card {b : G // orderOf b = 2} - (Nat.card (centralizer ({a} : Set G)) - 2) := by
  classical
  let I := {b : G // orderOf b = 2}
  let C := centralizer ({a} : Set G)
  let aC : C := ⟨a, mem_centralizer_singleton_iff.mpr rfl⟩
  have ha1 : a ≠ 1 := by intro he; simp [he] at ha
  let e : {b : I // ¬ Odd (orderOf (a * b.val))} ≃ {b : C // b ≠ 1 ∧ b ≠ aC} := {
    toFun b := by
      have hb := (not_odd_order_mul_iff hC ha b.val.property).mp b.property
      have hb1 : (b.val : G) ≠ 1 := by intro he; have hh := b.val.property; simp [he] at hh
      exact ⟨⟨b.val, mem_centralizer_singleton_iff.mpr hb.2.symm.eq⟩,
        fun he => hb1 (congrArg Subtype.val he), fun he => hb.1 (congrArg Subtype.val he)⟩
    invFun b := by
      have hc : Commute a (b.val : G) := (mem_centralizer_singleton_iff.mp b.val.property).symm
      have hb1 : (b.val : G) ≠ 1 := fun he => b.property.1 (Subtype.ext he)
      have hb2 : orderOf (b.val : G) = 2 := orderOf_eq_prime (hC a ha b.val hc) hb1
      exact ⟨⟨b.val, hb2⟩, (not_odd_order_mul_iff hC ha hb2).mpr
        ⟨fun he => b.property.2 (Subtype.ext he), hc⟩⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  have hbad : Nat.card {b : I // ¬ Odd (orderOf (a * b.val))} = Nat.card C - 2 := by
    rw [Nat.card_congr e]
    exact card_except_two 1 aC (fun he => ha1 (congrArg Subtype.val he.symm))
  let : Fintype I := Fintype.ofFinite _
  have he : Nat.card {b : I // Odd (orderOf (a * b.val))} =
      Nat.card I - Nat.card {b : I // ¬ Odd (orderOf (a * b.val))} := by
    simp only [Nat.card_eq_fintype_card, ← Fintype.card_subtype_compl, not_not]
  exact he.trans (congrArg (Nat.card I - ·) hbad)

/-- Count ordered odd-product pairs when all involution centralizers have
one fixed order and exponent two. -/
public theorem card_pairs {q : ℕ}
    (hC : ∀ a : G, orderOf a = 2 → ∀ b : G, Commute a b → b ^ 2 = 1)
    (hc : ∀ a : G, orderOf a = 2 → Nat.card (centralizer ({a} : Set G)) = q) :
    Nat.card {p : G × G // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} =
      Nat.card {a : G // orderOf a = 2} * (Nat.card {a : G // orderOf a = 2} - (q - 2)) := by
  classical
  let I := {a : G // orderOf a = 2}
  let : Fintype I := Fintype.ofFinite _
  let e : {p : G × G // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ Odd (orderOf (p.1 * p.2))} ≃
      Σ a : I, {b : I // Odd (orderOf (a.val * b.val))} := {
    toFun p := ⟨⟨p.val.1, p.property.1⟩, ⟨⟨p.val.2, p.property.2.1⟩, p.property.2.2⟩⟩
    invFun p := ⟨(p.1.val, p.2.val.val), p.1.property, p.2.val.property, p.2.property⟩
    left_inv _ := rfl
    right_inv _ := rfl }
  rw [Nat.card_congr e, Nat.card_sigma]
  have hf (a : I) : Nat.card {b : I // Odd (orderOf (a.val * b.val))} = Nat.card I - (q - 2) := by
    rw [card_second_factors hC a.val a.property, hc a.val a.property]
  simp only [hf, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, ← Nat.card_eq_fintype_card]
  rfl
end Theory.GroupTheory.InvolutionOddPairCount
