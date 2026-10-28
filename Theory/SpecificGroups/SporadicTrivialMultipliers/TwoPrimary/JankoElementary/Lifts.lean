module
public import Theory.SpecificGroups.SporadicTrivialMultipliers.TwoPrimary.JankoElementary.Collection
public import Mathlib.GroupTheory.OrderOfElement

/-!
# Coefficients of a central double extension

An ordered lift of commuting involutions has squares and pair twists in the
central kernel. When this kernel has order two, its unique nonidentity element
encodes both sets of coefficients as Boolean values. This is the group-theoretic
input to the literal J4 local calculation.
-/

@[expose] public section
namespace Janko4.TwoPrimary.JankoElementary
open Subgroup Cardinality.KernelCount

/-- A central kernel of order two has exponent two. -/
theorem kernel_square {G H : Type*} [Group G] [Group H] (q : G →* H)
    (hk : Nat.card q.ker = 2) (z : G) (hz : z ∈ q.ker) : z ^ 2 = 1 := by
  have h := pow_card_eq_one' (x := (⟨z, hz⟩ : q.ker))
  rw [hk] at h
  exact congrArg Subtype.val h

/-- Encode the squares and pair twists of lifts using the central involution.
Only the images are assumed to commute and square to one. -/
theorem exists_coefficients {G H : Type*} [Group G] [Group H]
    (q : G →* H) (hc : q.ker ≤ center G) (hk : Nat.card q.ker = 2)
    {n : ℕ} (e : Fin n → G)
    (hes : ∀ i, q (e i) * q (e i) = 1)
    (hec : ∀ i j, Commute (q (e i)) (q (e j))) :
    ∃ (t : G) (s : Fin n → Bool) (b : Fin n → Fin n → Bool),
      t ≠ 1 ∧ t ∈ center G ∧ t ^ 2 = 1 ∧
      (∀ i, e i ^ 2 = bit t (s i)) ∧
      (∀ i j, e j * e i = e i * e j * bit t (b i j)) := by
  classical
  obtain ⟨z, hz, huniq⟩ := (Nat.card_eq_two_iff' (1 : q.ker)).mp hk
  let t : G := z.val
  have ht : t ≠ 1 := fun he => hz (Subtype.ext he)
  let code : G → Bool := fun a => decide (a ≠ 1)
  have hcode (a : G) (ha : a ∈ q.ker) : a = bit t (code a) := by
    by_cases h1 : a = 1
    · simp [code, h1, bit]
    · have he : (⟨a, ha⟩ : q.ker) = z := huniq _ (fun h => h1 (congrArg Subtype.val h))
      have hat : a = t := congrArg Subtype.val he
      simp only [code, h1, ne_eq, not_false_eq_true, decide_true, bit, ↓reduceIte]
      exact hat
  let s : Fin n → Bool := fun i => code (e i ^ 2)
  let b : Fin n → Fin n → Bool := fun i j => code ((e i * e j)⁻¹ * (e j * e i))
  refine ⟨t, s, b, ht, hc z.property, kernel_square q hk t z.property, ?_, ?_⟩
  · intro i
    apply hcode
    change q (e i ^ 2) = 1
    rw [map_pow, pow_two, hes i]
  · intro i j
    have hkij : (e i * e j)⁻¹ * (e j * e i) ∈ q.ker := by
      change q ((e i * e j)⁻¹ * (e j * e i)) = 1
      rw [map_mul, map_inv, map_mul, map_mul, (hec j i).eq, inv_mul_cancel]
    change e j * e i = e i * e j * bit t (code ((e i * e j)⁻¹ * (e j * e i)))
    rw [← hcode _ hkij, mul_inv_cancel_left]

end Janko4.TwoPrimary.JankoElementary
