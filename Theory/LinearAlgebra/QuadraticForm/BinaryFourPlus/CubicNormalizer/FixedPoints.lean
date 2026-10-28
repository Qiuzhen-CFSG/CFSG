module
public import Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CubicNormalizer.SymmetricFactor
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CubicNormalizer
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.CubicNormalizer.SymmetricFactor
import all Theory.LinearAlgebra.QuadraticForm.BinaryFourPlus.Plane

/-!
# Fixed spaces in the marked cubic normalizer

A nonidentity singular-displacement actor centralizing a cubic subgroup places
that subgroup on one of the two full-support cubic lines. Its normalizer is
the literal S₃ × S₃ subgroup of the wreath model. Each nonidentity involution
in that subgroup fixes four vectors, and two distinct commuting involutions
fix two vectors in common. An element whose fourth power is one is involutive.

The finite checks use the existing 36-element normalizer and its action on
the 16-vector plus space. Internal imports deliberately share its coordinate
implementation; the public statements retain the original cubic subgroup,
singular actor and linear action, with no abstract model assumption.

Source: Aschbacher–Smith, Lemmas 13.5.15–13.5.16, printed pp.919–921.
These bounds supply the order-two and order-four image cases in the
characteristic-subgroup argument for the original extension of U_H/Φ(U_H).
-/

open Subgroup
namespace BinaryFourPlus.CubicNormalizer

private def eval (w : Wreath) (v : V) : V :=
  if w.right = 1 then
    (planeLinear (w.left 1) v.1, planeLinear (w.left swapIndex) v.2)
  else (planeLinear (w.left 1) v.2, planeLinear (w.left swapIndex) v.1)

private theorem eval_eq (w : Wreath) (v : V) :
    eval w v = (wreathToIsometry w).val v :=
  (wreathToIsometry_apply w v).symm

private theorem one_actor_table : ∀ p : S3 × S3,
    p ^ 2 = 1 → p ≠ 1 → Fintype.card {v : V // eval (full p) v = v} = 4 := by
  decide +kernel

private theorem full_involution_fixed_card (a : Wreath) (ha : a ∈ full.range)
    (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) :
    Nat.card {v : V // (wreathToIsometry a).val v = v} = 4 := by
  obtain ⟨p, rfl⟩ := ha
  have hp2 : p ^ 2 = 1 := full_injective (by simpa using ha2)
  have hp1 : p ≠ 1 := by intro h; simp [h] at ha1
  simpa only [Nat.card_eq_fintype_card, eval_eq] using one_actor_table p hp2 hp1

private def commonFixed (p r : S3 × S3) : Finset V :=
  Finset.univ.filter (fun v => eval (full p) v = v ∧ eval (full r) v = v)

private theorem two_actor_table : ∀ p r : S3 × S3,
    (p ^ 2 = 1 ∧ p ≠ 1 ∧ r ^ 2 = 1 ∧ r ≠ 1 ∧ p ≠ r ∧ p * r = r * p) →
    (commonFixed p r).card = 2 := by
  let dec : Decidable (∀ p r : S3 × S3,
      (p ^ 2 = 1 ∧ p ≠ 1 ∧ r ^ 2 = 1 ∧ r ≠ 1 ∧ p ≠ r ∧ p * r = r * p) →
        (commonFixed p r).card = 2) :=
    @Fintype.decidableForallFintype _ _ (fun p =>
      @Fintype.decidableForallFintype _ _ (fun r => inferInstance) _) _
  exact of_decide_eq_true (by decide +kernel)

private theorem full_involution_pair_fixed_card (a b : Wreath)
    (ha : a ∈ full.range) (hb : b ∈ full.range)
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : Commute a b) :
    Nat.card {v : V // (wreathToIsometry a).val v = v ∧
      (wreathToIsometry b).val v = v} = 2 := by
  obtain ⟨p, rfl⟩ := ha
  obtain ⟨r, rfl⟩ := hb
  have hp2 : p ^ 2 = 1 := full_injective (by simpa using ha2)
  have hr2 : r ^ 2 = 1 := full_injective (by simpa using hb2)
  have hp1 : p ≠ 1 := by intro h; simp [h] at ha1
  have hr1 : r ≠ 1 := by intro h; simp [h] at hb1
  have hpr : p ≠ r := fun h => hab (congrArg full h)
  have hc' : p * r = r * p := full_injective (by simpa using hc.eq)
  simpa only [Nat.card_eq_fintype_card, commonFixed, ← Fintype.card_subtype, eval_eq] using
    two_actor_table p r ⟨hp2, hp1, hr2, hr1, hpr, hc'⟩

private theorem full_square_of_fourth_power (a : Wreath) (ha : a ∈ full.range)
    (ha4 : a ^ 4 = 1) : a ^ 2 = 1 := by
  obtain ⟨p, rfl⟩ := ha
  have hp4 : p ^ 4 = 1 := full_injective (by simpa using ha4)
  have hh : ∀ p : S3 × S3, p ^ 4 = 1 → p ^ 2 = 1 := by decide +kernel
  simpa using congrArg full (hh p hp4)

/-- Every nonidentity involution in the marked cubic normalizer fixes four vectors. -/
public theorem cubicNormalizer_involution_fixed_card (A : Subgroup Wreath)
    (hA : Nat.card A = 3) (s : Wreath) (hs : s ≠ 1)
    (hss : SingularDisplacements s) (hcentral : s ∈ centralizer (A : Set Wreath))
    (a : Wreath) (ha : a ∈ normalizer (A : Set Wreath))
    (ha2 : a ^ 2 = 1) (ha1 : a ≠ 1) :
    Nat.card {v : V // (wreathToIsometry a).val v = v} = 4 := by
  obtain ⟨side, rfl⟩ := cyclic_position A hA s hs hss hcentral
  rw [← full_range_eq_normalizer side] at ha
  exact full_involution_fixed_card a ha ha2 ha1

/-- Distinct commuting involutions in the marked normalizer have two common fixed vectors. -/
public theorem cubicNormalizer_involution_pair_fixed_card (A : Subgroup Wreath)
    (hA : Nat.card A = 3) (s : Wreath) (hs : s ≠ 1)
    (hss : SingularDisplacements s) (hcentral : s ∈ centralizer (A : Set Wreath))
    (a b : Wreath) (ha : a ∈ normalizer (A : Set Wreath))
    (hb : b ∈ normalizer (A : Set Wreath))
    (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : Commute a b) :
    Nat.card {v : V // (wreathToIsometry a).val v = v ∧
      (wreathToIsometry b).val v = v} = 2 := by
  obtain ⟨side, rfl⟩ := cyclic_position A hA s hs hss hcentral
  rw [← full_range_eq_normalizer side] at ha hb
  exact full_involution_pair_fixed_card a b ha hb ha2 hb2 ha1 hb1 hab hc

/-- The marked cubic normalizer has no element of order four. -/
public theorem cubicNormalizer_square_of_fourth_power (A : Subgroup Wreath)
    (hA : Nat.card A = 3) (s : Wreath) (hs : s ≠ 1)
    (hss : SingularDisplacements s) (hcentral : s ∈ centralizer (A : Set Wreath))
    (a : Wreath) (ha : a ∈ normalizer (A : Set Wreath))
    (ha4 : a ^ 4 = 1) : a ^ 2 = 1 := by
  obtain ⟨side, rfl⟩ := cyclic_position A hA s hs hss hcentral
  rw [← full_range_eq_normalizer side] at ha
  exact full_square_of_fourth_power a ha ha4

end BinaryFourPlus.CubicNormalizer
