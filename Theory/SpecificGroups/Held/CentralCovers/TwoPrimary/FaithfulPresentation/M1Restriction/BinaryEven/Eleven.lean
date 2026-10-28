module
public import Theory.SpecificGroups.Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven.Involutions
import Mathlib.Algebra.BigOperators.Group.List.Lemmas

/-!
# The last even marked word by seven involution reversals

The seven displayed segments have square-one lifts by the concrete conjugacy
and source-commutation argument in `Involutions`. Reversing each such segment
preserves its value. Adjacent equal involutions cancel; cyclic rotations and
conjugation preserve the equation that a product is one. The seven steps
reduce exactly the frozen entry 11 to the empty word. Every list comparison
and every group equality is checked by Lean; the discovery search is untrusted.

Source: the literal entry 11 in `M1Restriction/Data.lean`, on John Bray's
marked generators from `Held/Model/Source/HeG1-P1.M`.
-/

public section
namespace Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven
open PerfectCentralCovering Subgroup.CosetWordCertificate
variable {E : Type*} [Group E]

private theorem positive_append (g : Fin 3 → E) (u v : List (Fin 3)) :
    positive g (u ++ v) = positive g u * positive g v := by
  simp only [positive, List.map_append, List.prod_append]

private theorem positive_reverse (g : Fin 3 → E) (hi : ∀ i, (g i)⁻¹ = g i)
    (w : List (Fin 3)) : positive g w.reverse = (positive g w)⁻¹ := by
  induction w with
  | nil => simp [positive]
  | cons a w ih =>
    rw [List.reverse_cons, positive_append, ih]
    simp only [positive, List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one, mul_inv_rev, hi]

private theorem reverse_segment (g : Fin 3 → E) (hi : ∀ i, (g i)⁻¹ = g i)
    (pre mid post : List (Fin 3)) (hs : positive g mid ^ 2 = 1) :
    positive g (pre ++ mid ++ post) = positive g (pre ++ mid.reverse ++ post) := by
  simp only [positive_append, positive_reverse g hi]
  rw [inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hs)]

private theorem step0 (g : Fin 3 → E) (hi : ∀ i, (g i)⁻¹ = g i)
    (hs : positive g (testLetters 2) ^ 2 = 1)
    (hn : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2] : List (Fin 3)) = 1) :
    positive g ([1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] : List (Fin 3)) = 1 := by
  have hc (i : Fin 3) : g i * g i = 1 := by simpa only [hi] using inv_mul_cancel (g i)
  have hcc (i : Fin 3) (z : E) : g i * (g i * z) = z := by rw [← mul_assoc, hc, one_mul]
  have hr := reverse_segment g hi ([1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1]) ([2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0]) ([2]) hs
  change positive g ([1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] : List (Fin 3)) = positive g ([1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] : List (Fin 3)) at hr
  rw [hr]
  have he : positive g ([1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 2, 2] : List (Fin 3)) =
      positive g ([] : List (Fin 3)) * positive g ([1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0] : List (Fin 3)) *
        (positive g ([] : List (Fin 3)))⁻¹ := by
    simp only [positive, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      inv_one, mul_one, one_mul, hc]
  rw [he]
  have ht : positive g ([1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0] : List (Fin 3)) = 1 := by
    have hh := List.prod_rotate_eq_one_of_prod_eq_one hn 19
    have hrot : ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2] : List (Fin 3)).rotate 19 = [1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0] := by decide
    simpa only [positive, ← List.map_rotate, hrot] using hh
  rw [ht, mul_one, mul_inv_cancel]

private theorem step1 (g : Fin 3 → E) (hi : ∀ i, (g i)⁻¹ = g i)
    (hs : positive g (testLetters 3) ^ 2 = 1)
    (hn : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2] : List (Fin 3)) = 1) :
    positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2] : List (Fin 3)) = 1 := by
  have hc (i : Fin 3) : g i * g i = 1 := by simpa only [hi] using inv_mul_cancel (g i)
  have hcc (i : Fin 3) (z : E) : g i * (g i * z) = z := by rw [← mul_assoc, hc, one_mul]
  have hr := reverse_segment g hi ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0]) ([1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1]) ([2]) hs
  change positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2] : List (Fin 3)) = positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2] : List (Fin 3)) at hr
  rw [hr]
  have he : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2] : List (Fin 3)) =
      positive g ([] : List (Fin 3)) * positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2] : List (Fin 3)) *
        (positive g ([] : List (Fin 3)))⁻¹ := by
    simp only [positive, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      inv_one, mul_one, one_mul]
  rw [he]
  have ht : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2] : List (Fin 3)) = 1 := by
    have hh := List.prod_rotate_eq_one_of_prod_eq_one hn 0
    have hrot : ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2] : List (Fin 3)).rotate 0 = [0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2] := by decide
    simpa only [positive, ← List.map_rotate, hrot] using hh
  rw [ht, mul_one, mul_inv_cancel]

private theorem step2 (g : Fin 3 → E) (hi : ∀ i, (g i)⁻¹ = g i)
    (hs : positive g (testLetters 4) ^ 2 = 1)
    (hn : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)) = 1) :
    positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2] : List (Fin 3)) = 1 := by
  have hc (i : Fin 3) : g i * g i = 1 := by simpa only [hi] using inv_mul_cancel (g i)
  have hcc (i : Fin 3) (z : E) : g i * (g i * z) = z := by rw [← mul_assoc, hc, one_mul]
  have hr := reverse_segment g hi ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0]) ([2, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2]) ([1, 0, 1, 2]) hs
  change positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 2, 1, 0, 1, 0, 1, 0, 2, 1, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 1, 0, 1, 2] : List (Fin 3)) = positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)) at hr
  rw [hr]
  have he : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)) =
      positive g ([] : List (Fin 3)) * positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)) *
        (positive g ([] : List (Fin 3)))⁻¹ := by
    simp only [positive, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      inv_one, mul_one, one_mul]
  rw [he]
  have ht : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)) = 1 := by
    have hh := List.prod_rotate_eq_one_of_prod_eq_one hn 0
    have hrot : ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)).rotate 0 = [0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] := by decide
    simpa only [positive, ← List.map_rotate, hrot] using hh
  rw [ht, mul_one, mul_inv_cancel]

private theorem step3 (g : Fin 3 → E) (hi : ∀ i, (g i)⁻¹ = g i)
    (hs : positive g (testLetters 5) ^ 2 = 1)
    (hn : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2] : List (Fin 3)) = 1) :
    positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)) = 1 := by
  have hc (i : Fin 3) : g i * g i = 1 := by simpa only [hi] using inv_mul_cancel (g i)
  have hcc (i : Fin 3) (z : E) : g i * (g i * z) = z := by rw [← mul_assoc, hc, one_mul]
  have hr := reverse_segment g hi ([0, 1, 0, 1, 0, 1, 2, 0]) ([1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2]) ([1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2]) hs
  change positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 0, 2, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)) = positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)) at hr
  rw [hr]
  have he : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 1, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)) =
      positive g ([] : List (Fin 3)) * positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)) *
        (positive g ([] : List (Fin 3)))⁻¹ := by
    simp only [positive, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      inv_one, mul_one, one_mul, hcc]
  rw [he]
  have ht : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] : List (Fin 3)) = 1 := by
    have hh := List.prod_rotate_eq_one_of_prod_eq_one hn 25
    have hrot : ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2] : List (Fin 3)).rotate 25 = [0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2] := by decide
    simpa only [positive, ← List.map_rotate, hrot] using hh
  rw [ht, mul_one, mul_inv_cancel]

private theorem step4 (g : Fin 3 → E) (hi : ∀ i, (g i)⁻¹ = g i)
    (hs : positive g (testLetters 6) ^ 2 = 1)
    (hn : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] : List (Fin 3)) = 1) :
    positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2] : List (Fin 3)) = 1 := by
  have hc (i : Fin 3) : g i * g i = 1 := by simpa only [hi] using inv_mul_cancel (g i)
  have hcc (i : Fin 3) (z : E) : g i * (g i * z) = z := by rw [← mul_assoc, hc, one_mul]
  have hr := reverse_segment g hi ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2]) ([1, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0]) ([1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2]) hs
  change positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 1, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2] : List (Fin 3)) = positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2] : List (Fin 3)) at hr
  rw [hr]
  have he : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 2, 0, 1, 0, 1, 1, 0, 1, 0, 2, 0, 1, 2, 0, 1, 0, 2] : List (Fin 3)) =
      positive g ([] : List (Fin 3)) * positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2] : List (Fin 3)) *
        (positive g ([] : List (Fin 3)))⁻¹ := by
    simp only [positive, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      inv_one, mul_one, one_mul, hcc]
  rw [he]
  have ht : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2] : List (Fin 3)) = 1 := by
    have hh := List.prod_rotate_eq_one_of_prod_eq_one hn 29
    have hrot : ([0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] : List (Fin 3)).rotate 29 = [0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2] := by decide
    simpa only [positive, ← List.map_rotate, hrot] using hh
  rw [ht, mul_one, mul_inv_cancel]

private theorem step5 (g : Fin 3 → E) (hi : ∀ i, (g i)⁻¹ = g i)
    (hs : positive g (testLetters 7) ^ 2 = 1)
    (hn : positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2] : List (Fin 3)) = 1) :
    positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] : List (Fin 3)) = 1 := by
  have hc (i : Fin 3) : g i * g i = 1 := by simpa only [hi] using inv_mul_cancel (g i)
  have hcc (i : Fin 3) (z : E) : g i * (g i * z) = z := by rw [← mul_assoc, hc, one_mul]
  have hr := reverse_segment g hi ([0]) ([1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2]) ([1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2]) hs
  change positive g ([0, 1, 0, 1, 0, 1, 2, 0, 1, 2, 0, 2, 1, 0, 1, 0, 1, 0, 2, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] : List (Fin 3)) = positive g ([0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] : List (Fin 3)) at hr
  rw [hr]
  have he : positive g ([0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 1, 0, 2, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] : List (Fin 3)) =
      positive g ([] : List (Fin 3)) * positive g ([0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] : List (Fin 3)) *
        (positive g ([] : List (Fin 3)))⁻¹ := by
    simp only [positive, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      inv_one, mul_one, one_mul, hcc]
  rw [he]
  have ht : positive g ([0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] : List (Fin 3)) = 1 := by
    have hh := List.prod_rotate_eq_one_of_prod_eq_one hn 9
    have hrot : ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2] : List (Fin 3)).rotate 9 = [0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2] := by decide
    simpa only [positive, ← List.map_rotate, hrot] using hh
  rw [ht, mul_one, mul_inv_cancel]

private theorem step6 (g : Fin 3 → E) (hi : ∀ i, (g i)⁻¹ = g i)
    (hs : positive g (testLetters 8) ^ 2 = 1)
    (hn : positive g ([] : List (Fin 3)) = 1) :
    positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2] : List (Fin 3)) = 1 := by
  have hc (i : Fin 3) : g i * g i = 1 := by simpa only [hi] using inv_mul_cancel (g i)
  have hcc (i : Fin 3) (z : E) : g i * (g i * z) = z := by rw [← mul_assoc, hc, one_mul]
  have hr := reverse_segment g hi ([]) ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2]) ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2]) hs
  change positive g ([0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2] : List (Fin 3)) = positive g ([2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2] : List (Fin 3)) at hr
  rw [hr]
  have he : positive g ([2, 0, 2, 0, 2, 1, 0, 1, 0, 1, 0, 0, 1, 0, 1, 0, 1, 2, 0, 2, 0, 2] : List (Fin 3)) =
      positive g ([] : List (Fin 3)) * positive g ([] : List (Fin 3)) *
        (positive g ([] : List (Fin 3)))⁻¹ := by
    simp only [positive, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      inv_one, mul_one, hc, hcc]
  rw [he]
  have ht : positive g ([] : List (Fin 3)) = 1 := by
    have hh := List.prod_rotate_eq_one_of_prod_eq_one hn 0
    have hrot : ([] : List (Fin 3)).rotate 0 = [] := by decide
    simpa only [positive, ← List.map_rotate, hrot] using hh
  rw [ht, mul_one, mul_inv_cancel]

/-- The literal final even relation in every compatible central double cover. -/
theorem relation_eleven (f : Cover E He) (hc : Nat.card f.toMonoidHom.ker = 2)
    (h : Presentation →* E) (ht : f.toMonoidHom.comp h = presentationMap) :
    h (eval liftedGenerator (relationLetters 11)) = 1 := by
  let g := h ∘ liftedGenerator
  have hi (i : Fin 3) : (g i)⁻¹ = g i := by
    apply inv_eq_of_mul_eq_one_left
    change h (liftedGenerator i) * h (liftedGenerator i) = 1
    rw [← map_mul, ← pow_two, liftedGenerator_sq, map_one]
  rw [image_relation]
  apply step0 g hi (test_square f hc h ht 2)
  apply step1 g hi (test_square f hc h ht 3)
  apply step2 g hi (test_square f hc h ht 4)
  apply step3 g hi (test_square f hc h ht 5)
  apply step4 g hi (test_square f hc h ht 6)
  apply step5 g hi (test_square f hc h ht 7)
  apply step6 g hi (test_square f hc h ht 8)
  rfl

end Held.CentralCovers.TwoPrimary.FaithfulPresentation.M1Restriction.BinaryEven
