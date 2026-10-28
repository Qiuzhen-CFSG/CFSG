module

public import Mathlib.GroupTheory.Index
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Subgroup indices from a double-coset census

A subgroup containing `H` is a union of `H` double cosets. If a finite labeling
partitions a finite group into such cosets and each fiber has cardinality
`w i * |H|`, every relative index above `H` is a sum of selected weights.
The ambient index is the sum of all weights.

The proof counts fibers inside the overgroup and cancels the positive order
of `H` from Lagrange's formula. This is the elementary counting step in the
subdegree obstruction to imprimitivity; one application uses the subdegrees
listed in Breuer–Magaard–Wilson (2019), §5.2, https://arxiv.org/abs/1902.07758.
-/

public section

open scoped BigOperators

namespace Subgroup
variable {G ι : Type*} [Group G] [Finite G]

private lemma card_eq_sum_of_saturated_fibers (K : Subgroup G) (f : G → ι) (w : ι → ℕ)
    (hcard : ∀ i, Nat.card {x : G // f x = i} = w i)
    (hsat : ∀ x y : G, f x = f y → x ∈ K → y ∈ K) :
    ∃ s : Finset ι, f 1 ∈ s ∧ Nat.card K = ∑ i ∈ s, w i := by
  classical
  let _ := Fintype.ofFinite G
  let t : Finset G := Finset.univ.filter (· ∈ K)
  let s := t.image f
  have ht (x : G) : x ∈ t ↔ x ∈ K := by simp [t]
  have hf (i : ι) (hi : i ∈ s) : t.filter (fun x => f x = i) =
      Finset.univ.filter (fun x => f x = i) := by
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hi
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨And.right, fun hy => ⟨(ht y).mpr (hsat x y hy.symm ((ht x).mp hx)), hy⟩⟩
  refine ⟨s, Finset.mem_image.mpr ⟨1, (ht 1).mpr K.one_mem, rfl⟩, ?_⟩
  calc
    Nat.card K = t.card := Nat.subtype_card t ht
    _ = ∑ i ∈ s, (t.filter (fun x => f x = i)).card :=
      Finset.card_eq_sum_card_image f t
    _ = ∑ i ∈ s, w i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [hf i hi, ← hcard i]
      exact (Nat.subtype_card _ (by simp)).symm

/-- The relative index of an overgroup is a sum of fiber weights, including
 the weight of the fiber containing the identity. Equal labels need only imply
 membership in the same double coset. -/
theorem relIndex_eq_sum_of_doubleCoset_fibers (H K : Subgroup G) (hHK : H ≤ K)
    (f : G → ι) (w : ι → ℕ)
    (hcard : ∀ i, Nat.card {x : G // f x = i} = w i * Nat.card H)
    (hcoset : ∀ x y : G, f x = f y → ∃ a ∈ H, ∃ b ∈ H, y = a * x * b) :
    ∃ s : Finset ι, f 1 ∈ s ∧ H.relIndex K = ∑ i ∈ s, w i := by
  obtain ⟨s, hs, hc⟩ := card_eq_sum_of_saturated_fibers K f (fun i => w i * Nat.card H) hcard
    (fun x y hxy hx => by
      obtain ⟨a, ha, b, hb, rfl⟩ := hcoset x y hxy
      exact K.mul_mem (K.mul_mem (hHK ha) hx) (hHK hb))
  refine ⟨s, hs, ?_⟩
  have hh : Nat.card (H.subgroupOf K) = Nat.card H :=
    Nat.card_congr (subgroupOfEquivOfLe hHK).toEquiv
  have hm := (H.subgroupOf K).index_mul_card
  change H.relIndex K * Nat.card (H.subgroupOf K) = Nat.card K at hm
  rw [hh, hc, ← Finset.sum_mul] at hm
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hm

/-- A partition whose fibers have sizes `w i * |H|` determines the index of `H`. -/
theorem index_eq_sum_of_fiber_card [Fintype ι] (H : Subgroup G) (f : G → ι) (w : ι → ℕ)
    (hcard : ∀ i, Nat.card {x : G // f x = i} = w i * Nat.card H) :
    H.index = ∑ i, w i := by
  classical
  let _ := Fintype.ofFinite G
  have hc : Nat.card G = ∑ i, w i * Nat.card H := by
    rw [Nat.card_eq_fintype_card, Fintype.card]
    calc
      Finset.univ.card = ∑ i : ι, (Finset.univ.filter (fun x : G => f x = i)).card :=
        Finset.card_eq_sum_card_fiberwise (by simp)
      _ = ∑ i, w i * Nat.card H := by
        apply Finset.sum_congr rfl
        intro i _
        rw [← hcard i]
        exact (Nat.subtype_card _ (by simp)).symm
  have hm := H.index_mul_card
  rw [hc, ← Finset.sum_mul] at hm
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hm
end Subgroup
