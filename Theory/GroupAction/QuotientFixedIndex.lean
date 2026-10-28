module
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.Index

/-!
# Fixed-point indices under equivariant quotient maps

For actions by automorphisms on finite groups, a surjective equivariant
group homomorphism cannot increase the index of the fixed subgroup. The
associated bound on the ratio of group order to fixed-subgroup order
therefore also descends to the quotient. No coprimality or commutativity
hypothesis is needed.

The homomorphism sends fixed elements to fixed elements. Its fixed-subgroup
image has index dividing the original index, and enlarging this image to
the quotient's full fixed subgroup decreases the index. Multiplying by
the fixed-subgroup order gives the cardinal-bound corollary.

This is the elementary fixed-index transfer used on `U/Z` before the
application of (1.3) in Stellmacher (9.1), Journal of Algebra 190 (1997),
p.47; all graph and residual hypotheses belong to that application.
-/

public theorem fixedPoints_index_le_of_surjective_equivariant
    {A V W : Type*} [Group A] [Group V] [Group W] [Finite V] [Finite W]
    [MulDistribMulAction A V] [MulDistribMulAction A W]
    (f : V →* W) (hf : Function.Surjective f)
    (heq : ∀ (a : A) (v : V), f (a • v) = a • f v) :
    (FixedPoints.subgroup A W).index ≤ (FixedPoints.subgroup A V).index := by
  have hmap : (FixedPoints.subgroup A V).map f ≤ FixedPoints.subgroup A W := by
    rintro w ⟨v, hv, rfl⟩ a
    rw [← heq, hv a]
  exact (Subgroup.index_antitone hmap).trans
    (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := FixedPoints.subgroup A V)))
      ((FixedPoints.subgroup A V).index_map_dvd hf))

public theorem fixedPoints_card_bound_of_surjective_equivariant
    {A V W : Type*} [Group A] [Group V] [Group W] [Finite V] [Finite W]
    [MulDistribMulAction A V] [MulDistribMulAction A W]
    (f : V →* W) (hf : Function.Surjective f)
    (heq : ∀ (a : A) (v : V), f (a • v) = a • f v)
    (k : ℕ) (hbound : Nat.card V ≤ k * Nat.card (FixedPoints.subgroup A V)) :
    Nat.card W ≤ k * Nat.card (FixedPoints.subgroup A W) := by
  have hV : (FixedPoints.subgroup A V).index ≤ k := by
    rw [← (FixedPoints.subgroup A V).card_mul_index, mul_comm k] at hbound
    exact Nat.le_of_mul_le_mul_left hbound Nat.card_pos
  have hW := (fixedPoints_index_le_of_surjective_equivariant f hf heq).trans hV
  rw [← (FixedPoints.subgroup A W).card_mul_index, mul_comm k]
  exact Nat.mul_le_mul_left _ hW
